module J2ME {
  declare var util, config;
  declare var Promise;

  import BytecodeStream = Bytecode.BytecodeStream;
  import BlockMap = Bytecode.BlockMap;
  import checkArrayBounds = J2ME.checkArrayBounds;
  import checkDivideByZero = J2ME.checkDivideByZero;
  import checkDivideByZeroLong = J2ME.checkDivideByZeroLong;

  import Bytecodes = Bytecode.Bytecodes;
  import assert = Debug.assert;

  export var interpreterCounter = null; // new Metrics.Counter(true);
  export var interpreterMethodCounter = new Metrics.Counter(true);

  var traceArrayAccess = false;

  function traceArrayStore(index: number, array: any [], value: any) {
    traceWriter.writeLn(toDebugString(array) + "[" + index + "] = " + toDebugString(value));
  }

  function traceArrayLoad(index: number, array: any []) {
    assert(array[index] !== undefined, "Bad array value in traceArrayLoad");
    traceWriter.writeLn(toDebugString(array) + "[" + index + "] (" + toDebugString(array[index]) + ")");
  }

  function resolveClass(index: number, classInfo: ClassInfo): ClassInfo {
    var classInfo = classInfo.constantPool.resolveClass(index);
    linkKlass(classInfo);
    return classInfo;
  }

  /**
   * The number of opcodes executed thus far.
   */
  export var bytecodeCount = 0;

  /**
   * The number of times the interpreter method was called thus far.
   */
  export var interpreterCount = 0;

  export var onStackReplacementCount = 0;

  function buildExceptionLog(ex, stackTrace) {
    var classInfo: ClassInfo = ex.klass.classInfo;
    var className = classInfo.getClassNameSlow();
    var detailMessage = J2ME.fromJavaString(classInfo.getFieldByName(toUTF8("detailMessage"), toUTF8("Ljava/lang/String;"), false).get(ex));
    return className + ": " + (detailMessage || "") + "\n" + stackTrace.map(function(entry) {
      return " - " + entry.className + "." + entry.methodName + entry.methodSignature + ", pc=" + entry.offset;
    }).join("\n") + "\n\n";
  }

  function tryCatch(e) {
    var ctx = $.ctx;
    var frame = ctx.current();

    var exClass = e.class;
    if (!e.stackTrace) {
      e.stackTrace = [];
    }

    var stackTrace = e.stackTrace;

    while (frame) {
      var stack = frame.stack;
      var handler_pc = null;

      for (var i = 0; i < frame.methodInfo.exception_table_length; i++) {
        var exceptionEntryView = frame.methodInfo.getExceptionEntryViewByIndex(i);
        if (frame.opPC >= exceptionEntryView.start_pc && frame.opPC < exceptionEntryView.end_pc) {
          if (exceptionEntryView.catch_type === 0) {
            handler_pc = exceptionEntryView.handler_pc;
            break;
          } else {
            var ci = resolveClass(exceptionEntryView.catch_type, frame.methodInfo.classInfo);
            if (isAssignableTo(e.klass, ci.klass)) {
              handler_pc = exceptionEntryView.handler_pc;
              break;
            }
          }
        }
      }

      if (handler_pc != null) {
        stack.length = 0;
        stack.push(e);
        frame.pc = handler_pc;

        if (VM.DEBUG_PRINT_ALL_EXCEPTIONS) {
          console.error(buildExceptionLog(e, stackTrace));
        }

        return;
      }
      frame.free();
      ctx.popFrame();
      frame = ctx.current();
    }

    ctx.stop();
      ctx.kill();
      if (ctx.thread && ctx.thread._lock && ctx.thread._lock.waiting.length > 0) {
        console.error(buildExceptionLog(e, stackTrace));
        for (var i = 0; i < ctx.thread._lock.waiting.length; i++) {
          var waitingCtx = ctx.thread._lock.waiting[i];
          ctx.thread._lock.waiting[i] = null;
          waitingCtx.wakeup(ctx.thread);
        }
      }
      throw new Error(buildExceptionLog(e, stackTrace));
  }

  export function interpret() {
    interpreterCount ++;

    // TODO: Find the right place for this now
        // TODO: Make sure this works even if we JIT everything. At the moment it fails
        // for synthetic method frames which have bad max_local counts.
        // Inline heuristics that trigger JIT compilation here.
        //        if ((enableRuntimeCompilation &&
        //             mi.state < MethodState.Compiled && // Give up if we're at this state.
        //             mi.stats.backwardsBranchCount + mi.stats.interpreterCallCount > 10) ||
        //            config.forceRuntimeCompilation) {
        //          compileAndLinkMethod(mi);
        //        }

    var ctx = $.ctx;
    var frame = ctx.current();
    if (!frame) {
      ctx.stop();
      return;
    }
    if (ctx.U) {
      return;
    }
    var stack = frame.stack;
    var op: Bytecodes;
    var a: any, b: any, c: any, d: any;
    var fi: FieldInfo;
    var ci: ClassInfo;

    // TODO: It's harder to account for this now. Do we care?
    // mi.stats.interpreterCallCount ++;

    // NB: This loop is the heart of our JVM. It is run very frequently
    // and it MUST BE VERY FAST. Any logic that is placed in this loop is
    // likely to affect performance.
    do {
        frame.opPC = frame.pc;
        op = frame.read8();

        //console.log(frame.methodInfo.implKey + (frame.methodInfo.isNative ? " (native)" : "") + ". pc=" + frame.pc + ". op=" + op + ". stack length=" + stack.length);

        bytecodeCount ++;
        frame.methodInfo.stats.bytecodeCount ++;
        switch (op) {
          case Bytecodes.NOP:
            break;
          case Bytecodes.ACONST_NULL:
            stack.push(null);
            break;
          case Bytecodes.ICONST_M1:
          case Bytecodes.ICONST_0:
          case Bytecodes.ICONST_1:
          case Bytecodes.ICONST_2:
          case Bytecodes.ICONST_3:
          case Bytecodes.ICONST_4:
          case Bytecodes.ICONST_5:
            stack.push(op - Bytecodes.ICONST_0);
            break;
          case Bytecodes.FCONST_0:
          case Bytecodes.FCONST_1:
          case Bytecodes.FCONST_2:
            stack.push(op - Bytecodes.FCONST_0);
            break;
          case Bytecodes.DCONST_0:
          case Bytecodes.DCONST_1:
            stack.push2(op - Bytecodes.DCONST_0);
            break;
          case Bytecodes.LCONST_0:
          case Bytecodes.LCONST_1:
            stack.push2(Long.fromInt(op - Bytecodes.LCONST_0));
            break;
          case Bytecodes.BIPUSH:
            stack.push(frame.read8Signed());
            break;
          case Bytecodes.SIPUSH:
            stack.push(frame.read16Signed());
            break;
          case Bytecodes.LDC:
            stack.push(frame.methodInfo.classInfo.constantPool.resolve(frame.read8(), TAGS.CONSTANT_Any, false));
            break;
          case Bytecodes.LDC_W:
            stack.push(frame.methodInfo.classInfo.constantPool.resolve(frame.read16(), TAGS.CONSTANT_Any, false));
            break;
          case Bytecodes.LDC2_W:
            stack.push2(frame.methodInfo.classInfo.constantPool.resolve(frame.read16(), TAGS.CONSTANT_Any, false));
            break;
          case Bytecodes.ILOAD:
            stack.push(frame.local[frame.read8()]);
            break;
          case Bytecodes.FLOAD:
            stack.push(frame.local[frame.read8()]);
            break;
          case Bytecodes.ALOAD:
            stack.push(frame.local[frame.read8()]);
            break;
          case Bytecodes.ALOAD_ILOAD:
            stack.push(frame.local[frame.read8()]);
            frame.pc ++;
            stack.push(frame.local[frame.read8()]);
            break;
          case Bytecodes.LLOAD:
          case Bytecodes.DLOAD:
            stack.push2(frame.local[frame.read8()]);
            break;
          case Bytecodes.ILOAD_0:
          case Bytecodes.ILOAD_1:
          case Bytecodes.ILOAD_2:
          case Bytecodes.ILOAD_3:
            stack.push(frame.local[op - Bytecodes.ILOAD_0]);
            break;
          case Bytecodes.FLOAD_0:
          case Bytecodes.FLOAD_1:
          case Bytecodes.FLOAD_2:
          case Bytecodes.FLOAD_3:
            stack.push(frame.local[op - Bytecodes.FLOAD_0]);
            break;
          case Bytecodes.ALOAD_0:
          case Bytecodes.ALOAD_1:
          case Bytecodes.ALOAD_2:
          case Bytecodes.ALOAD_3:
            stack.push(frame.local[op - Bytecodes.ALOAD_0]);
            break;
          case Bytecodes.LLOAD_0:
          case Bytecodes.LLOAD_1:
          case Bytecodes.LLOAD_2:
          case Bytecodes.LLOAD_3:
            stack.push2(frame.local[op - Bytecodes.LLOAD_0]);
            break;
          case Bytecodes.DLOAD_0:
          case Bytecodes.DLOAD_1:
          case Bytecodes.DLOAD_2:
          case Bytecodes.DLOAD_3:
            stack.push2(frame.local[op - Bytecodes.DLOAD_0]);
            break;
          case Bytecodes.IALOAD:
          case Bytecodes.FALOAD:
          case Bytecodes.AALOAD:
          case Bytecodes.BALOAD:
          case Bytecodes.CALOAD:
          case Bytecodes.SALOAD:
            a = stack.pop();
            c = stack.pop();
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            if (!checkArrayBounds(c, a)) {
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            stack.push(c[a]);
            break;
          case Bytecodes.LALOAD:
          case Bytecodes.DALOAD:
            a = stack.pop();
            c = stack.pop();
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            if (!checkArrayBounds(c, a)) {
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            stack.push2(c[a]);
            break;
          case Bytecodes.ISTORE:
          case Bytecodes.FSTORE:
          case Bytecodes.ASTORE:
            frame.local[frame.read8()] = stack.pop();
            break;
          case Bytecodes.LSTORE:
          case Bytecodes.DSTORE:
            frame.local[frame.read8()] = stack.pop2();
            break;
          case Bytecodes.ISTORE_0:
          case Bytecodes.FSTORE_0:
          case Bytecodes.ASTORE_0:
            frame.local[0] = stack.pop();
            break;
          case Bytecodes.ISTORE_1:
          case Bytecodes.FSTORE_1:
          case Bytecodes.ASTORE_1:
            frame.local[1] = stack.pop();
            break;
          case Bytecodes.ISTORE_2:
          case Bytecodes.FSTORE_2:
          case Bytecodes.ASTORE_2:
            frame.local[2] = stack.pop();
            break;
          case Bytecodes.ISTORE_3:
          case Bytecodes.FSTORE_3:
          case Bytecodes.ASTORE_3:
            frame.local[3] = stack.pop();
            break;
          case Bytecodes.LSTORE_0:
          case Bytecodes.DSTORE_0:
            frame.local[0] = stack.pop2();
            break;
          case Bytecodes.LSTORE_1:
          case Bytecodes.DSTORE_1:
            frame.local[1] = stack.pop2();
            break;
          case Bytecodes.LSTORE_2:
          case Bytecodes.DSTORE_2:
            frame.local[2] = stack.pop2();
            break;
          case Bytecodes.LSTORE_3:
          case Bytecodes.DSTORE_3:
            frame.local[3] = stack.pop2();
            break;
          case Bytecodes.IASTORE:
          case Bytecodes.FASTORE:
          case Bytecodes.BASTORE:
          case Bytecodes.CASTORE:
          case Bytecodes.SASTORE:
            b = stack.pop();
            a = stack.pop();
            c = stack.pop();
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            if (!checkArrayBounds(c, a)) {
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            c[a] = b;
            break;
          case Bytecodes.LASTORE:
          case Bytecodes.DASTORE:
            b = stack.pop2();
            a = stack.pop();
            c = stack.pop();
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            if (!checkArrayBounds(c, a)) {
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            c[a] = b;
            break;
          case Bytecodes.AASTORE:
            b = stack.pop();
            a = stack.pop();
            c = stack.pop();
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            if (!checkArrayBounds(c, a)) {
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            if (!checkArrayStore(c, b)) {
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            c[a] = b;
            break;
          case Bytecodes.POP:
            stack.pop();
            break;
          case Bytecodes.POP2:
            stack.pop2();
            break;
          case Bytecodes.DUP:
            stack.push(stack[stack.length - 1]);
            break;
          case Bytecodes.DUP_X1:
            a = stack.pop();
            b = stack.pop();
            stack.push(a);
            stack.push(b);
            stack.push(a);
            break;
          case Bytecodes.DUP_X2:
            a = stack.pop();
            b = stack.pop();
            c = stack.pop();
            stack.push(a);
            stack.push(c);
            stack.push(b);
            stack.push(a);
            break;
          case Bytecodes.DUP2:
            a = stack.pop();
            b = stack.pop();
            stack.push(b);
            stack.push(a);
            stack.push(b);
            stack.push(a);
            break;
          case Bytecodes.DUP2_X1:
            a = stack.pop();
            b = stack.pop();
            c = stack.pop();
            stack.push(b);
            stack.push(a);
            stack.push(c);
            stack.push(b);
            stack.push(a);
            break;
          case Bytecodes.DUP2_X2:
            a = stack.pop();
            b = stack.pop();
            c = stack.pop();
            d = stack.pop();
            stack.push(b);
            stack.push(a);
            stack.push(d);
            stack.push(c);
            stack.push(b);
            stack.push(a);
            break;
          case Bytecodes.SWAP:
            a = stack.pop();
            b = stack.pop();
            stack.push(a);
            stack.push(b);
            break;
          case Bytecodes.IINC:
            a = frame.read8();
            b = frame.read8Signed();
            frame.local[a] += b | 0;
            break;
          case Bytecodes.IINC_GOTO:
            a = frame.read8();
            b = frame.read8Signed();
            frame.local[a] += frame.local[a];
            frame.pc ++;
            frame.pc = frame.readTargetPC();
            break;
          case Bytecodes.IADD:
            stack.push((stack.pop() + stack.pop()) | 0);
            break;
          case Bytecodes.LADD:
            stack.push2(stack.pop2().add(stack.pop2()));
            break;
          case Bytecodes.FADD:
            stack.push(Math.fround(stack.pop() + stack.pop()));
            break;
          case Bytecodes.DADD:
            stack.push2(stack.pop2() + stack.pop2());
            break;
          case Bytecodes.ISUB:
            stack.push((-stack.pop() + stack.pop()) | 0);
            break;
          case Bytecodes.LSUB:
            stack.push2(stack.pop2().negate().add(stack.pop2()));
            break;
          case Bytecodes.FSUB:
            stack.push(Math.fround(-stack.pop() + stack.pop()));
            break;
          case Bytecodes.DSUB:
            stack.push2(-stack.pop2() + stack.pop2());
            break;
          case Bytecodes.IMUL:
            stack.push(Math.imul(stack.pop(), stack.pop()));
            break;
          case Bytecodes.LMUL:
            stack.push2(stack.pop2().multiply(stack.pop2()));
            break;
          case Bytecodes.FMUL:
            stack.push(Math.fround(stack.pop() * stack.pop()));
            break;
          case Bytecodes.DMUL:
            stack.push2(stack.pop2() * stack.pop2());
            break;
          case Bytecodes.IDIV:
            b = stack.pop();
            a = stack.pop();
            if (!checkDivideByZero(b)) {
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            stack.push((a === Constants.INT_MIN && b === -1) ? a : ((a / b) | 0));
            break;
          case Bytecodes.LDIV:
            b = stack.pop2();
            a = stack.pop2();
            if (!checkDivideByZeroLong(b)) {
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            stack.push2(a.div(b));
            break;
          case Bytecodes.FDIV:
            b = stack.pop();
            a = stack.pop();
            stack.push(Math.fround(a / b));
            break;
          case Bytecodes.DDIV:
            b = stack.pop2();
            a = stack.pop2();
            stack.push2(a / b);
            break;
          case Bytecodes.IREM:
            b = stack.pop();
            a = stack.pop();
            if (!checkDivideByZero(b)) {
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            stack.push(a % b);
            break;
          case Bytecodes.LREM:
            b = stack.pop2();
            a = stack.pop2();
            if (!checkDivideByZeroLong(b)) {
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            stack.push2(a.modulo(b));
            break;
          case Bytecodes.FREM:
            b = stack.pop();
            a = stack.pop();
            stack.push(Math.fround(a % b));
            break;
          case Bytecodes.DREM:
            b = stack.pop2();
            a = stack.pop2();
            stack.push2(a % b);
            break;
          case Bytecodes.INEG:
            stack.push((-stack.pop()) | 0);
            break;
          case Bytecodes.LNEG:
            stack.push2(stack.pop2().negate());
            break;
          case Bytecodes.FNEG:
            stack.push(-stack.pop());
            break;
          case Bytecodes.DNEG:
            stack.push2(-stack.pop2());
            break;
          case Bytecodes.ISHL:
            b = stack.pop();
            a = stack.pop();
            stack.push(a << b);
            break;
          case Bytecodes.LSHL:
            b = stack.pop();
            a = stack.pop2();
            stack.push2(a.shiftLeft(b));
            break;
          case Bytecodes.ISHR:
            b = stack.pop();
            a = stack.pop();
            stack.push(a >> b);
            break;
          case Bytecodes.LSHR:
            b = stack.pop();
            a = stack.pop2();
            stack.push2(a.shiftRight(b));
            break;
          case Bytecodes.IUSHR:
            b = stack.pop();
            a = stack.pop();
            stack.push(a >>> b);
            break;
          case Bytecodes.LUSHR:
            b = stack.pop();
            a = stack.pop2();
            stack.push2(a.shiftRightUnsigned(b));
            break;
          case Bytecodes.IAND:
            stack.push(stack.pop() & stack.pop());
            break;
          case Bytecodes.LAND:
            stack.push2(stack.pop2().and(stack.pop2()));
            break;
          case Bytecodes.IOR:
            stack.push(stack.pop() | stack.pop());
            break;
          case Bytecodes.LOR:
            stack.push2(stack.pop2().or(stack.pop2()));
            break;
          case Bytecodes.IXOR:
            stack.push(stack.pop() ^ stack.pop());
            break;
          case Bytecodes.LXOR:
            stack.push2(stack.pop2().xor(stack.pop2()));
            break;
          case Bytecodes.LCMP:
            b = stack.pop2();
            a = stack.pop2();
            if (a.greaterThan(b)) {
              stack.push(1);
            } else if (a.lessThan(b)) {
              stack.push(-1);
            } else {
              stack.push(0);
            }
            break;
          case Bytecodes.FCMPL:
            b = stack.pop();
            a = stack.pop();
            if (isNaN(a) || isNaN(b) || a < b) {
              stack.push(-1);
            } else if (a > b) {
              stack.push(1);
            } else {
              stack.push(0);
            }
            break;
          case Bytecodes.FCMPG:
            b = stack.pop();
            a = stack.pop();
            if (isNaN(a) || isNaN(b) || a > b) {
              stack.push(1);
            } else if (a < b) {
              stack.push(-1);
            } else {
              stack.push(0);
            }
            break;
          case Bytecodes.DCMPL:
            b = stack.pop2();
            a = stack.pop2();
            if (isNaN(a) || isNaN(b) || a < b) {
              stack.push(-1);
            } else if (a > b) {
              stack.push(1);
            } else {
              stack.push(0);
            }
            break;
          case Bytecodes.DCMPG:
            b = stack.pop2();
            a = stack.pop2();
            if (isNaN(a) || isNaN(b) || a > b) {
              stack.push(1);
            } else if (a < b) {
              stack.push(-1);
            } else {
              stack.push(0);
            }
            break;
          case Bytecodes.IFEQ:
            a = frame.readTargetPC();
            if (stack.pop() === 0) {
              frame.pc = a;
            }
            break;
          case Bytecodes.IFNE:
            a = frame.readTargetPC();
            if (stack.pop() !== 0) {
              frame.pc = a;
            }
            break;
          case Bytecodes.IFLT:
            a = frame.readTargetPC();
            if (stack.pop() < 0) {
              frame.pc = a;
            }
            break;
          case Bytecodes.IFGE:
            a = frame.readTargetPC();
            if (stack.pop() >= 0) {
              frame.pc = a;
            }
            break;
          case Bytecodes.IFGT:
            a = frame.readTargetPC();
            if (stack.pop() > 0) {
              frame.pc = a;
            }
            break;
          case Bytecodes.IFLE:
            a = frame.readTargetPC();
            if (stack.pop() <= 0) {
              frame.pc = a;
            }
            break;
          case Bytecodes.IF_ICMPEQ:
            a = frame.readTargetPC();
            if (stack.pop() === stack.pop()) {
              frame.pc = a;
            }
            break;
          case Bytecodes.IF_ICMPNE:
            a = frame.readTargetPC();
            if (stack.pop() !== stack.pop()) {
              frame.pc = a;
            }
            break;
          case Bytecodes.IF_ICMPLT:
            a = frame.readTargetPC();
            if (stack.pop() > stack.pop()) {
              frame.pc = a;
            }
            break;
          case Bytecodes.IF_ICMPGE:
            a = frame.readTargetPC();
            if (stack.pop() <= stack.pop()) {
              frame.pc = a;
            }
            break;
          case Bytecodes.IF_ICMPGT:
            a = frame.readTargetPC();
            if (stack.pop() < stack.pop()) {
              frame.pc = a;
            }
            break;
          case Bytecodes.IF_ICMPLE:
            a = frame.readTargetPC();
            if (stack.pop() >= stack.pop()) {
              frame.pc = a;
            }
            break;
          case Bytecodes.IF_ACMPEQ:
            a = frame.readTargetPC();
            if (stack.pop() === stack.pop()) {
              frame.pc = a;
            }
            break;
          case Bytecodes.IF_ACMPNE:
            a = frame.readTargetPC();
            if (stack.pop() !== stack.pop()) {
              frame.pc = a;
            }
            break;
          case Bytecodes.IFNULL:
            a = frame.readTargetPC();
            if (!stack.pop()) {
              frame.pc = a;
            }
            break;
          case Bytecodes.IFNONNULL:
            a = frame.readTargetPC();
            if (stack.pop()) {
              frame.pc = a;
            }
            break;
          case Bytecodes.GOTO:
            frame.pc = frame.readTargetPC();
            break;
          case Bytecodes.GOTO_W:
            frame.pc = frame.read32Signed() - 1;
            break;
          case Bytecodes.JSR:
            a = frame.read16();
            stack.push(frame.pc);
            frame.pc = a;
            break;
          case Bytecodes.JSR_W:
            a = frame.read32();
            stack.push(frame.pc);
            frame.pc = a;
            break;
          case Bytecodes.RET:
            frame.pc = frame.local[frame.read8()];
            break;
          case Bytecodes.I2L:
            stack.push2(Long.fromInt(stack.pop()));
            break;
          case Bytecodes.I2F:
            break;
          case Bytecodes.I2D:
            stack.push2(stack.pop());
            break;
          case Bytecodes.L2I:
            stack.push(stack.pop2().toInt());
            break;
          case Bytecodes.L2F:
            stack.push(Math.fround(stack.pop2().toNumber()));
            break;
          case Bytecodes.L2D:
            stack.push2(stack.pop2().toNumber());
            break;
          case Bytecodes.F2I:
            stack.push(util.double2int(stack.pop()));
            break;
          case Bytecodes.F2L:
            stack.push2(Long.fromNumber(stack.pop()));
            break;
          case Bytecodes.F2D:
            stack.push2(stack.pop());
            break;
          case Bytecodes.D2I:
            stack.push(util.double2int(stack.pop2()));
            break;
          case Bytecodes.D2L:
            stack.push2(util.double2long(stack.pop2()));
            break;
          case Bytecodes.D2F:
            stack.push(Math.fround(stack.pop2()));
            break;
          case Bytecodes.I2B:
            stack.push((stack.pop() << 24) >> 24);
            break;
          case Bytecodes.I2C:
            stack.push(stack.pop() & 0xffff);
            break;
          case Bytecodes.I2S:
            stack.push((stack.pop() << 16) >> 16);
            break;
          case Bytecodes.TABLESWITCH:
            frame.pc = frame.tableSwitch();
            break;
          case Bytecodes.LOOKUPSWITCH:
            frame.pc = frame.lookupSwitch();
            break;
          case Bytecodes.NEWARRAY:
            a = frame.read8();
            b = stack.pop();
            if (b < 0) {
              ctx.pushExceptionThrow(NegativeArraySizeExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            stack.push(newArray(PrimitiveClassInfo["????ZCFDBSIJ"[a]].klass, b));
            break;
          case Bytecodes.ANEWARRAY:
            a = frame.read16();
            ci = resolveClass(a, frame.methodInfo.classInfo);
            b = stack.pop();
            if (b < 0) {
              ctx.pushExceptionThrow(NegativeArraySizeExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            stack.push(newArray(ci.klass, b));
            break;
          case Bytecodes.MULTIANEWARRAY:
            a = frame.read16();
            ci = resolveClass(a, frame.methodInfo.classInfo);
            d = frame.read8();
            if (d < 0) {
              ctx.pushExceptionThrow(NegativeArraySizeExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            b = new Array(d);
            c = b.length;
            for (; c > 0; c--) {
              b[c-1] = stack.pop();
              if (b[c-1] < 0) {
                ctx.pushExceptionThrow(NegativeArraySizeExceptionStr);
                frame = ctx.current();
                stack = frame.stack;
                break;
              }
            }
            if (c !== 0) {
              continue;
            }
            stack.push(J2ME.newMultiArray(ci.klass, b));
            break;
          case Bytecodes.ARRAYLENGTH:
            c = stack.pop();
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            stack.push(c.length);
            break;
          case Bytecodes.ARRAYLENGTH_IF_ICMPGE:
            c = stack.pop();
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            stack.push(c.length);
            frame.pc ++;
            a = frame.readTargetPC();
            if (stack.pop() <= stack.pop()) {
              frame.pc = a;
            }
            break;
          case Bytecodes.GETFIELD:
            a = frame.read16();
            fi = frame.methodInfo.classInfo.constantPool.resolveField(a, false);
            if (!fi) {
              ctx.pushExceptionThrow(RuntimeExceptionStr, "Field not found on class " + frame.methodInfo.classInfo.getClassNameSlow() + " at index " + a);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            c = stack.pop();
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            stack.pushKind(fi.kind, fi.get(c));
            frame.patch(3, Bytecodes.GETFIELD, Bytecodes.RESOLVED_GETFIELD);
            break;
          case Bytecodes.RESOLVED_GETFIELD:
            fi = <FieldInfo><any>frame.methodInfo.classInfo.constantPool.resolved[frame.read16()];
            c = stack.pop();
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            stack.pushKind(fi.kind, fi.get(c));
            break;
          case Bytecodes.PUTFIELD:
            a = frame.read16();
            fi = frame.methodInfo.classInfo.constantPool.resolveField(a, false);
            if (!fi) {
              ctx.pushExceptionThrow(RuntimeExceptionStr, "Field not found on class " + frame.methodInfo.classInfo.getClassNameSlow() + " at index " + a);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            b = stack.popKind(fi.kind);
            c = stack.pop();
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            fi.set(c, b);
            frame.patch(3, Bytecodes.PUTFIELD, Bytecodes.RESOLVED_PUTFIELD);
            break;
          case Bytecodes.RESOLVED_PUTFIELD:
            fi = <FieldInfo><any>frame.methodInfo.classInfo.constantPool.resolved[frame.read16()];
            b = stack.popKind(fi.kind);
            c = stack.pop();
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            fi.set(c, b);
            break;
          case Bytecodes.GETSTATIC:
            a = frame.read16();
            fi = frame.methodInfo.classInfo.constantPool.resolveField(a, true);
            if (!fi) {
              ctx.pushExceptionThrow(RuntimeExceptionStr, "Field not found on class " + frame.methodInfo.classInfo.getClassNameSlow() + " at index " + a);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            if (!ctx.runtime.maybePushClassInit(fi.classInfo)) {
              frame.pc = frame.opPC;
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            b = fi.getStatic();
            stack.pushKind(fi.kind, b);
            break;
          case Bytecodes.PUTSTATIC:
            a = frame.read16();
            fi = frame.methodInfo.classInfo.constantPool.resolveField(a, true);
            if (!fi) {
              ctx.pushExceptionThrow(RuntimeExceptionStr, "Field not found on class " + frame.methodInfo.classInfo.getClassNameSlow() + " at index " + a);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            if (!ctx.runtime.maybePushClassInit(fi.classInfo)) {
              frame.pc = frame.opPC;
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            fi.setStatic(stack.popKind(fi.kind));
            break;
          case Bytecodes.NEW:
            a = frame.read16();
            ci = resolveClass(a, frame.methodInfo.classInfo);
            if (!ctx.runtime.maybePushClassInit(ci)) {
              frame.pc = frame.opPC;
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            stack.push(newObject(ci.klass));
            break;
          case Bytecodes.CHECKCAST:
            a = frame.read16();
            ci = resolveClass(a, frame.methodInfo.classInfo);
            c = stack[stack.length - 1];
            if (c && !isAssignableTo(c.klass, ci.klass)) {
              ctx.pushExceptionThrow(ClassCastExceptionStr,
                  c.klass.classInfo.getClassNameSlow() + " is not assignable to " +
                  ci.getClassNameSlow());
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            break;
          case Bytecodes.INSTANCEOF:
            a = frame.read16();
            ci = resolveClass(a, frame.methodInfo.classInfo);
            c = stack.pop();
            stack.push(c && isAssignableTo(c.klass, ci.klass) ? 1 : 0);
            break;
          case Bytecodes.ATHROW:
            c = stack.pop();
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            tryCatch(c);
            if (VMState.Running !== ctx.U) {
              return;
            }
            frame = ctx.current();
            stack = frame.stack;
            continue;
          case Bytecodes.MONITORENTER:
            c = stack.pop();
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            ctx.monitorEnter(c);
            if (VMState.Running !== ctx.U) {
              return;
            }
            break;
          case Bytecodes.MONITOREXIT:
            c = stack.pop();
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            if (!ctx.monitorExit(c)) {
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            break;
          case Bytecodes.WIDE:
            frame.wide();
            break;

          case Bytecodes.INVOKEJS:
            frame.local[0].apply(frame.local[1], frame.local[2]);
            if (ctx.U) {
              return;
            }
            // NB: The function we called may have added frames or set
            // ctx.U. We currently don't expect it to have removed frames.
            // If that changes in the future, we'll need to check for
            // frame being null.
            frame = ctx.current();
            stack = frame.stack;
            continue;

          case Bytecodes.RESOLVED_INVOKEVIRTUAL:
            a = frame.read16();
            b = <MethodInfo><any>frame.methodInfo.classInfo.constantPool.resolved[a];

            c = frame.peekInvokeObject(b);
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            b = c.klass.classInfo.vTable[b.vTableIndex];

            frame = Frame.create(b, []);
            if (b.isNative || b.state === MethodState.Compiled) {
              frame.local.push(c[b.virtualName]);
              frame.local.push(c);
              d = [];
              ArrayUtilities.popArgsInto(stack, b, d);
              frame.local.push(d);
            } else {
              ArrayUtilities.popArgSlotsInto(stack, b, frame.local);
            }
            stack = frame.stack;
            ctx.pushFrame(frame);
            if (b.isSynchronized) {
              if (!frame.lockObject) {
                frame.lockObject = c;
              }
              ctx.monitorEnter(frame.lockObject);
              if (ctx.U) {
                return;
              }
            }
            continue;

          case Bytecodes.INVOKEVIRTUAL:
            a = frame.read16();
            b = frame.methodInfo.classInfo.constantPool.resolveMethod(a, false);
            if (!b) {
              ctx.pushExceptionThrow(RuntimeExceptionStr, "Method not found on class " + frame.methodInfo.classInfo.getClassNameSlow() + " at index " + a);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }

            c = frame.peekInvokeObject(b);
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            // TODO: Remove this
            var oldB = b;
            b = c.klass.classInfo.vTable[b.vTableIndex];
            if (!b) {
              console.log("FAILURE");
              console.log(oldB.implKey);
              console.log(c.klass.classInfo.getClassNameSlow());
            }
            frame.patch(3, Bytecodes.INVOKEVIRTUAL, Bytecodes.RESOLVED_INVOKEVIRTUAL);

            frame = Frame.create(b, []);
            if (b.isNative) {
              frame.local.push(c[b.virtualName]);
              frame.local.push(c);
              d = [];
              ArrayUtilities.popArgsInto(stack, b, d);
              frame.local.push(d);
            } else {
              ArrayUtilities.popArgSlotsInto(stack, b, frame.local);
            }
            stack = frame.stack;
            ctx.pushFrame(frame);
            if (b.isSynchronized) {
              if (!frame.lockObject) {
                frame.lockObject = c;
              }
              ctx.monitorEnter(frame.lockObject);
              if (ctx.U) {
                return;
              }
            }
            continue;

          case Bytecodes.INVOKESPECIAL:
            a = frame.read16();
            b = frame.methodInfo.classInfo.constantPool.resolveMethod(a, false);
            if (!b) {
              ctx.pushExceptionThrow(RuntimeExceptionStr, "Method not found on class " + frame.methodInfo.classInfo.getClassNameSlow() + " at index " + a);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }

            c = frame.peekInvokeObject(b);
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }

            frame = Frame.create(b, []);
            if (b.isNative) {
              frame.local.push(getLinkedMethod(b));
              frame.local.push(c);
              d = [];
              ArrayUtilities.popArgsInto(stack, b, d);
              frame.local.push(d);
            } else if (b.state === MethodState.Compiled) {
              // TODO
            } else {
              ArrayUtilities.popArgSlotsInto(stack, b, frame.local);
            }
            stack = frame.stack;
            ctx.pushFrame(frame);
            if (b.isSynchronized) {
              if (!frame.lockObject) {
                frame.lockObject = c;
              }
              ctx.monitorEnter(frame.lockObject);
              if (ctx.U) {
                return;
              }
            }
            continue;

          case Bytecodes.INVOKESTATIC:
          //console.log("INVOKESTATIC");
            a = frame.read16();
            b = frame.methodInfo.classInfo.constantPool.resolveMethod(a, true);
            if (!b) {
              ctx.pushExceptionThrow(RuntimeExceptionStr, "Method not found on class " + frame.methodInfo.classInfo.getClassNameSlow() + " at index " + a);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }

            if (!ctx.runtime.maybePushClassInit(b.classInfo)) {
              frame.pc = frame.opPC;
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            frame = Frame.create(b, []);
            if (b.isNative) {
            //console.log("\tnative!");
              frame.local.push(getLinkedMethod(b));
              frame.local.push(null);
              d = [];
              ArrayUtilities.popArgsInto(stack, b, d);
              frame.local.push(d);
            } else if (b.state === MethodState.Compiled) {
              // TODO
            } else {
            //console.log("\tpopping args: " + stack.length);
              ArrayUtilities.popArgSlotsInto(stack, b, frame.local);
              //console.log("\tpopped args: " + stack.length);
            }
            stack = frame.stack;

            ctx.pushFrame(frame);
            if (b.isSynchronized) {
              if (!frame.lockObject) {
                frame.lockObject = b.classInfo.getClassObject();
              }
              ctx.monitorEnter(frame.lockObject);
              if (VMState.Running !== ctx.U) {
                return;
              }
            }
            continue;

          case Bytecodes.INVOKEINTERFACE:
            a = frame.read16();
            frame.read16(); // Args Number & Zero
            b = frame.methodInfo.classInfo.constantPool.resolveMethod(a, false);
            if (!b) {
              ctx.pushExceptionThrow(RuntimeExceptionStr, "Method not found on class " + frame.methodInfo.classInfo.getClassNameSlow() + " at index " + a);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }

            c = frame.peekInvokeObject(b);
            if (!c) {
              ctx.pushExceptionThrow(NullPointerExceptionStr);
              frame = ctx.current();
              stack = frame.stack;
              continue;
            }
            b = c.klass.classInfo.getMethodByName(b.utf8Name, b.utf8Signature);

            frame = Frame.create(b, []);
            if (b.isNative) {
              frame.local.push(c[b.virtualName]);
              frame.local.push(c);
              d = [];
              ArrayUtilities.popArgsInto(stack, b, d);
              frame.local.push(d);
            } else if (b.state === MethodState.Compiled) {
              // TODO
            } else {
              ArrayUtilities.popArgSlotsInto(stack, b, frame.local);
            }
            stack = frame.stack;
            ctx.pushFrame(frame);
            if (b.isSynchronized) {
              if (!frame.lockObject) {
                frame.lockObject = c;
              }
              ctx.monitorEnter(frame.lockObject);
              if (ctx.U) {
                return;
              }
            }
            continue;

          case Bytecodes.LRETURN:
          case Bytecodes.DRETURN:
            a = stack.pop2();
            b = ctx.popFrame();
            if (b.lockObject) {
              if (!ctx.monitorExit(b.lockObject)) {
                frame = ctx.current();
                stack = frame.stack;
                continue;
              }
            }
            b.free();
            frame = ctx.current();
            assert(frame, "Returned a wide value to nowhere");
            stack = frame.stack;
            stack.push2(a);
            break;
          case Bytecodes.IRETURN:
          case Bytecodes.FRETURN:
          case Bytecodes.ARETURN:
          //console.log("returning a narrow value");
            a = stack.pop();
            //console.log("value=" + a);
            b = ctx.popFrame();
            if (b.lockObject) {
              if (!ctx.monitorExit(b.lockObject)) {
                frame = ctx.current();
                stack = frame.stack;
                continue;
              }
            }
            b.free();
            frame = ctx.current();
            assert(frame, "Returned a narrow value to nowhere");
            stack = frame.stack;
            stack.push(a);
            break;
          case Bytecodes.RETURN:
            b = ctx.popFrame();
            if (b.lockObject) {
              if (!ctx.monitorExit(b.lockObject)) {
                frame = ctx.current();
                stack = frame.stack;
                continue;
              }
            }
            b.free();
            frame = ctx.current();
            if (!frame) {
              ctx.stop();
              return;
            }
            stack = frame.stack;
            break;
          default:
            throw new Error("Opcode " + Bytecodes[op] + " [" + op + "] not supported.");
        }
    } while(!J2ME.Scheduler.shouldPreempt());
  }

  export class VM {
    static execute = interpret;
    static Yield = {toString: function () { return "YIELD" }};
    static Pause = {toString: function () { return "PAUSE" }};
    static DEBUG_PRINT_ALL_EXCEPTIONS = false;
  }
}

var VM = J2ME.VM;
