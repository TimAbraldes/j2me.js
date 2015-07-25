/*
 node-jvm
 Copyright (c) 2013 Yaroslav Gaponov <yaroslav.gaponov@gmail.com>
*/

declare var Shumway;
declare var profiling;

interface Array<T> {
  push2: (value) => void;
  pop2: () => any;
  pushKind: (kind: J2ME.Kind, value) => void;
  popKind: (kind: J2ME.Kind) => any;
  read: (i) => any;
}

module J2ME {
  import assert = Debug.assert;
  import Bytecodes = Bytecode.Bytecodes;
  declare var VM;

  export enum WriterFlags {
    None  = 0x00,
    Trace = 0x01,
    Link  = 0x02,
    Init  = 0x04,
    Perf  = 0x08,
    Load  = 0x10,
    JIT   = 0x20,
    Code  = 0x40,
    Thread = 0x80,

    All   = Trace | Link | Init | Perf | Load | JIT | Code | Thread
  }

  /**
   * Toggle VM tracing here.
   */
  export var writers = WriterFlags.None;

  Array.prototype.push2 = function(value) {
    this.push(value);
    this.push(null);
    return value;
  }

  Array.prototype.pop2 = function() {
    this.pop();
    return this.pop();
  }

  Array.prototype.pushKind = function(kind: Kind, value) {
    if (isTwoSlot(kind)) {
      this.push2(value);
      return;
    }
    this.push(value);
  }

  Array.prototype.popKind = function(kind: Kind) {
    if (isTwoSlot(kind)) {
      return this.pop2();
    }
    return this.pop();
  }

  // A convenience function for retrieving values in reverse order
  // from the end of the stack.  stack.read(1) returns the topmost item
  // on the stack, while stack.read(2) returns the one underneath it.
  Array.prototype.read = function(i) {
    return this[this.length - i];
  };

  export var frameCount = 0;

  export class Frame {
    methodInfo: MethodInfo;
    local: any [];
    stack: any [];
    code: Uint8Array;
    pc: number;
    opPC: number;
    lockObject: java.lang.Object;

    static dirtyStack: Frame [] = [];

    constructor(methodInfo: MethodInfo, local: any []) {
      frameCount ++;
      this.stack = [];
      this.reset(methodInfo, local);
    }

    static nativeCodeVoid: Uint8Array = new Uint8Array([Bytecodes.INVOKEJS, Bytecodes.RETURN]);
    static nativeCodeLReturn: Uint8Array = new Uint8Array([Bytecodes.INVOKEJS, Bytecodes.LRETURN]);
    static nativeCodeIReturn: Uint8Array = new Uint8Array([Bytecodes.INVOKEJS, Bytecodes.IRETURN]);

    reset(methodInfo: MethodInfo, local: any []) {
      this.methodInfo = methodInfo;
      this.pc = 0;
      this.opPC = 0;
      this.stack.length = 0;
      this.local = local;
      this.lockObject = null;

      if (!methodInfo.isNative && methodInfo.state !== MethodState.Compiled) {
        this.code = methodInfo.codeAttribute ? methodInfo.codeAttribute.code : null;
        if (!this.code) {
          console.log("no code for " + methodInfo.implKey);
        }
        return;
      }

      if (methodInfo.returnKind === Kind.Void) {
        this.code = Frame.nativeCodeVoid;
      } else if (isTwoSlot(methodInfo.returnKind)) {
        this.code = Frame.nativeCodeLReturn;
      } else {
        this.code = Frame.nativeCodeIReturn;
      }
    }

    static create(methodInfo: MethodInfo, local: any []): Frame {
    //console.log("Frame.create, methodInfo=" + methodInfo);
      var dirtyStack = Frame.dirtyStack;
      if (dirtyStack.length) {
        var frame = dirtyStack.pop();
        frame.reset(methodInfo, local);
        return frame;
      } else {
        return new Frame(methodInfo, local);
      }
    }

    free() {
      Frame.dirtyStack.push(this);
    }

    incLocal(i: number, value: any) {
      this.local[i] += value | 0;
    }

    read8(): number {
      return this.code[this.pc++];
    }

    peek8(): number {
      return this.code[this.pc];
    }

    read16(): number {
      var code = this.code
      return code[this.pc++] << 8 | code[this.pc++];
    }

    patch(offset: number, oldValue: Bytecodes, newValue: Bytecodes) {
      release || assert(this.code[this.pc - offset] === oldValue, "patch target doesn't match");
      this.code[this.pc - offset] = newValue;
    }

    read32(): number {
      return this.read32Signed() >>> 0;
    }

    read8Signed(): number {
      return this.code[this.pc++] << 24 >> 24;
    }

    read16Signed(): number {
      var pc = this.pc;
      var code = this.code;
      this.pc = pc + 2
      return (code[pc] << 8 | code[pc + 1]) << 16 >> 16;
    }

    readTargetPC(): number {
      var pc = this.pc;
      var code = this.code;
      this.pc = pc + 2
      var offset = (code[pc] << 8 | code[pc + 1]) << 16 >> 16;
      return pc - 1 + offset;
    }

    read32Signed(): number {
      return this.read16() << 16 | this.read16();
    }

    tableSwitch(): number {
      var start = this.pc;
      while ((this.pc & 3) != 0) {
        this.pc++;
      }
      var def = this.read32Signed();
      var low = this.read32Signed();
      var high = this.read32Signed();
      var value = this.stack.pop();
      var pc;
      if (value < low || value > high) {
        pc = def;
      } else {
        this.pc += (value - low) << 2;
        pc = this.read32Signed();
      }
      return start - 1 + pc;
    }

    lookupSwitch(): number {
      var start = this.pc;
      while ((this.pc & 3) != 0) {
        this.pc++;
      }
      var pc = this.read32Signed();
      var size = this.read32();
      var value = this.stack.pop();
      lookup:
      for (var i = 0; i < size; i++) {
        var key = this.read32Signed();
        var offset = this.read32Signed();
        if (key === value) {
          pc = offset;
        }
        if (key >= value) {
          break lookup;
        }
      }
      return start - 1 + pc;
    }

    wide() {
      var stack = this.stack;
      var op = this.read8();
      switch (op) {
        case Bytecodes.ILOAD:
        case Bytecodes.FLOAD:
        case Bytecodes.ALOAD:
          stack.push(this.local[this.read16()]);
          break;
        case Bytecodes.LLOAD:
        case Bytecodes.DLOAD:
          stack.push2(this.local[this.read16()]);
          break;
        case Bytecodes.ISTORE:
        case Bytecodes.FSTORE:
        case Bytecodes.ASTORE:
          this.local[this.read16()] = stack.pop();
          break;
        case Bytecodes.LSTORE:
        case Bytecodes.DSTORE:
          this.local[this.read16()] = stack.pop2();
          break;
        case Bytecodes.IINC:
          var index = this.read16();
          var value = this.read16Signed();
          this.local[index] += value;
          break;
        case Bytecodes.RET:
          this.pc = this.local[this.read16()];
          break;
        default:
          var opName = Bytecodes[op];
          throw new Error("Wide opcode " + opName + " [" + op + "] not supported.");
      }
    }

    /**
     * Returns the |object| on which a call to the specified |methodInfo| would be
     * called.
     */
    peekInvokeObject(methodInfo: MethodInfo): java.lang.Object {
      release || assert(!methodInfo.isStatic, "peekInvokeObject called on static method");
      var i = this.stack.length - methodInfo.argumentSlots - 1;
      release || assert (i >= 0, "not enough stack in peekInvokeObject");
      release || assert (this.stack[i] !== undefined, "unexpected undefined in peekInvokeObject");
      return this.stack[i];
    }

    toString() {
      return this.methodInfo.implKey + " " + this.pc;
    }

    trace(writer: IndentingWriter) {
      var localStr = this.local.map(function (x) {
        return toDebugString(x);
      }).join(", ");

      var stackStr = this.stack.map(function (x) {
        return toDebugString(x);
      }).join(", ");

      writer.writeLn(("" + this.pc).padLeft(" ", 4) + " " + localStr + " | " + stackStr);
    }
  }

  export class Context {
    private static _nextId: number = 0;
    private static _colors = [
      IndentingWriter.PURPLE,
      IndentingWriter.YELLOW,
      IndentingWriter.GREEN,
      IndentingWriter.RED,
      IndentingWriter.BOLD_RED
    ];
    private static writer: IndentingWriter = new IndentingWriter(false, function (s) {
      console.log(s);
    });

    private static ctxs: Context [] = [];

    id: number;

    /**
     * Are we currently unwinding the stack?
     */
    U: J2ME.VMState = J2ME.VMState.Running;

    /**
     * Whether or not the context is currently paused.  The profiler uses this
     * to distinguish execution time from paused time in an async method.
     */
    paused: boolean = true;

    /*
     * Contains method frames
     */
    private frames: Frame [];
    lockTimeout: number;
    lockLevel: number;
    thread: java.lang.Thread;
    writer: IndentingWriter;
    methodTimeline: any;
    virtualRuntime: number;
    constructor(public runtime: Runtime) {
      var id = this.id = Context._nextId ++;
      this.frames = [];
      this.runtime = runtime;
      this.runtime.addContext(this);
      this.virtualRuntime = 0;
      this.writer = new IndentingWriter(false, function (s) {
        console.log(s);
      });
      if (profile && typeof Shumway !== "undefined") {
        this.methodTimeline = new Shumway.Tools.Profiler.TimelineBuffer("Thread " + this.runtime.id + ":" + this.id);
        methodTimelines.push(this.methodTimeline);
      }
    }

    public static color(id) {
      if (inBrowser) {
        return id;
      }
      return Context._colors[id % Context._colors.length] + id + IndentingWriter.ENDC;
    }
    public static currentContextPrefix() {
      if ($) {
        return Context.color($.id) + "." + $.ctx.runtime.priority + ":" + Context.color($.ctx.id) + "." + $.ctx.getPriority();
      }
      return "";
    }

    /**
     * Sets global writers. Uncomment these if you want to see trace output.
     */
    static setWriters(writer: IndentingWriter) {
      traceWriter = writers & WriterFlags.Trace ? writer : null;
      perfWriter = writers & WriterFlags.Perf ? writer : null;
      linkWriter = writers & WriterFlags.Link ? writer : null;
      jitWriter = writers & WriterFlags.JIT ? writer : null;
      codeWriter = writers & WriterFlags.Code ? writer : null;
      initWriter = writers & WriterFlags.Init ? writer : null;
      threadWriter = writers & WriterFlags.Thread ? writer : null;
      loadWriter = writers & WriterFlags.Load ? writer : null;
    }

    getPriority() {
      if (this.thread) {
        return this.thread.priority;
      }
      return NORMAL_PRIORITY;
    }

    kill() {
      if (this.thread) {
        this.thread.alive = false;
      }
      this.runtime.removeContext(this);
    }

    current(): Frame {
      var frames = this.frames;
      return frames[frames.length - 1];
    }

    pushExceptionThrow(className: string, msg?: string) {
      this.setAsCurrentContext();

      try {
        var classInfo = CLASSES.getClass("org/mozilla/internal/Sys");
        var methodInfo = classInfo.getMethodByNameString("throwException", "(Ljava/lang/Exception;)V");
        var frame = Frame.create(methodInfo, []);
        this.pushFrame(frame);

        if (!msg) {
          msg = "";
        }
        msg = "" + msg;

        classInfo = CLASSES.loadAndLinkClass(className);
        runtimeCounter && runtimeCounter.count("createException " + className);
        var exception = new classInfo.klass();
        frame.local[0] = exception;

        methodInfo = classInfo.getMethodByNameString("<init>", "(Ljava/lang/String;)V");
        frame = Frame.create(methodInfo, [exception, newString(msg)]);
        this.pushFrame(frame);

        this.runtime.maybePushClassInit(classInfo);
      } finally {
        this.clearCurrentContext();
      }
    }

    popFrame(): Frame {
      var frame = this.frames.pop();
      if (profile) {
        this.leaveMethodTimeline(frame.methodInfo.implKey, MethodType.Interpreted);
      }
      return frame;
    }

    pushFrame(frame: Frame) {
      if (profile) {
        this.enterMethodTimeline(frame.methodInfo.implKey, MethodType.Interpreted);
      }
      this.frames.push(frame);
    }

    private setAsCurrentContext() {
      if ($) {
        threadTimeline && threadTimeline.leave();
        Context.ctxs.push($.ctx);
      }
      threadTimeline && threadTimeline.enter(this.runtime.id + ":" + this.id);
      $ = this.runtime;
      if ($.ctx === this) {
        return;
      }
      $.ctx = this;
      Context.setWriters(this.writer);
    }

    private clearCurrentContext() {
      if ($) {
        threadTimeline && threadTimeline.leave();
      }
      var ctx = Context.ctxs.pop();
      $ = ctx ? ctx.runtime : null;
      Context.setWriters(Context.writer);
    }

    // NB: This runs while a different context is technically active,
    // so any logging of this function appears as if it is coming
    // from the other context.
    start(frames: Frame[]) {
      for (var i = 0; i < frames.length; i++) {
        this.pushFrame(frames[i]);
      }
      this.resume();
    }

    execute() {
      this.setAsCurrentContext();
      profile && this.resumeMethodTimeline();

      VM.execute();
      this.clearCurrentContext();

      if (VMState.Stopping === this.U || this.frames.length === 0) {
        this.kill();
        return;
      }

      if (VMState.Running === this.U) {
        Scheduler.enqueue(this);
      }
    }

    // NB: This runs while a different context is technically active,
    // so any logging of this function appears as if it is coming
    // from the other context (or no context at all).
    resume() {
      this.U = VMState.Running;
      Scheduler.enqueue(this);
    }

    block(obj, queue, lockLevel) {
      obj._lock[queue].push(this);
      this.lockLevel = lockLevel;
      this.pause("block");
    }

    unblock(obj, queue, notifyAll) {
      while (obj._lock[queue].length) {
        var ctx = obj._lock[queue].pop();
        if (!ctx)
          continue;
        ctx.wakeup(obj)
        if (!notifyAll)
          break;
      }
    }

    wakeup(obj) {
      if (this.lockTimeout !== null) {
        window.clearTimeout(this.lockTimeout);
        this.lockTimeout = null;
      }
      if (obj._lock.level !== 0) {
        obj._lock.ready.push(this);
      } else {
        this.resume();
        while (this.lockLevel-- > 0) {
          this.monitorEnter(obj);
        }
      }
    }

    monitorEnter(object: java.lang.Object) {
      var lock = object._lock;
      if (!lock) {
        object._lock = new Lock(this, 1);
        return;
      }
      if (lock.ctx === this) {
        ++lock.level;
        return;
      }
      if (lock.level === 0) {
        lock.ctx = this;
        lock.level = 1;
        return;
      }
      this.block(object, "ready", 1);
    }

    monitorExit(object: java.lang.Object): boolean {
      var lock = object._lock;
      if (lock.ctx !== this || lock.level === 0) {
        this.pushExceptionThrow(IllegalMonitorStateExceptionStr);
        return false;
      }
      if (--lock.level > 0) {
        return true;
      }
      if (lock.ready.length > 0) {
        this.unblock(object, "ready", false);
      }
      return true;
    }

    wait(object: java.lang.Object, timeout: number): boolean {
      var lock = object._lock;
      if (timeout < 0) {
        this.pushExceptionThrow(IllegalArgumentExceptionStr);
        return false;
      }
      if (!lock || lock.ctx !== this || lock.level === 0) {
        this.pushExceptionThrow(IllegalMonitorStateExceptionStr);
        return false;
      }
      var lockLevel = lock.level;
      for (var i = lockLevel; i > 0; i--) {
        // This can technically throw an exception but we've already
        // checked the condition that could cause that to happen
        this.monitorExit(object);
      }
      if (timeout) {
        var self = this;
        this.lockTimeout = window.setTimeout(function () {
          for (var i = 0; i < lock.waiting.length; i++) {
            var ctx = lock.waiting[i];
            if (ctx === self) {
              lock.waiting[i] = null;
              ctx.wakeup(object);
            }
          }
        }, timeout);
      } else {
        this.lockTimeout = null;
      }
      this.block(object, "waiting", lockLevel);
      return true;
    }

    notify(obj, notifyAll) {
      if (!obj._lock || obj._lock.ctx !== this || obj._lock.level === 0) {
        this.pushExceptionThrow(IllegalMonitorStateExceptionStr);
        return false;
      }

      this.unblock(obj, "waiting", notifyAll);
      return true;
    }

    pauseMethodTimeline() {
      release || assert(!this.paused, "context is not paused");

      if (profiling) {
        this.methodTimeline.enter("<pause>", MethodType.Interpreted);
      }

      this.paused = true;
    }

    resumeMethodTimeline() {
      release || assert(this.paused, "context is paused");

      if (profiling) {
        this.methodTimeline.leave("<pause>", MethodType.Interpreted);
      }

      this.paused = false;
    }

    /**
     * Re-enters all the frames that are currently on the stack so the full stack
     * trace shows up in the profiler.
     */
    restartMethodTimeline() {
      for (var i = 0; i < this.frames.length; i++) {
        var frame = this.frames[i];
        this.methodTimeline.enter(frame.methodInfo.implKey, MethodType.Interpreted);
      }

      if (this.paused) {
        this.methodTimeline.enter("<pause>", MethodType.Interpreted);
      }
    }

    enterMethodTimeline(key: string, methodType: MethodType) {
      if (profiling) {
        this.methodTimeline.enter(key, MethodType[methodType]);
      }
    }

    leaveMethodTimeline(key: string, methodType: MethodType) {
      if (profiling) {
        this.methodTimeline.leave(key, MethodType[methodType]);
      }
    }

    pause(reason: string) {
      unwindCount ++;
      threadWriter && threadWriter.writeLn("pausing " + reason);
      runtimeCounter && runtimeCounter.count("pausing " + reason);
      this.U = VMState.Pausing;
      profile && this.pauseMethodTimeline();
    }

    stop() {
      this.U = VMState.Stopping;
    }
  }
}

var Context = J2ME.Context;
var Frame = J2ME.Frame;
