module J2ME {
  /** @const */ export var MAX_PRIORITY: number = 10;
  /** @const */ export var MIN_PRIORITY: number = 1;
  /** @const */ export var NORMAL_PRIORITY: number = 5;

  /** @const */ export var ISOLATE_MIN_PRIORITY: number = 1;
  /** @const */ export var ISOLATE_NORM_PRIORITY: number = 2;
  /** @const */ export var ISOLATE_MAX_PRIORITY: number = 3;

  /**
   * Number of ms that a thread is allowed to execute before being
   * preempted.
   *
   * @type {number}
   * @const
   */
  var PREEMPTION_INTERVAL: number = 7;

  /**
   * Number of preemptions thus far.
   */
  export var preemptionCount: number = 0;

  /**
   * Time when the context began execution.
   * @type {number}
   */
  var threadStartTime: number = 0;

  /**
   * Used to block preemptions from happening during code that can't handle them.
   */
  export var preemptionLockLevel: number = 0;

  /**
   * True when a setTimeout has been scheduled to run the threads.
   */
  var isRunScheduled: boolean = false;

  /**
   * queue
   *
   * The queue of Contexts waiting to be run
   */
  var queue: ContextQueue = new ContextQueue();

  export class Scheduler {

    static enqueue(ctx: Context) {
      queue.put(ctx);
      Scheduler.scheduleRun();
    }

    static shouldPreempt(): boolean {
      if (preemptionLockLevel > 0) {
        return false;
      }

      var now = performance.now();
      var ret = now - threadStartTime > PREEMPTION_INTERVAL;
      if (ret) {
        preemptionCount++;
        threadWriter && threadWriter.writeLn("Thread execution timeout. Thread time: " + (now - threadStartTime).toFixed(2) + "ms, samples: " + PS + ", count: " + preemptionCount);
      }
      return ret;
    }

    private static run() {
      isRunScheduled = false;

      threadStartTime = performance.now();
      queue.get(threadStartTime).execute();

      if (queue.hasMore()) {
        Scheduler.scheduleRun();
      }
    }

    private static scheduleRun() {
      if (isRunScheduled) {
        return;
      }
      isRunScheduled = true;

      (<any>window).nextTickDuringEvents(Scheduler.run);
    }
  }
}
