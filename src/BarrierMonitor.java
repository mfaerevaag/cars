public class BarrierMonitor {

    private boolean active;
    private int threshold, incomingCount, leavingCount;
    private BarrierSelector mode;

    private Semaphore barrierIncoming, barrierLeaving, mutex;

    public BarrierMonitor() {
        this.active = false;
        this.threshold = 9;
        this.incomingCount = 0;
        this.leavingCount = 0;
        this.mode = BarrierSelector.INCOMING;

        this.barrierIncoming = new Semaphore(0);
        this.barrierLeaving = new Semaphore(0);
        this.mutex = new Semaphore(1);
    }


    public synchronized void sync() {
        //TODO: barrier-mode. Use BarrierSelector

        if (!this.active)
            return;

        // 1st - all cars must arrive ("incoming")

        // Wait until the barrier accepts incoming cars
        while (this.mode != BarrierSelector.INCOMING) {
            try {
                if(!this.active) //Check if barrier is still active when awoken
                    return;
                else
                    wait();
            }
            catch (InterruptedException ex) { return; }
        }

        this.incomingCount++;

        if(this.incomingCount == this.threshold) {
            this.mode = BarrierSelector.LEAVING;
            this.incomingCount = 0;
            notifyAll();
        }

        // 2nd - all cars must leave ("leaving")


        // Wait until the barrier accepts leaving cars
        while (this.mode != BarrierSelector.LEAVING) {
            try {
                if(!this.active) //Check if barrier is still active when awoken
                    return;
                else
                    wait();
            }
            catch (InterruptedException ex) { return; }
        }

        this.leavingCount++;

        if(this.leavingCount == this.threshold) {
            this.mode = BarrierSelector.INCOMING;
            this.leavingCount = 0;
            notifyAll();
        }
    }


    /**
     * Activate barrier
     */
    public synchronized void on() {
        this.active = true;
//        try {
//            this.mutex.P();
//
//            if (!this.active) {
//                this.active = true;
//
//                this.incomingCount = 0;
//                this.leavingCount = 0;
//            }
//
//            this.mutex.V();
//
//        } catch (InterruptedException e) {
//            e.printStackTrace();
//        }
    }

    /**
     * Deactivate barrier
     */
    public synchronized void off() {
        this.active = false;
        this.notifyAll();
        this.leavingCount = 0;
        this.incomingCount = 0;
        this.mode = BarrierSelector.INCOMING;
//        try {
//            this.mutex.P();
//            if (this.active) {
//
//                this.active = false;
//                this.free(this.incomingCount, BarrierSelector.INCOMING);
//                this.free(this.leavingCount+this.incomingCount, BarrierSelector.LEAVING); //leavingCount PLUS incomingCount, as the just released incomings will need to pass the leaving barrier
//                this.incomingCount = 0;
//                this.leavingCount = 0;
//            }
//            this.mutex.V();
//
//        } catch (InterruptedException e) {
//            e.printStackTrace();
//        }
    }


}
