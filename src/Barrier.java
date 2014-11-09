enum BarrierSelector {
    INCOMING, LEAVING
}

public class Barrier {

    private boolean active;
    private int threshold, incomingCount, leavingCount;

    private Semaphore barrierIncoming, barrierLeaving, mutex;

    public Barrier() {
        this.active = false;
        this.threshold = 9;
        this.incomingCount = 0;
        this.leavingCount = 0;
        this.barrierIncoming = new Semaphore(0);
        this.barrierLeaving = new Semaphore(0);
        this.mutex = new Semaphore(1);
    }

    /**
     * Wait for others to arrive (if barrier active)
     */
    public void sync() throws Exception {

        this.mutex.P();

        if (this.active) {

            // 1st - all cars must arrive ("incoming")

            this.incomingCount++;

            if (this.incomingCount < this.threshold) { // All cars, except one
                this.mutex.V();
                this.barrierIncoming.P();

            } else { // Final car needed to start a new round
                this.free(this.incomingCount - 1, BarrierSelector.INCOMING);
                this.incomingCount = 0;
                this.mutex.V();
            }


            // 2nd - all cars must leave ("leaving")

            this.mutex.P();

            this.leavingCount++;

            if (this.leavingCount < this.threshold) {
                this.mutex.V();
                this.barrierLeaving.P();

            }else {
                this.free(this.leavingCount - 1, BarrierSelector.LEAVING);
                this.leavingCount = 0;
                this.mutex.V();
            }

        }else {
            this.mutex.V();
        }

    }

    /**
     * Activate barrier
     */
    public void on() {

        try {
            this.mutex.P();

            if (!this.active) {
                this.active = true;

                this.incomingCount = 0;
                this.leavingCount = 0;
            }

            this.mutex.V();

        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    /**
     * Deactivate barrier
     */
    public void off() {

        try {
            this.mutex.P();
            if (this.active) {

                this.active = false;
                this.free(this.incomingCount, BarrierSelector.INCOMING);
                this.free(this.leavingCount+this.incomingCount, BarrierSelector.LEAVING); //leavingCount PLUS incomingCount, as the just released incomings will need to pass the leaving barrier
                this.incomingCount = 0;
                this.leavingCount = 0;
            }
            this.mutex.V();

        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    /**
     * Signals n times from the selected semaphore
     */
    private void free(int n, BarrierSelector selector) {
        for (int i = 0; i < n; i++) {
            if (selector == BarrierSelector.INCOMING)
                this.barrierIncoming.V();
            else
                this.barrierLeaving.V();
        }

    }


}
