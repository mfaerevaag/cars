public class BarrierMonitor {

    private boolean active;
    private int threshold, incomingCount, leavingCount;
    private BarrierSelector mode;

    private int increaseThreshold;

    public BarrierMonitor() {
        this.active = false;
        this.threshold = 9;
        this.incomingCount = 0;
        this.leavingCount = 0;
        this.increaseThreshold = -1;
        this.mode = BarrierSelector.INCOMING;
    }


    public synchronized void sync() {
        if (!this.active)
            return;

        // 1st - all cars must arrive ("incoming")

        // Wait until the barrier accepts incoming cars
        this.waitForMode(BarrierSelector.INCOMING);
        if(!this.active) //Check if barrier is still active when awoken
            return;

        this.incomingCount++;

        if(this.incomingCount == this.threshold) {
            this.mode = BarrierSelector.LEAVING;
            this.incomingCount = 0;

            notifyAll();
        }

        // 2nd - all cars must leave ("leaving")

        // Wait until the barrier accepts leaving cars
        this.waitForMode(BarrierSelector.LEAVING);
        if(!this.active) //Check if barrier is still active when awoken
            return;

        this.leavingCount++;

        if(this.leavingCount == this.threshold) {
            this.mode = BarrierSelector.INCOMING;
            this.leavingCount = 0;

            // This statement is part of task "EXTRA (E)" and used to implement a variable threshold value
            if(this.increaseThreshold > 1) {
                this.threshold = this.increaseThreshold;
                this.increaseThreshold = -1;
            }

            notifyAll();
        }
    }

    public synchronized void setThreshold(int k) {
        // Waiting for all cars that are flagged for leaving actually leaves.
        // This is always in the order of milliseconds, as cars cannot be sleeping in this period.
        // So we consider it instant.
        while (this.mode == BarrierSelector.LEAVING) {
            try {
                if(!this.active) {//Check if barrier is still active when awoken
                    this.threshold = k;
                    return;
                }
                else
                    wait();
            }
            catch (InterruptedException ex) { return; }
        }


        if (k < this.threshold) {
            if (k <= this.incomingCount) {

                this.mode = BarrierSelector.LEAVING;

                this.leavingCount = k - this.incomingCount;
                this.incomingCount = 0;
                this.threshold = k;

                notifyAll();

            }else {
                this.threshold = k;
            }
            // Check if it should release
        } else if (k > this.threshold) {
            this.increaseThreshold = k;

            while (this.mode == BarrierSelector.INCOMING) {
                try {
                    if(!this.active) { //Check if barrier is still active when awoken
                        this.threshold = k;
                        return;
                    }
                    else
                        wait();
                }
                catch (InterruptedException ex) { return; }
            }
        }
    }


    private void waitForMode(BarrierSelector selector) {
        // Wait until the barrier accepts the wanted type of cars
        while (this.mode != selector) {
            try {
                if(!this.active) //Check if barrier is still active when awoken
                    return;
                else
                    wait();
            }
            catch (InterruptedException ex) { return; }
        }
    }

    /**
     * Activate barrier
     */
    public synchronized void on() {
        if (! this.active) {
            this.active = true;
            this.incomingCount = 0;
            this.leavingCount = 0;
            this.increaseThreshold = -1;
        }
    }

    /**
     * Deactivate barrier
     */
    public synchronized void off() {
        this.active = false;
        this.leavingCount = 0;
        this.incomingCount = 0;
        this.mode = BarrierSelector.INCOMING;
        this.increaseThreshold = -1;
        this.notifyAll();
    }


}
