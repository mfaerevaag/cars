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
            catch (InterruptedException ex) { System.out.println("EXCEPTION"); return; }
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
            catch (InterruptedException ex) { System.out.println("EXCEPTION"); return; }
        }

        this.leavingCount++;


        if(this.leavingCount == this.threshold) {
            this.mode = BarrierSelector.INCOMING;
            this.leavingCount = 0;

            if(this.increaseThreshold > 1) {
                this.threshold = this.increaseThreshold;
                this.increaseThreshold = -1;
            }

            notifyAll();
        }
    }

    public synchronized void setThreshold(int k) {
        // Waiting for all cars "flagged" for leaving.
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
                System.out.println("Before stuff: incC: " + this.incomingCount + ", leaC: " + this.leavingCount + ", threshold: " + this.threshold);

                this.leavingCount = - this.incomingCount + k;
                this.incomingCount = 0;
                this.threshold = k;

                System.out.println("After stuff: incC: " + this.incomingCount + ", leaC: " + this.leavingCount + ", threshold: " + this.threshold);

                notifyAll();

            }else {
                this.threshold = k;
            }
            // Check if it should release
        } else if (k > this.threshold) {
            this.increaseThreshold = k;
            System.out.println("Before stuff: incC: " + this.incomingCount + ", leaC: " + this.leavingCount + ", threshold: " + this.threshold);
            while (this.mode != BarrierSelector.LEAVING) {
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

            System.out.println("After stuff: incC: " + this.incomingCount + ", leaC: " + this.leavingCount + ", threshold: " + this.threshold);
            //TODO: something with waiting!
        }
    }

    public synchronized void printArriving(int carNo) {
        System.out.println("Car # " + carNo + " arriving at barrier. incC: " + this.incomingCount + ", leaC: " + this.leavingCount);
    }

    public synchronized void printLeaving(int carNo) {
        System.out.println("Car # " + carNo + " left barrier. incC: " + this.incomingCount + ", leaC: " + this.leavingCount);
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
