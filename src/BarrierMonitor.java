public class BarrierMonitor {

    private boolean active;
    public int threshold, incomingCount, leavingCount;
    private BarrierSelector mode;

    public BarrierMonitor() {
        this.active = false;
        this.threshold = 9;
        this.incomingCount = 0;
        this.leavingCount = 0;
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

        //TODO: remove this statement
        if(this.incomingCount > this.threshold) {
            System.out.println("ASLDOASKDO");
            this.incomingCount--;
            notifyAll();
        }

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

        //TODO: remove this statement
        if(this.leavingCount > this.threshold) {
            System.out.println("CXVXCMVNCXMNVCXM");
            this.leavingCount--;
            notifyAll();
        }

        if(this.leavingCount == this.threshold) {
            this.mode = BarrierSelector.INCOMING;
            this.leavingCount = 0;
            notifyAll();
        }
    }

    public synchronized void setThreshold(int k) {
        // Waiting for all cars "flagged" for leaving.
        // This is always in the order of milliseconds, as cars cannot be sleeping in this period.
        // So we consider it instant.
        while (this.mode == BarrierSelector.LEAVING) {
            try {
                if(!this.active) //Check if barrier is still active when awoken
                    return;
                else
                    wait();
            }
            catch (InterruptedException ex) { return; }
        }


        if (k > this.threshold) {

            //TODO: something with waiting!
        } else if (k < this.threshold) {
            if (k <= this.incomingCount) {


                this.mode = BarrierSelector.LEAVING;
                System.out.println("Before stuff: incC: " + this.incomingCount + ", leaC: " + this.leavingCount + ", threshold: " + this.threshold);

                this.leavingCount = -this.incomingCount + k;
                this.incomingCount = 0;
                this.threshold = k;


                System.out.println("After stuff: incC: " + this.incomingCount + ", leaC: " + this.leavingCount + ", threshold: " + this.threshold);

                notifyAll();

            }else {
                this.threshold = k;
            }
            // Check if it should release
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
        this.active = true;
        this.incomingCount = 0;
        this.leavingCount = 0;
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
    }


}
