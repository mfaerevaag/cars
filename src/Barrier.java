enum BarrierSelector {
    INCOMING, LEAVING
}

public class Barrier {

    private boolean active;
    private int threshold, incomingCount, leavingCount;
    private int[] debug_carsRounds;

    private Semaphore barrierIncoming, barrierLeaving, mutex;

    public Barrier() {
        this.active = false;
        this.threshold = 9; // TODO: extend

        this.debug_carsRounds = new int[9]; //TODO: remove

        this.barrierIncoming = new Semaphore(0);
        this.barrierLeaving = new Semaphore(0);
        this.mutex = new Semaphore(1);
    }

    /**
     * Wait for others to arrive (if barrier active)
     */
    public void sync(int carNo) throws Exception {

        this.mutex.P();

        this.checkInvariant(carNo); //TODO: remove

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
                this.debug_carsRounds[carNo]++; //TODO: remove
                this.checkInvariant(carNo);    //TODO: remove
                this.mutex.V();
                this.barrierLeaving.P();

            }else {
                this.free(this.leavingCount - 1, BarrierSelector.LEAVING);
                this.leavingCount = 0;
                this.debug_carsRounds[carNo]++;//TODO: remove
                this.checkInvariant(carNo);//TODO: remove
                this.mutex.V();
            }

        }else {
            this.mutex.V();
        }

    }

    private void checkInvariant(int carNo) throws Exception{ //TODO: remove
        int min = 100000000;
        int max = -1;

        for (int carRounds : this.debug_carsRounds) {
            if (carRounds < min)
                min = carRounds;

            if (carRounds > max)
                max = carRounds;
        }

        if (max - min > 1)
            throw new Exception("MaxRound: " + max + ", MinRound: " + min + ", car # " + carNo);
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

                for (int i = 0; i < this.debug_carsRounds.length; i++) {
                    this.debug_carsRounds[i] = 0;
                }
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

                for (int i = 0; i < this.debug_carsRounds.length; i++) {
                    this.debug_carsRounds[i] = 0;
                }

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

    private void free(int n, BarrierSelector selector) {
        for (int i = 0; i < n; i++) {
            if (selector == BarrierSelector.INCOMING)
                this.barrierIncoming.V();
            else
                this.barrierLeaving.V();
        }

    }

//    private void freeIncoming(int n) {
//        // last car does not P(), so no need to release it
//        for (int i = 0; i < n; i++)
//            this.barrierIncoming.V();
//    }
//
//    private void freeLeaving(int n) {
//        // last car does not P(), so no need to release it
//        for (int i = 0; i < n; i++)
//            this.barrierLeaving.V();
//    }


}
