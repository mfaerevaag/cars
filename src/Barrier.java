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
                this.freeIncoming(this.incomingCount - 1);
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
                this.freeLeaving(this.leavingCount - 1);
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
                this.freeIncoming(this.incomingCount);
                this.freeLeaving(this.incomingCount);
                this.incomingCount = 0;
                this.leavingCount = 0;
            }
            this.mutex.V();

        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    private void freeIncoming(int n) {
        // last car does not P(), so no need to release it
        for (int i = 0; i < n; i++)
            this.barrierIncoming.V();
    }

    private void freeLeaving(int n) {
        // last car does not P(), so no need to release it
        for (int i = 0; i < n; i++)
            this.barrierLeaving.V();
    }


}

//import javax.sound.midi.SysexMessage;
//import java.util.Arrays;
//
//public class Barrier {
//
//    private boolean active;
//    private int threshold;
//    private int count;
//    private int roundCount;
//
//    // Dealing with speeding
//    private int lowestRoundCount; //Save the lowest carCurrentRound. If any car is
//    private int speederCounts;
//
//    private int[] carCurrentRound;
//    private Semaphore barrier, mutex;
//    private CarDisplayI cd;
//
//    public Barrier(CarDisplayI cd) {
//        this.cd = cd;
//        this.active = false;
//        this.threshold = 9; // TODO: extend
//        this.count = 0;
//        this.roundCount = 0;
//
//        this.lowestRoundCount = 0;
//        this.speederCounts = 0;
//
//        this.carCurrentRound = new int[9];
//        this.barrier = new Semaphore(0);
//        this.mutex = new Semaphore(1);
//    }
//
//    /**
//     * Wait for others to arrive (if barrier active)
//     */
//    public void sync(int carNo) throws Exception {
//
//        this.mutex.P();
//
//        this.invariantCheck(carNo);
////        System.out.println("Car # " + carNo + " calling .sync()");
//
//        boolean activeCopy = this.active;
////        this.mutex.V();
//
//        if (activeCopy) {
////            this.mutex.P();
//
//            this.count++;
////            System.out.println("Car # " + carNo + " was the car no. " + this.count + " to arrive this round.");
//            if (this.count < this.threshold) { // All cars, except one
//
//                boolean freeToIgnore = this.carCurrentRound[carNo] < this.roundCount;
//                System.out.println("Car #" + carNo + " carRound: " + this.carCurrentRound[carNo] + ", barrierRound: " + this.roundCount);
//                this.mutex.V();
//
//                if (! freeToIgnore)
//                    this.barrier.P();
//
//                this.mutex.P();
//                this.carCurrentRound[carNo]++;
////                System.out.println("Car # "+ carNo + "left: " + Arrays.toString(this.carCurrentRound));
//                this.mutex.V();
//
//            } else { // Final car needed to start a new round
//
//                this.roundCount++;
//                this.free(this.count - 1);
//
//                this.count = 0;
////                System.out.println("Car # " + carNo + " was the last to arrive this round.");
////                System.out.println(Arrays.toString(this.carCurrentRound));
//                this.carCurrentRound[carNo]++;
//                this.mutex.V();
//            }
//        }else {
//            this.mutex.V();
//        }
//
//        this.mutex.P();
//
//        this.invariantCheck(carNo);
//
//        this.mutex.V();
//
//    }
//
//    /**
//     * Activate barrier
//     */
//    public void on() {
//
//        try {
//
//            this.mutex.P();
//            if (!this.active) {
//                this.active = true;
//
//                this.roundCount = 0;
//                this.carCurrentRound = new int[9];
//            }
//            this.mutex.V();
//
//        } catch (InterruptedException e) {
//            e.printStackTrace();
//        }
//    }
//
//    /**
//     * Deactivate barrier
//     */
//    public void off() {
//
//        try {
//            this.mutex.P();
//            if (this.active) {
//
//                this.active = false;
//                this.free(this.count);
//                this.count = 0;
//
//            }
//            this.mutex.V();
//
//        } catch (InterruptedException e) {
//            e.printStackTrace();
//        }
//    }
//
//    private void free(int n) {
//        // last car does not P(), so no need to release it
//        for (int i = 0; i < n; i++)
//            this.barrier.V();
//    }
//
//    private int getLowestRoundCount() {
//        int min = 100000000;
//        for(int i = 0; i < this.carCurrentRound.length; i++) {
//            if (this.carCurrentRound[i] < min)
//                min = this.carCurrentRound[i];
//        }
//
//        return min;
//
//    }
//
//    private void invariantCheck(int carNo) throws Exception{
//        //Find min and max
//        int min = 100000000;
//        int max = -1;
//
//        for(int i = 0; i < this.carCurrentRound.length; i++) {
//            if (this.carCurrentRound[i] < min)
//                min = this.carCurrentRound[i];
//
//            if (this.carCurrentRound[i] > max)
//                max = this.carCurrentRound[i];
//
//        }
//
//        if (max - min > 1) {
//            System.out.println("Car #" + carNo + " carRound: " + this.carCurrentRound[carNo] + ", barrierRound: " + this.roundCount);
//            System.out.println("Lowest roundCount: " + this.getLowestRoundCount());
//            this.cd.println("Error, invariant violated!");
//            throw (new Exception("Error, invariant violated!"));
//        }
//
//
//    }
//}