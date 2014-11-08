import java.util.Arrays;

public class Barrier {

    private boolean active;
    private int threshold;
    private int count;
    private int roundCount;
    private int[] carCurrentRound;
    private Semaphore barrier, mutex;

    public Barrier() {
        this.active = false;
        this.threshold = 9; // TODO: extend
        this.count = 0;
        this.roundCount = 0;
        this.carCurrentRound = new int[9];
        this.barrier = new Semaphore(0);
        this.mutex = new Semaphore(1);
    }

    /**
     * Wait for others to arrive (if barrier active)
     */
    public void sync(int carNo) throws InterruptedException {

        this.mutex.P();
        boolean activeCopy = this.active;
        this.mutex.V();

        if (activeCopy) {
            this.mutex.P();

            this.count++;

            if (this.count < this.threshold) { // All cars, except one


                boolean freeToIgnore = this.carCurrentRound[carNo] != this.roundCount;
                this.mutex.V();

                if (! freeToIgnore)
                    this.barrier.P();

                this.mutex.P();
                this.carCurrentRound[carNo]++;
                System.out.println(Arrays.toString(this.carCurrentRound));
                this.mutex.V();

            } else { // Final car needed to start a new round

                this.roundCount++;
                System.out.println("RoundCount updated:" + roundCount);

                this.free(this.count - 1);
                this.count = 0;

                this.carCurrentRound[carNo]++;
                System.out.println(Arrays.toString(this.carCurrentRound));
                this.mutex.V();
            }
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

                this.roundCount = 0;
                this.carCurrentRound = new int[9];
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

            if (this.active) {

                this.mutex.P();

                this.active = false;
                this.free(this.count);
                this.count = 0;

                this.mutex.V();
            }


        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    private void free(int n) {
        // last car does not P(), so no need to release it
        for (int i = 0; i < n; i++)
            this.barrier.V();
    }

}