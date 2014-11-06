public class Barrier {

    private boolean active;
    private int threshold;
    private int count;
    private Semaphore barrier, mutex, activeMutex;

    public Barrier() {
        this.active = false;
        this.threshold = 9; // TODO: extend
        this.count = 0;
        this.barrier = new Semaphore(0);
        this.mutex = new Semaphore(1);
        this.activeMutex = new Semaphore(1);
    }

    /**
     * Wait for others to arrive (if barrier active)
     */
    public void sync() throws InterruptedException {
        this.activeMutex.P();

        if (this.active) {

            this.mutex.P();

            this.count++;
            System.out.println("inc count = " + this.count);

            if (this.count >= this.threshold) {

                this.free(this.count - 1);
                this.count = 0;

                this.mutex.V();

            } else {
                this.mutex.V();

                this.barrier.P();
            }
        }

        this.activeMutex.V();
    }

    /**
     * Activate barrier
     */
    public void on() {
        try {
            this.activeMutex.P();
            this.active = true;
            this.activeMutex.V();

        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    /**
     * Deactivate barrier
     */
    public void off() {
        try {
            this.activeMutex.P();

            if (this.active) {
                this.mutex.P();

                this.active = false;

                this.free(this.count);
                this.count = 0;

                this.mutex.V();
            }

            this.activeMutex.V();

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