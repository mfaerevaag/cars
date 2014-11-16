public class Alley {

    private int upCount, downCount;
    private Semaphore alleyFree, mutexUp, mutexDown;

    public Alley() {
        this.upCount = 0;
        this.downCount = 0;
        this.alleyFree = new Semaphore(1);
        this.mutexDown = new Semaphore(1);
        this.mutexUp = new Semaphore(1);
    }

    // Heavily inspired by the book p. 170
    public void enter(int no) throws InterruptedException {
        AlleyDirection newDir = (no < 5) ? AlleyDirection.UP : AlleyDirection.DOWN;

        if (newDir == AlleyDirection.UP) {
            this.mutexUp.P();

            this.upCount++;
            if (this.upCount == 1)
                this.alleyFree.P();

            this.mutexUp.V();

        } else {
            this.mutexDown.P();

            this.downCount++;
            if (this.downCount == 1)
                this.alleyFree.P();

            this.mutexDown.V();
        }
    }

    public void leave(int no) throws InterruptedException{
        AlleyDirection newDir = (no < 5) ? AlleyDirection.UP : AlleyDirection.DOWN;

        if (newDir == AlleyDirection.UP) {
            this.mutexUp.P();

            this.upCount--;
            if(this.upCount == 0)
                this.alleyFree.V();

            this.mutexUp.V();

        }else {
            this.mutexDown.P();

            this.downCount--;
            if(this.downCount == 0)
                this.alleyFree.V();

            this.mutexDown.V();
        }

    }
}