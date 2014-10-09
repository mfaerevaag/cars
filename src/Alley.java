enum Direction {
    UP, DOWN
}

public class Alley {

    int upCount, downCount;
    Semaphore alleyFree, mutexUp, mutexDown;

    public Alley() {
        this.upCount = 0;
        this.downCount = 0;
        this.alleyFree = new Semaphore(1);
        this.mutexDown = new Semaphore(1);
        this.mutexUp = new Semaphore(1);
    }

    // Heavily inspired by the book p. 170
    public void enter(int no) throws InterruptedException {
        Direction newDir = (no < 5) ? Direction.UP : Direction.DOWN;

        if (newDir == Direction.UP) {
            this.mutexUp.P();

            this.upCount++;
            if (this.upCount == 1)
                this.alleyFree.P();

            this.mutexUp.V();

        }else {
            this.mutexDown.P();

            this.downCount++;
            if (this.downCount == 1)
                this.alleyFree.P();

            this.mutexDown.V();
        }
    }

    public void leave(int no) throws InterruptedException{
        Direction newDir = (no < 5) ? Direction.UP : Direction.DOWN;

        if (newDir == Direction.UP) {
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
