enum Direction {
    UP, DOWN
}

public class Alley {

    CarDisplayI cd;
    Semaphore sem;
    Direction dir;
    int count;

    int upCount, downCount;
    Semaphore alleyFree, mutexUp, mutexDown;

    public Alley(CarDisplayI cd) {
        this.cd = cd;
        this.sem = new Semaphore(1);
        this.count = 0;


        this.upCount = 0;
        this.downCount = 0;
        this.alleyFree = new Semaphore(1);
        this.mutexDown = new Semaphore(1);
        this.mutexUp = new Semaphore(1);
    }

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

            this.mutexDown.P();
//            this.alleyFree.P();
        }
//        this.sem.P();
//
//
//
//        if (this.isEmpty() || newDir == this.dir) {
//            cd.println("Entering no: " + no);
//            this.dir = newDir;
//            this.count++;
//        }
//        else {
//            cd.println("Could not enter no: " + no + " dir: " + this.dir.toString());
//        }
    }

    public void leave(int no) throws InterruptedException{
        cd.println("Leaving no: " + no);
        Direction newDir = (no < 5) ? Direction.UP : Direction.DOWN;

        if (newDir == Direction.UP) {
            this.mutexUp.P();

            this.upCount--;
            if(this.upCount == 0)
                this.alleyFree.V();
        }else {
            this.mutexDown.P();

            this.downCount--;
            if(this.downCount == 0)
                this.alleyFree.V();
//            this.alleyFree.V();
        }


//        this.sem.V();
//        this.count--;
    }

    private boolean isEmpty() {
        return this.count == 0;
    }
}
