enum Direction {
    UP, DOWN
}

public class Alley {

    CarDisplayI cd;
    Semaphore sem;
    Direction dir;
    int count;

    public Alley(CarDisplayI cd) {
        this.cd = cd;
        this.sem = new Semaphore(1);
        this.count = 0;
    }

    public void enter(int no) throws InterruptedException {
        Direction newDir = (no < 5) ? Direction.UP : Direction.DOWN;
        this.sem.P();

        if (this.isEmpty() || newDir == this.dir) {
            cd.println("Entering no: " + no);
            this.dir = newDir;
            this.count++;
        }
        else {
            cd.println("Could not enter no: " + no + " dir: " + this.dir.toString());
        }
    }

    public void leave(int no){
        cd.println("Leaving no: " + no);
        this.sem.V();
        this.count--;
    }

    private boolean isEmpty() {
        return this.count == 0;
    }
}
