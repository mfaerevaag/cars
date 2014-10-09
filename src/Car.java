import java.awt.Color;

public class Car extends Thread {

    int basespeed = 100;             // Rather: degree of slowness
    int variation =  50;             // Percentage of base speed

    CarDisplayI cd;                  // GUI part

    int no;                          // Car number
    Pos startpos;                    // Startpositon (provided by GUI)
    Pos barpos;                      // Barrierpositon (provided by GUI)
    Color col;                       // Car  color
    Gate mygate;                     // Gate at startposition
    Alley alley;
    Semaphore[][] semap; // The entire map as semaphores

    int speed;                       // Current car speed
    Pos curpos;                      // Current position
    Pos newpos;                      // New position to go to

    public Car(int no, CarDisplayI cd, Gate g, Semaphore[][] semap, Alley alley) {
        this.no = no;
        this.cd = cd;

        this.mygate = g;
        this.alley = alley;
        this.semap = semap;
        this.startpos = cd.getStartPos(no);
        this.barpos = cd.getBarrierPos(no);  // For later use

        this.col = chooseColor();

        // do not change the special settings for car no. 0
        if (no == 0) {
            this.basespeed = 0;
            this.variation = 0;
            this.setPriority(Thread.MAX_PRIORITY);
        }
    }

    public synchronized void setSpeed(int speed) {
        // not modify car no 0 or set negative speed
        if (this.no != 0 && this.speed >= 0)
            basespeed = speed;
        else
            cd.println("Illegal speed settings");
    }

    public synchronized void setVariation(int var) {
        // not modify car no 0 and 0 <= var <= 100
        if (no != 0 && 0 <= var && var <= 100)
            variation = var;
        else
            cd.println("Illegal variation settings");
    }

    synchronized int chooseSpeed() {
        double factor = (1.0D+(Math.random()-0.5D)*2*variation/100);

        return (int) Math.round(factor * basespeed);
    }

    private int speed() {
        // Slow down if requested
        final int slowfactor = 3;

        return speed * (cd.isSlow(this.curpos) ? slowfactor : 1);
    }

    private Semaphore getSemaphoreFromPos(Pos pos) {
        return this.semap[pos.col][pos.row];
    }

    Color chooseColor() {
        // You can get any color, as longs as it's blue
        return Color.blue;
    }

    Pos nextPos(Pos pos) {
        // Get my track from display
        return cd.nextPos(no, pos);
    }

    boolean atGate(Pos pos) {
        return pos.equals(startpos);
    }

    boolean atAlleyEnterance(Pos pos) {
        boolean result;

        switch (this.no) {
        case 0:
            result = false;
            break;

        case 1:
        case 2:
            result = (pos.col == 2 && pos.row == 8);
            break;

        case 3:
        case 4:
            result = (pos.col == 4 && pos.row == 9);
            break;

        case 5:
        case 6:
        case 7:
        case 8:
            result = (pos.col == 1 && pos.row == 0);
            break;

        default:
            result = false;
            break;
        }

        return result;
    }

    boolean atAlleyExit(Pos pos) {
        boolean result;

        switch (this.no) {
        case 0:
            result = false;
            break;

        case 1:
        case 2:
        case 3:
        case 4:
            result = (pos.col == 1 && pos.row == 1);
            break;

        case 5:
        case 6:
        case 7:
        case 8:
            result = (pos.col == 2 && pos.row == 10);
            break;

        default:
            result = false;
            break;
        }

        return result;
    }

    public void run() {
        try {

            speed = chooseSpeed();
            curpos = startpos;
            cd.mark(curpos,col,no);

            while (true) {
                sleep(speed());

                if (atGate(curpos)) {
                    mygate.pass();
                    speed = chooseSpeed();
                }

                newpos = nextPos(curpos);

                // TODO: check if newpos is free.
                cd.println("[" + no + "] nextpos: " + this.getSemaphoreFromPos(newpos).toString());
                this.getSemaphoreFromPos(newpos).P();

                if (atAlleyEnterance(curpos))
                    this.alley.enter(this.no);
                else if (atAlleyExit(curpos))
                    this.alley.leave(this.no);

                //  Move to new position
                cd.clear(curpos);
                cd.mark(curpos,newpos,col,no);
                sleep(speed());

                cd.clear(curpos,newpos);
                cd.mark(newpos,col,no);

                this.getSemaphoreFromPos(curpos).V();

                curpos = newpos;
            }

        } catch (Exception e) {
            cd.println("Exception in Car no. " + no);
            System.err.println("Exception in Car no. " + no + ":" + e);
            e.printStackTrace();
        }
    }

}
