import java.awt.Color;
import java.io.InterruptedIOException;

public class Car extends Thread {

    int basespeed = 100;             // Rather: degree of slowness
    int variation =  50;             // Percentage of base speed

    CarDisplayI cd;                  // GUI part

    int no;                          // Car number
    Pos startpos;                    // Startpositon (provided by GUI)
    Pos barpos;                      // Barrierpositon (provided by GUI)
    Color col;                       // Car  color
    Gate mygate;                     // Gate at startposition
//    Alley alley;
    AlleyMonitor alley;
//    Barrier barrier;
    BarrierMonitor barrier;
    Semaphore[][] semap; // The entire map as semaphores

    int speed;                       // Current car speed
    Pos curpos;                      // Current position
    Pos newpos;                      // New position to go to

    public Car(int no, CarDisplayI cd, Gate g, Semaphore[][] semap, AlleyMonitor alley, BarrierMonitor barrier) {
        this.no = no;
        this.cd = cd;

        this.mygate = g;
        this.alley = alley;
        this.barrier = barrier;
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

    public synchronized void remove() {
        this.interrupt();
    }

    public synchronized void restore() {
        // TODO
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

    boolean atBarrier(Pos pos) {
        boolean result;
        int col = this.no + 3;

        switch (this.no) {
        case 0:
            result = (pos.col == 3 && pos.row == 4);
            break;

        case 1:
        case 2:
        case 3:
        case 4:
            result = (pos.col == col && pos.row == 4);
            break;

        case 5:
        case 6:
        case 7:
        case 8:
            result = (pos.col == col && pos.row == 5);
            break;

        default:
            result = false;
            break;
        }

        return result;
    }

    boolean atAlleyEnterance(Pos pos) {
        boolean result;

        switch (this.no) {
            case 0:
                result = false;
                break;

            case 1:
            case 2:
                result = (pos.col == 1 && pos.row == 8);
                break;

            case 3:
            case 4:
                result = (pos.col == 3 && pos.row == 9);
                break;

            case 5:
            case 6:
            case 7:
            case 8:
                result = (pos.col == 0 && pos.row == 0);
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

                if (atAlleyEnterance(curpos)) {
                    this.alley.enter(this.no);
                }
                else if (atAlleyExit(curpos)) {
                    this.alley.leave(this.no);
                }
                else if (atBarrier(curpos)) {
                    this.barrier.sync();
                }

                this.getSemaphoreFromPos(newpos).P();

                //  Move to new position
                cd.clear(curpos);
                cd.mark(curpos,newpos,col,no);

                //TODO: remove in the end. A means to figure out the coordinate system
                // Pos testPos = new Pos(4,3);
                // cd.mark(testPos, Color.cyan,0);


                sleep(speed());

                cd.clear(curpos,newpos);
                cd.mark(newpos,col,no);
                this.getSemaphoreFromPos(curpos).V();
                curpos = newpos;
            }

        } catch (InterruptedException e) {
            System.out.println("Car no. " + no + " interrupted");

        } catch (Exception e) {
            cd.println("Exception in Car no. " + no);
            System.err.println("Exception in Car no. " + no + ":" + e);
            e.printStackTrace();
        }
    }

}
