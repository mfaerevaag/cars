import java.awt.Color;

public class Car extends Thread {

    private int baseSpeed = 100;     // Degree of slowness
    private int variation =  50;     // Percentage of base speed

    private int no;                  // Car number
    private Gate gate;               // Gate at startposition
    private Semaphore[][] semaMap;   // The entire map as semaphores

    /*
    Below you can choose between using semaphores og monitors.
    Remember to change constructor as well.
     */
    // private Alley alley;
    private AlleyMonitor alley;
    // private Barrier barrier;
    private BarrierMonitor barrier;

    private Pos startPos;            // Start position (provided by GUI)
    private Pos barPos;              // Barrier position (provided by GUI)
    private Color col;               // Car color
    private int speed;               // Current car speed
    private Pos curPos;              // Current position
    private Pos newPos;              // New position to go to
    private boolean moving;          // TODO: car maintenance wip

    private CarDisplayI cd;          // GUI part

    /**
     * Car constructor
     *
     * @param no - Car number
     * @param cd - Car Display
     * @param gate - Car's start gate
     * @param semaMap -  Car Controller's map of Seamphores
     * @param alley - Car Controller's Alley
     * @param barrier -  Car Controller's Alley
     */
    public Car(int no, CarDisplayI cd, Gate gate, Semaphore[][] semaMap, AlleyMonitor alley, BarrierMonitor barrier) {
        this.no = no;
        this.cd = cd;
        this.moving = false;

        this.gate = gate;
        this.semaMap = semaMap;
        this.alley = alley;
        this.barrier = barrier;

        this.startPos = cd.getStartPos(no);
        this.barPos = cd.getBarrierPos(no);  // For later use

        this.col = chooseColor();

        // do not change the special settings for car no. 0
        if (no == 0) {
            this.baseSpeed = 0;
            this.variation = 0;
            this.setPriority(Thread.MAX_PRIORITY);
        }
    }

    /**
     * Set speed of car (synchronized)
     * @param speed
     */
    public synchronized void setSpeed(int speed) {
        // not modify car no 0 or set negative speed
        if (this.no != 0 && this.speed >= 0)
            baseSpeed = speed;
        else
            cd.println("Illegal speed settings");
    }

    /**
     * Set variation of car's speed (synchronized)
     * @param var
     */
    public synchronized void setVariation(int var) {
        // not modify car no 0 and 0 <= var <= 100
        if (no != 0 && 0 <= var && var <= 100)
            variation = var;
        else
            cd.println("Illegal variation settings");
    }

    /**
     * Run car
     */
    public void run() {
        try {
            speed = chooseSpeed();
            curPos = startPos;
            cd.mark(curPos,col,no);

            while (true) {
                sleep(getSpeed());

                if (atGate()) {
                    gate.pass();
                    speed = chooseSpeed();
                }

                newPos = nextPos();

                if (atAlleyEnterance()) {
                    this.alley.enter(this.no);
                }
                else if (atAlleyExit()) {
                    this.alley.leave(this.no);
                }
                else if (atBarrier()) {
                    this.barrier.sync();
                }

                this.getSemaphoreFromPos(newPos).P();
                this.moving = true;

                //  Move to new position
                cd.clear(curPos);
                cd.mark(curPos, newPos, col, no);

                //TODO: remove in the end. A means to figure out the coordinate system
                // Pos testPos = new Pos(4,3);
                // if (inAlley())
                //     cd.mark(curPos, Color.cyan, no);

                sleep(getSpeed());

                cd.clear(curPos, newPos);
                cd.mark(newPos, col, no);

                this.getSemaphoreFromPos(curPos).V();
                curPos = newPos;
                this.moving = false;
            }

        } catch (InterruptedException e) {
            System.out.println("Car no. " + no + " interrupted");

            this.getSemaphoreFromPos(curPos).V();
            cd.clear(curPos);

            if (curPos != newPos && this.moving) {
                this.getSemaphoreFromPos(newPos).V();
                cd.clear(newPos); // TODO: fix yellow spots
            }

            if (inAlley()) {
                AlleyDirection dir = (no < 5) ? AlleyDirection.UP : AlleyDirection.DOWN;
                if (dir == AlleyDirection.UP)
                    this.alley.decrementUpCount();
                else
                    this.alley.decrementDownCount();
            }


        } catch (Exception e) {
            cd.println("Exception in Car no. " + no);
            System.err.println("Exception in Car no. " + no + ":" + e);
            e.printStackTrace();
        }
    }

    /*
    Utility method used by class it self
     */

    private Semaphore getSemaphoreFromPos(Pos pos) {
        return this.semaMap[pos.col][pos.row];
    }

    private int getSpeed() {
        // Slow down if requested
        final int slowfactor = 3;

        return speed * (cd.isSlow(this.curPos) ? slowfactor : 1);
    }

    private synchronized int chooseSpeed() {
        double factor = (1.0D+(Math.random()-0.5D)*2*variation/100);

        return (int) Math.round(factor * baseSpeed);
    }

    private Pos nextPos() {
        // Get my track from display
        return cd.nextPos(this.no, this.curPos);
    }

    private Color chooseColor() {
        // You can get any color, as longs as it's blue
        return Color.blue;
    }

    private boolean atGate() {
        return this.curPos.equals(this.startPos);
    }

    private boolean atBarrier() {
        boolean result;
        int col = this.no + 3;

        switch (this.no) {
            case 0:
                result = (this.curPos.col == 3 && this.curPos.row == 4);
                break;

            case 1:
            case 2:
            case 3:
            case 4:
                result = (this.curPos.col == col && this.curPos.row == 4);
                break;

            case 5:
            case 6:
            case 7:
            case 8:
                result = (this.curPos.col == col && this.curPos.row == 5);
                break;

            default:
                result = false;
                break;
        }

        return result;
    }

    private boolean atAlleyEnterance() {
        boolean result;

        switch (this.no) {
            case 0:
                result = false;
                break;

            case 1:
            case 2:
                result = (this.curPos.col == 1 && this.curPos.row == 8);
                break;

            case 3:
            case 4:
                result = (this.curPos.col == 3 && this.curPos.row == 9);
                break;

            case 5:
            case 6:
            case 7:
            case 8:
                result = (this.curPos.col == 0 && this.curPos.row == 0);
                break;

            default:
                result = false;
                break;
        }

        return result;
    }

    private boolean inAlley() {
        boolean result;

        if (this.curPos.col == 0 && (0 < this.curPos.row && this.curPos.row < 9))
            return true;

        switch (this.no) {
            case 0:
            case 1:
            case 2:
                result = false;
                break;

            case 3:
            case 4:
            case 5:
            case 6:
            case 7:
            case 8:
                result = (this.curPos.col < 3 && this.curPos.row == 9);
                break;

            default:
                result = false;
                break;
        }

        return result;
    }

    private boolean atAlleyExit() {
        boolean result;

        switch (this.no) {
            case 0:
                result = false;
                break;

            case 1:
            case 2:
            case 3:
            case 4:
                result = (this.curPos.col == 1 && this.curPos.row == 1);
                break;

            case 5:
            case 6:
            case 7:
            case 8:
                result = (this.curPos.col == 2 && this.curPos.row == 10);
                break;

            default:
                result = false;
                break;
        }

        return result;
    }

    /*
    Getters and setters
     */

    public Pos getStartPos() {
        return startPos;
    }
}
