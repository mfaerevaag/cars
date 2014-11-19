//Mandatory assignment
//Course 02158 Concurrent Programming, DTU, Fall 2014

//Hans Henrik Loevengreen    Oct 6, 2014

import java.awt.Color;

public class CarControl implements CarControlI {

    CarDisplayI cd;           // Reference to GUI
    Car[] cars;               // Cars
    Gate[] gate;              // Gates
    Alley alley;       // Alley
    Barrier barrier;   // Barrier

    static final int MAP_WIDTH = 12, MAP_HEIGHT = 11;

    Semaphore[][] semap;        // Map of the semap?

    public CarControl(CarDisplayI cd) {
        this.cd = cd;
        this.cars = new Car[9];
        this.gate = new Gate[9];
        this.alley = new Alley();
        this.barrier = new Barrier();
        this.semap = new Semaphore[MAP_WIDTH][MAP_HEIGHT];

        for (int x = 0; x < MAP_WIDTH; x++) {
            for(int y = 0; y < MAP_HEIGHT; y++) {
                // Mark all spots on the semap as free to use
                this.semap[x][y] = new Semaphore(1);
            }
        }

        for (int no = 0; no < 9; no++) {
            this.gate[no] = new Gate();
            this.cars[no] = new Car(no, cd, gate[no], this.semap, this.alley, this.barrier);
            this.cars[no].start();

            // Used to occupy the spot where the car is spawned
            Pos startPos = this.cars[no].getStartPos();
            this.semap[startPos.col][startPos.row] = new Semaphore(0);
        }

    }

    /* Car movement */

    public void startCar(int no) {
        this.gate[no].open();
    }

    public void stopCar(int no) {
        this.gate[no].close();
    }

    /* Barrier */

    public void barrierOn() {
        cd.println("Barrier on");
        this.barrier.on();
    }

    public void barrierOff() {
        cd.println("Barrier off");
        this.barrier.off();
    }


    public void barrierSet(int k) {
        this.barrier.setThreshold(k);
    }

    /* Car maintenance */

    public void removeCar(int no) {
        Car car = this.cars[no];

        if (car == null) {
            cd.println("Car #" + no + " already repairing");
            return;
        } else {
            cd.println("Car #" + no + " repairing...");
        }

        car.interrupt();

        this.cars[no] = null;
    }

    public void restoreCar(int no) {
        if (this.cars[no] != null) {
            cd.println("Car #" + no + " not repairing");
            return;
        } else {
            cd.println("Car #" + no + " restored");
        }

        this.cars[no] = new Car(no, cd, this.gate[no], this.semap, this.alley, this.barrier);

        this.cars[no].start();
    }

    /* Speed settings for testing purposes */

    public void setSpeed(int no, int speed) {
        cars[no].setSpeed(speed);
    }

    public void setVariation(int no, int var) {
        cars[no].setVariation(var);
    }

}

enum AlleyDirection {
    UP, DOWN;
}

class Alley {

    private int upCount, downCount;

    public Alley() {
        this.upCount = 0;
        this.downCount = 0;
    }

    public synchronized void enter(int no) throws InterruptedException {
        // get car direction
        AlleyDirection dir = (no < 5) ? AlleyDirection.UP : AlleyDirection.DOWN;

        if (dir == AlleyDirection.UP) {
            // Wait while there are cars going the opposite direction.
            while (this.downCount > 0)
                wait();

            this.upCount++;

        } else {
            while (this.upCount > 0)
                wait();

            this.downCount++;
        }
    }

    //please note the difference: notify() vs notifyAll()! There are 2 places where upwards bound cars wait, but only 1 where cars going down wait.
    public synchronized void leave(int no) {
        // get car direction
        AlleyDirection dir = (no < 5) ? AlleyDirection.UP : AlleyDirection.DOWN;

        if (dir == AlleyDirection.UP) {
            this.upCount--;

            if (this.upCount == 0) //Needs to be synchronized due to this check
                notify();

        } else {
            this.downCount--;

            if (this.downCount == 0)
                notifyAll();
        }
    }
}

enum BarrierSelector {
    INCOMING, LEAVING;
}

class Barrier {

    private boolean active;
    private int threshold, incomingCount, leavingCount;
    private BarrierSelector mode;

    private int increaseThreshold;

    public Barrier() {
        this.active = false;
        this.threshold = 9;
        this.incomingCount = 0;
        this.leavingCount = 0;
        this.increaseThreshold = -1;
        this.mode = BarrierSelector.INCOMING;
    }


    public synchronized void sync() {
        if (!this.active)
            return;

        // 1st - all cars must arrive ("incoming")

        // Wait until the barrier accepts incoming cars
        this.waitForMode(BarrierSelector.INCOMING);
        if(!this.active) //Check if barrier is still active when awoken
            return;

        this.incomingCount++;

        if(this.incomingCount == this.threshold) {
            this.mode = BarrierSelector.LEAVING;
            this.incomingCount = 0;

            notifyAll();
        }

        // 2nd - all cars must leave ("leaving")

        // Wait until the barrier accepts leaving cars
        this.waitForMode(BarrierSelector.LEAVING);
        if(!this.active) //Check if barrier is still active when awoken
            return;

        this.leavingCount++;

        if(this.leavingCount == this.threshold) {
            this.mode = BarrierSelector.INCOMING;
            this.leavingCount = 0;

            // This statement is part of task "EXTRA (E)" and used to implement a variable threshold value
            if(this.increaseThreshold > 1) {
                this.threshold = this.increaseThreshold;
                this.increaseThreshold = -1;
            }

            notifyAll();
        }
    }

    public synchronized void setThreshold(int k) {
        // Waiting for all cars that are flagged for leaving actually leaves.
        // This is always in the order of milliseconds, as cars cannot be sleeping in this period.
        // So we consider it instant.
        while (this.mode == BarrierSelector.LEAVING) {
            try {
                if(!this.active) {//Check if barrier is still active when awoken
                    this.threshold = k;
                    return;
                }
                else
                    wait();
            }
            catch (InterruptedException ex) { return; }
        }


        if (k < this.threshold) {
            if (k <= this.incomingCount) {

                this.mode = BarrierSelector.LEAVING;

                this.leavingCount = k - this.incomingCount;
                this.incomingCount = 0;
                this.threshold = k;

                notifyAll();

            }else {
                this.threshold = k;
            }
            // Check if it should release
        } else if (k > this.threshold) {
            this.increaseThreshold = k;

            while (this.mode == BarrierSelector.INCOMING) {
                try {
                    if(!this.active) { //Check if barrier is still active when awoken
                        this.threshold = k;
                        return;
                    }
                    else
                        wait();
                }
                catch (InterruptedException ex) { return; }
            }
        }
    }


    private void waitForMode(BarrierSelector selector) {
        // Wait until the barrier accepts the wanted type of cars
        while (this.mode != selector) {
            try {
                if(!this.active) //Check if barrier is still active when awoken
                    return;
                else
                    wait();
            }
            catch (InterruptedException ex) { return; }
        }
    }

    /**
     * Activate barrier
     */
    public synchronized void on() {
        if (! this.active) {
            this.active = true;
            this.incomingCount = 0;
            this.leavingCount = 0;
            this.increaseThreshold = -1;
        }
    }

    /**
     * Deactivate barrier
     */
    public synchronized void off() {
        this.active = false;
        this.leavingCount = 0;
        this.incomingCount = 0;
        this.mode = BarrierSelector.INCOMING;
        this.increaseThreshold = -1;
        this.notifyAll();
    }


}

class Car extends Thread {

    private enum State {
        INIT,
        WAITING_FOR_SPECIAL,
        WAITING_FOR_POS,
        MOVING,
        ARRIVED,
        FINISHED;
    }

    private int baseSpeed = 100;     // Degree of slowness
    private int variation =  50;     // Percentage of base speed

    private int no;                  // Car number
    private State state;             // State of car
    private Gate gate;               // Gate at startposition
    private Semaphore[][] semaMap;   // The entire map as semaphores

    /*
      Below you can choose between using semaphores og monitors.
      Remember to change constructor as well.
    */
    // private Alley alley;
    private Alley alley;
    // private Barrier barrier;
    private Barrier barrier;

    private Pos startPos;            // Start position (provided by GUI)
    private Pos barPos;              // Barrier position (provided by GUI)
    private Color col;               // Car color
    private int speed;               // Current car speed
    private Pos curPos;              // Current position
    private Pos newPos;              // New position to go

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
    public Car(int no, CarDisplayI cd, Gate gate, Semaphore[][] semaMap, Alley alley, Barrier barrier) {
        this.no = no;
        this.state = State.INIT;
        this.cd = cd;

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
        speed = chooseSpeed();

        // start at gate
        curPos = startPos;
        cd.mark(curPos, col, no);

        while (true) {
            try {
                this.state = State.INIT;

                sleep(getSpeed());

                // get next position
                newPos = nextPos();

                this.state = State.WAITING_FOR_SPECIAL;

                // check if at any significant position
                // cannot be at more than one at the same time
                if (atGate()) {
                    gate.pass();
                    speed = chooseSpeed();
                } else if (atAlleyEnterance()) {
                    this.alley.enter(this.no);
                } else if (atAlleyExit()) {
                    this.alley.leave(this.no);
                } else if (atBarrier()) {
                    this.barrier.sync();
                }

                this.state = State.WAITING_FOR_POS;

                // wait for new position
                this.getSemaphoreFromPos(newPos).P();

                this.state = State.MOVING;

                // move to new position
                cd.clear(curPos);
                cd.mark(curPos, newPos, col, no);

                sleep(getSpeed());

                this.state = State.ARRIVED;

                // clear old position
                cd.clear(curPos, newPos);
                cd.mark(newPos, col, no);

                this.state = State.FINISHED;

                // free old position
                this.getSemaphoreFromPos(curPos).V();
                curPos = newPos;

            } catch (InterruptedException e) {
                // if old position not signaled, signal both new and old
                this.repair();
            }
        }
    }

    /*
      Utility method used by class it self
    */

    private void repair() {
        // clean up depending on car's state
        switch (this.state) {
            case INIT:
                cd.clear(curPos);
                this.getSemaphoreFromPos(curPos).V();

                if (inAlley() || atAlleyExit())
                    this.alley.leave(this.no);

                break;

            case WAITING_FOR_SPECIAL:
                cd.clear(curPos);
                this.getSemaphoreFromPos(curPos).V();

                if (inAlley())
                    this.alley.leave(this.no);

                break;

            case WAITING_FOR_POS:
                cd.clear(curPos);
                this.getSemaphoreFromPos(curPos).V();

                if (inAlley() || atAlleyEnterance())
                    this.alley.leave(this.no);

                break;

            case MOVING:
                cd.clear(curPos, newPos);
                this.getSemaphoreFromPos(curPos).V();
                this.getSemaphoreFromPos(newPos).V();

                if (inAlley() || atAlleyEnterance())
                    this.alley.leave(this.no);

                break;

            case ARRIVED:
                cd.clear(newPos);
                this.getSemaphoreFromPos(newPos).V();
                this.getSemaphoreFromPos(curPos).V();

                if (inAlley() || atAlleyEnterance())
                    this.alley.leave(this.no);

                break;

            case FINISHED:
                cd.clear(newPos);
                this.getSemaphoreFromPos(newPos).V();

                if (inAlley() || atAlleyEnterance())
                    this.alley.leave(this.no);

                break;

            default:
                break;
        }

        // stop thread
        try {
            this.join();
        } catch (InterruptedException e) {
            cd.println("Exception in Car no. " + no);
            System.err.println("Exception in Car no. " + no + ":" + e);
            e.printStackTrace();
        }
    }

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

class Gate {

    Semaphore g = new Semaphore(0);
    Semaphore e = new Semaphore(1);
    boolean isopen = false;

    public void pass() throws InterruptedException {
        g.P();
        g.V();
    }

    public void open() {
        try { e.P(); } catch (InterruptedException e) {}
        if (!isopen) { g.V();  isopen = true; }
        e.V();
    }

    public void close() {
        try { e.P(); } catch (InterruptedException e) {}
        if (isopen) {
            try { g.P(); } catch (InterruptedException e) {}
            isopen = false;
        }
        e.V();
    }
}
