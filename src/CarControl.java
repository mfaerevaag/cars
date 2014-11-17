//Mandatory assignment
//Course 02158 Concurrent Programming, DTU, Fall 2014

//Hans Henrik Løvengreen    Oct 6, 2014

public class CarControl implements CarControlI {

    CarDisplayI cd;           // Reference to GUI
    Car[] cars;                // Cars
    Gate[] gate;              // Gates
    AlleyMonitor alley;       // Alley
    BarrierMonitor barrier;   // Barrier

    static final int MAP_WIDTH = 12, MAP_HEIGHT = 11;

    Semaphore[][] semap;        // Map of the semap?

    public CarControl(CarDisplayI cd) {
        this.cd = cd;
        this.cars = new Car[9];
        this.gate = new Gate[9];
        this.alley = new AlleyMonitor();
        this.barrier = new BarrierMonitor();
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
            cd.println("Car " + no + " already repairing");
            return;
        } else {
            cd.println("Car no. " + no + " repairing...");
        }

            car.interrupt();

        this.cars[no] = null;
    }

    public void restoreCar(int no) {
        if (this.cars[no] != null) {
            cd.println("Car " + no + " not repairing");
            return;
        } else {
            cd.println("Car no. " + no + " restored");
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
