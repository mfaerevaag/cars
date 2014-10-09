//Mandatory assignment
//Course 02158 Concurrent Programming, DTU, Fall 2014

//Hans Henrik Løvengreen    Oct 6, 2014

public class CarControl implements CarControlI {

    CarDisplayI cd;           // Reference to GUI
    Car[] car;                // Cars
    Gate[] gate;              // Gates
    Alley alley;

    static final int MAP_WIDTH = 12, MAP_HEIGHT = 11;

    Semaphore[][] semap;        // Map of the semap?

    public CarControl(CarDisplayI cd) {
        this.cd = cd;
        this.car  = new Car[9];
        this.gate = new Gate[9];
        this.alley = new Alley(cd);
        this.semap = new Semaphore[MAP_WIDTH][MAP_HEIGHT];


        for(int x = 0; x < MAP_WIDTH; x++) {
            for(int y = 0; y < MAP_HEIGHT; y++) {
                // Mark all spots on the semap as free to use
                this.semap[x][y] = new Semaphore(1);
            }
        }

        for (int no = 0; no < 9; no++) {
            this.gate[no] = new Gate();
            this.car[no] = new Car(no,cd,gate[no], this.semap, this.alley);
            this.car[no].start();

            // Used to occupy the spot where the car is spawned
            Pos startPos = this.car[no].startpos;
            this.semap[startPos.col][startPos.row] = new Semaphore(0);
        }

    }

   public void startCar(int no) {
        this.gate[no].open();
    }

    public void stopCar(int no) {
        this.gate[no].close();
    }

    public void barrierOn() {
        cd.println("Barrier On not implemented in this version");
    }

    public void barrierOff() {
        cd.println("Barrier Off not implemented in this version");
    }

    public void barrierSet(int k) {
        cd.println("Barrier threshold setting not implemented in this version");
         // This sleep is for illustrating how blocking affects the GUI
        // Remove when feature is properly implemented.
        try {
            Thread.sleep(3000);
        } catch (InterruptedException e) {}
     }

    public void removeCar(int no) {
        cd.println("Remove Car not implemented in this version");
    }

    public void restoreCar(int no) {
        cd.println("Restore Car not implemented in this version");
    }

    /* Speed settings for testing purposes */

    public void setSpeed(int no, int speed) {
        car[no].setSpeed(speed);
    }

    public void setVariation(int no, int var) {
        car[no].setVariation(var);
    }

}
