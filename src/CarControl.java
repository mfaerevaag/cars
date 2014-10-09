//Mandatory assignment
//Course 02158 Concurrent Programming, DTU, Fall 2014

//Hans Henrik Løvengreen    Oct 6, 2014

public class CarControl implements CarControlI {

    CarDisplayI cd;           // Reference to GUI
    Car[]  car;               // Cars
    Gate[] gate;              // Gates

    public CarControl(CarDisplayI cd) {
        this.cd = cd;
        this.car  = new  Car[9];
        this.gate = new Gate[9];

        for (int no = 0; no < 9; no++) {
            this.gate[no] = new Gate();
            this.car[no] = new Car(no,cd,gate[no]);
            this.car[no].start();
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
