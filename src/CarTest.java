public class CarTest extends Thread {

    private CarTestingI cars;
    private int testNo;

    public CarTest(CarTestingI ct, int no) {
        this.cars = ct;
        this.testNo = no;
    }

    public void run() {
        int t; // for convenience when setting and logging threshold

        try {
            switch (testNo) {
                case 0:
                    log("reset everything");

                    cars.barrierSet(9);
                    cars.barrierOff();

                    cars.stopAll();
                    setSpeedAll(100);

                    break;

                case 1:
                    log("car collision");

                    cars.setSpeed(1, 50);
                    cars.setSpeed(8, 50);

                    cars.startAll();

                    break;

                /*
                Barrier tests
                 */

                case 2:
                case 3:
                case 4:
                case 5:
                case 6:
                case 7:
                case 8:
                case 9:
                    log("barrier (" + this.testNo + " threshold)");

                    for (int i = 1; i < this.testNo; i++) {
                        cars.startCar(i);
                    }

                    cars.barrierSet(this.testNo);
                    cars.barrierOn();

                    // waits a bit for the last one to more clearly demonstrate
                    // that the barrier only opens when all cars have arrived
                    Thread.sleep(1000);

                    cars.startCar(0);

                    break;

                /*
                Should set barrier to x, then after some, but before the barrier
                has been satisfied, increase it to y. The barrier should first wait
                for x, then after it has been satisfied, be set to y.
                 */

                case 10:
                    log("variable barrier threshold (low to high)");

                    setSpeedAll(100);

                    cars.startAll();
                    cars.startCar(0);
                    Thread.sleep(1000);

                    cars.barrierOn();

                    t = 4;
                    log("threshold " + t);
                    cars.barrierSet(t);

                    Thread.sleep(2000);

                    t = 9;
                    log("threshold " + t);
                    cars.barrierSet(t);

                    break;

                case 11:
                    log("variable barrier threshold (high to low)");

                    setSpeedAll(100);

                    cars.startAll();
                    cars.startCar(0);
                    Thread.sleep(1000);

                    cars.barrierOn();

                    t = 9;
                    log("threshold " + t);
                    cars.barrierSet(t);

                    Thread.sleep(7000);

                    t = 4;
                    log("threshold " + t);
                    cars.barrierSet(t);

                    break;

                /*
                Maintenance tests
                 */

                case 12:
                    log("simple remove and restore");

                    cars.startAll();

                    for (int i = 0; i < 3; i++) {
                        cars.removeCar(1);
                        cars.restoreCar(1);
                    }

                    break;

                case 13:
                    log("simple remove and restore");

                    cars.startAll();

                    for (int i = 0; i < 3; i++) {
                        Thread.sleep(1000);

                        cars.removeCar(1);

                        Thread.sleep(1000);

                        cars.restoreCar(1);
                    }

                    break;

                case 19:
                    // Demonstration of speed setting.
                    // Change speed to double of default values
                    log("doubling speeds");
                    for (int i = 1; i < 9; i++)
                        cars.setSpeed(i,50);
                    break;

                default:
                    log("not available");
                    return;
            }

            log("ended");

        } catch (Exception e) {
            System.err.println("Exception in test #" + this.testNo);
            e.printStackTrace();
        }
    }

    private void log(String msg) {
        cars.println(String.format("Test #%d: %s", this.testNo, msg));
    }

    private void setSpeedAll(int speed) {
        for (int i = 1; i < 9; i++)
            cars.setSpeed(i, speed);
    }

}
