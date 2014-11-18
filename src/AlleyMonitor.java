public class AlleyMonitor {

    private int upCount, downCount;

    public AlleyMonitor() {
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

    //TODO: note the difference: notify() vs notifyAll()! There are 2 places where upwards bound cars wait, but only 1 where cars going down wait.
    public synchronized void leave(int no) {
        // get car direction
        AlleyDirection dir = (no < 5) ? AlleyDirection.UP : AlleyDirection.DOWN;

        if (dir == AlleyDirection.UP) {
            this.upCount--;

            if (this.upCount == 0) //Needs to be synchronized due to this check
                notifyAll();

        } else {
            this.downCount--;

            if (this.downCount == 0)
                notifyAll();
        }
    }
}