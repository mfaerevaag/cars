public class AlleyMonitor {

    private int upCount, downCount;

    public AlleyMonitor() {
        this.upCount = 0;
        this.downCount = 0;
    }

    public synchronized void enter(int carNo) {
        AlleyDirection dir = (carNo < 5) ? AlleyDirection.UP : AlleyDirection.DOWN;

        if (dir == AlleyDirection.UP) {
            // Wait while there are cars going the opposite direction.
            while (this.downCount > 0) {
                try { wait(); }
                catch (InterruptedException ex) { return; }
            }

            this.upCount++;
        } else {
            while (this.upCount > 0) {
                try { wait(); }
                catch (InterruptedException ex) { return; }
            }

            this.downCount++;
        }
    }

    //TODO: note the difference: notify() vs notifyAll()! There are 2 places where upwards bound cars wait, but only 1 where cars going down wait.
    public synchronized void leave(int carNo) {
        AlleyDirection dir = (carNo < 5) ? AlleyDirection.UP : AlleyDirection.DOWN;

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

    public void decrementUpCount() {
        this.upCount--;
    }

    public void decrementDownCount() {
        this.downCount--;
    }
}