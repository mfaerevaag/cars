public class AlleyMonitor {

    private int upCount, downCount;

    public AlleyMonitor() {
        this.upCount = 0;
        this.downCount = 0;
    }

    public synchronized void enter(int carNo) {
        Direction dir = (carNo < 5) ? Direction.UP : Direction.DOWN;

        if (dir == Direction.UP) {
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
        Direction dir = (carNo < 5) ? Direction.UP : Direction.DOWN;

        if (dir == Direction.UP) {
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