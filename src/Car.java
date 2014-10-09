import java.awt.Color;

public class Car extends Thread {

    int basespeed = 100;             // Rather: degree of slowness
    int variation =  50;             // Percentage of base speed

    CarDisplayI cd;                  // GUI part

    int no;                          // Car number
    Pos startpos;                    // Startpositon (provided by GUI)
    Pos barpos;                      // Barrierpositon (provided by GUI)
    Color col;                       // Car  color
    Gate mygate;                     // Gate at startposition


    int speed;                       // Current car speed
    Pos curpos;                      // Current position
    Pos newpos;                      // New position to go to

    public Car(int no, CarDisplayI cd, Gate g) {
        this.no = no;
        this.cd = cd;

        this.mygate = g;
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

                //  Move to new position
                cd.clear(curpos);
                cd.mark(curpos,newpos,col,no);
                sleep(speed());
                cd.clear(curpos,newpos);
                cd.mark(newpos,col,no);

                curpos = newpos;
            }

        } catch (Exception e) {
            cd.println("Exception in Car no. " + no);
            System.err.println("Exception in Car no. " + no + ":" + e);
            e.printStackTrace();
        }
    }

}
