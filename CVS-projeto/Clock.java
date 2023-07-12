

//@ predicate ClockInv(Clock c; int s) = c.seconds |-> s &*& s >= 0;

public class Clock {
    
    private int seconds;

    public void sync(Clock other)
    //@ requires ClockInv(this, ?s) &*& ClockInv(other, ?o);
    //@ ensures ClockInv(this, s) &*& ClockInv(other, s); 
    {
        other.seconds = this.seconds;
    }

    public int to(Clock other) 
    //@ requires ClockInv(this, ?s) &*& ClockInv(other, ?o);
    //@ ensures ClockInv(this, s) &*& ClockInv(other, o); 
    {
        return other.seconds - this.seconds;
    }

    public static void main(String[] args)
    //@ requires [_]System_out(?s) &*& s != null;
    //@ ensures true;
    {
        Clock c1 = new Clock();
        Clock c2 = new Clock();
        c1.sync(c2);
        System.out.println(c1.to(c1));
    }

}
