package handout3;

public class Client {
    
    public static void main(String args[])
    //@ requires [_]System.out |-> ?s &*& s != null;
    //@ ensures true;
    {
        CQueue q = new CQueue();
        int numClients = 100;
        //@ assert CQueueInv(q);
        //@ close frac(1);
        for (int i = 0; i < numClients; i++)
        //@ invariant 0 <= i &*& i <= 100 &*& frac(?f) &*& [f]CQueueInv(q) &*& [_]System.out |-> ?o &*& o != null;
        {
        //@ open frac(f);
        //@ close frac(f/2);
        new Thread(new Producer(q, i)).start();
        //@ close frac(f/4);
        new Thread(new Consumer(q)).start();
        //@ close frac(f/4);
        }
    }
}
