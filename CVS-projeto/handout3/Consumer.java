package handout3;

/*@
  predicate ConsumerInv(Consumer c;) =
  c.cq |-> ?cq
  &*& cq != null
  &*& [_]CQueueInv(cq);
@*/

//@ predicate frac(real f) = true;

public class Consumer implements Runnable {

    //@predicate pre() = ConsumerInv(this) &*& [_] System.out |-> ?o &*& o != null;
    //@predicate post() = emp;

    private CQueue cq;

    public Consumer(CQueue cq)
    //@ requires cq != null &*& frac(?f) &*& [f]CQueueInv(cq) &*& [_]System.out |-> ?o &*& o != null;
    //@ ensures ConsumerInv(this);
    {
        this.cq = cq;
    }

    public void run()
    //@ requires pre();
    //@ ensures post();
    {
        while (true)
        //@ invariant ConsumerInv(this) &*& [_]System.out |-> ?o &*& o != null;
        {
            int val = cq.dequeue();
            System.out.println("Consumer dequeued value: " + String.valueOf(val));
        }
    }
}
