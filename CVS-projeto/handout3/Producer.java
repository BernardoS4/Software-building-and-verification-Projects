package handout3;

/*@
  predicate ProducerInv(Producer p;) =
  p.cq |-> ?cq
  &*& cq != null
  &*& [_]CQueueInv(cq)
  &*& p.val |-> ?val;
@*/

  class Producer implements Runnable {
    //@predicate pre() = ProducerInv(this) &*& [_] System.out |-> ?s &*& s != null;
    //@predicate post() = emp;

    private CQueue cq;
    private int val;

    public Producer(CQueue cq, int val)
    //@ requires cq != null &*& frac(?f) &*& [f]CQueueInv(cq) &*& [_]System.out |-> ?s &*& s != null;
    //@ ensures ProducerInv(this);
    {
        this.cq = cq;
        this.val = val;
    }

    public void run()
    //@ requires pre();
    //@ ensures post();
    {
        while (true)
        //@ invariant ProducerInv(this) &*& [_]System.out |-> ?s &*& s != null;
        {
            cq.enqueue(val);
            System.out.println("Producer enqueued value: " + String.valueOf(val));
        }
    }
}
