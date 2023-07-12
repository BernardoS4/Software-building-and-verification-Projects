package handout3;

/*@
predicate Node(Node n; Node nxt, int v) = n.next |-> nxt &*& n.val |-> v;
@*/
public class Node {

    Node next;
    int val;

    public Node()
    //@ requires true;
    //@ ensures Node(this,null,0);
    {
        this.next = null;
        this.val = 0;
    }
  
    public Node getnext() 
    //@ requires Node(this,?n,?v);
    //@ ensures Node(this,n,v) &*& result == n;
    {
        return next;
    }

    public int getval() 
    //@ requires Node(this,?n,?v);
    //@ ensures Node(this,n,v) &*& result == v;
    {
        return val;
    }

    public void setnext(Node next) 
    //@ requires Node(this,_,?v);
    //@ ensures Node(this,next,v);
    {
        this.next = next;
    }

    public void setval(int val) 
    //@ requires Node(this,?n,_);
    //@ ensures Node(this,n,val);
    {
        this.val = val;
    }
}
