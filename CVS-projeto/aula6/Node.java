package aula6;

// quando se usa nomeVar; -> input

/*@
predicate Node(Node n; Node nxt, int v) = n.next |-> nxt &*& n.val |-> v;
predicate List(Node n;) = n == null ? emp : Node(n,?h,_) &*& List(h);
@*/
public class Node {

    Node next;
    int val;

    public Node()
    //@ requires true;
    //@ ensures Node(this,null,0);
    {
        next = null;
        val = 0;
    }
  
    public Node getnext() {
        return next;
    }

    public int getval() {
        return val;
    }

    public void setnext(Node next) {
        this.next = next;
    }

    public void setval(int val) {
        this.val = val;
    }
}
