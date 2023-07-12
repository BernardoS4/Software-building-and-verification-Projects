package aula6;

public class Stack {

    Node head;

    public int pop()
    //@ requires NonEmptyStack(this);
    //@ ensures StackInv(this);
    {
        int v = head.getval();
        head = head.getnext();
        return v;
    }

    public boolean isEmpty()
    //@ requires StackInv(this);
    //@ ensures (result ? StackInv(this):NonEmptyStack(this));
    {
        return head == null;
    }

    public void push(int v)
    //@ requires StackInv(this);
    //@ ensures NonEmptyStack(this);
    {
        Node n = new Node();
        n.setval(v);
        n.setnext(head);
        head = n;
    }
}
