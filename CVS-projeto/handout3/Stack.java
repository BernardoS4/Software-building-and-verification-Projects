package handout3;


/*@
    predicate StackInv(Stack s; list<int> elems) = s.head |-> ?h &*& List(h, elems);

    predicate List(Node n; list<int> elems) = n == null ? (emp &*& elems == nil) : Node(n, ?nn, ?v) &*& List(nn, ?tail) &*& elems == cons(v, tail);

    predicate NonEmptyStack(Stack s; list<int> elems) = s.head |-> ?h &*& h != null &*& List(h, elems);
 @*/

public class Stack {

    Node head;

    public Stack() 
    //@ requires true;
    //@ ensures StackInv(this, ?l) &*& l == nil;
    {
        head = null;
    }

    public int pop()
    //@ requires NonEmptyStack(this, ?l);
    //@ ensures StackInv(this, tail(l));
    {
        int v = head.getval();
        head = head.getnext();
        return v;
    }
    
    public boolean isEmpty()
    //@ requires StackInv(this, ?l);
    //@ ensures StackInv(this, l) &*& result ? l == nil : l != nil;
    {
        //@ open StackInv(this, l);
        //@ open List(head, l);   
        return head == null;
    }


    public void push(int v)
    //@ requires StackInv(this, ?l);
    //@ ensures StackInv(this, cons(v, l));
    {
        Node n = new Node();
        n.setval(v);
        n.setnext(head);
        head = n;
    }

    public int peek() 
    //@ requires NonEmptyStack(this, ?l);
    //@ ensures NonEmptyStack(this, l) &*& result == head(l);
    {
        return head.getval();
    }

    public void flip() 
    //@ requires StackInv(this, ?l);
    //@ ensures StackInv(this, reverse(l));
    {
        Node n = null;
        //@open StackInv(this, l);
        while (head != null)
        //@ invariant head |-> ?h &*& List(h, ?l1) &*& List(n, ?l2) &*& l == append(reverse(l2), l1);
        {
            Node k = head.next;
            head.next = n;
            n = head;
            head = k;
            //@assert l1 == cons(?v,?tail0) &*& l == append(reverse(l2),cons(v,tail0));
            //@reverse_reverse(cons(v,tail0));
            //@reverse_append( reverse(cons(v,tail0)) , l2 );
            //@append_assoc(reverse(tail0),cons(v,nil),l2);
            //@reverse_append(reverse(tail0),cons(v,l2));
            //@reverse_reverse(tail0);
        }
        //@open List(h, l1);
        head = n;
        //@append_nil(reverse(l2));
    }
}


