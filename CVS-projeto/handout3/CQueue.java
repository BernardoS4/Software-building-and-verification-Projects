package handout3;

import java.util.concurrent.locks.*;

/*@

    lemma void append_nnil(list<int> l1, list<int> l2)
        requires l2 != nil;
        ensures append(l1,l2) != nil;
    {
        switch (l1) {
            case nil:
            case cons(x,xs):
        }
    }

    lemma void reverse_nnil(list<int> xs)
        requires xs != nil;
        ensures reverse(xs) != nil;
    {
        switch(xs) {
            case nil:
            case cons(h, t):
                append_nnil(reverse(t),cons(h,nil));
        }
    }
    
	predicate_ctor CQueue_shared_state(CQueue cq) ()= 
		cq.left |-> ?left
        &*& cq.right |-> ?right
		&*& left != null &*& right != null
        &*& StackInv(left,_) &*& StackInv(right,_);
		
	predicate_ctor CQueue_nonempty_state(CQueue cq) ()=
		cq.left |-> ?left
        &*& cq.right |-> ?right
		&*& left != null &*& right != null
        &*& StackInv(left, ?l1) &*& StackInv(right, ?l2)
        &*& (l1 != nil || l2 != nil);
        		
	predicate CQueueInv(CQueue cq;) = 
		cq.mon |-> ?l
		&*& l != null
		&*& lck(l,1,CQueue_shared_state(cq))
		&*& cq.nonEmpty |-> ?cqNonEmpty
		&*& cqNonEmpty != null
		&*& cond(cqNonEmpty,CQueue_shared_state(cq),CQueue_nonempty_state(cq));

@*/

public class CQueue {

    ReentrantLock mon;
    Condition nonEmpty;
    Stack left;
    Stack right;

    public CQueue()
    //@ requires true;
    //@ ensures CQueueInv(this);
    {
        left = new Stack();
        right = new Stack();
        //@ close CQueue_shared_state(this)();
        //@ close enter_lck(1, CQueue_shared_state(this));
        mon = new ReentrantLock();
        //@ close set_cond(CQueue_shared_state(this), CQueue_nonempty_state(this));
        nonEmpty = mon.newCondition();
        //@ assert lck(?mon, 1, CQueue_shared_state(this));
        //@ close CQueueInv(this);
    }

    
    public void enqueue(int elem)
    //@ requires [?f]CQueueInv(this);
    //@ ensures [f]CQueueInv(this);
    {
        mon.lock();
        //@ open CQueue_shared_state(this)();
        //@ close StackInv(this.left,?l1);
        left.push(elem);
        //@ close CQueue_nonempty_state(this)();
        nonEmpty.signal();
        mon.unlock();
    }


    private void flush()
    //@ requires left |-> ?l &*& NonEmptyStack(l, ?l1) &*& l != null &*& right |-> ?r &*& r != null &*& StackInv(r, ?l2) &*& l1 !=nil &*& l2 ==nil;
    //@ ensures right |-> l &*& NonEmptyStack(l,reverse(l1)) &*& left |-> r &*& StackInv(r,l2);
    {
        //@ open NonEmptyStack(left, l1);
        left.flip();
        //@reverse_nnil(l1);
        //@ open StackInv(left, reverse(l1));
        //@ open List(left.head,reverse(l1));
        //@ close NonEmptyStack(left, reverse(l1));
        Stack temp = right;
        right = left;
        //@ close NonEmptyStack(right, reverse(l1));
        left = temp;
    }

    public boolean isEmpty()
    //@ requires CQueueInv(this);
    //@ ensures CQueueInv(this);
    {
        mon.lock();
        //@ open CQueue_shared_state(this)();
        boolean res = left.isEmpty() && right.isEmpty();
        //@ close StackInv(left, _);
        //@ close StackInv(right, _);
        //@ close CQueue_shared_state(this)();
        mon.unlock();
        return res;
    }

    public int dequeue()
    //@ requires [?f]CQueueInv(this);
    //@ ensures [f]CQueueInv(this);
    {
        //@ open CQueueInv(this);
        mon.lock();
        //@ open CQueue_shared_state(this)();
	
        while(right.isEmpty() && left.isEmpty()) 
        //@ invariant [f]this.nonEmpty |-> ?ne &*& ne != null &*& this.left |-> ?left &*& this.right |-> ?r &*& left != null &*& r != null &*& StackInv(left, ?l1) &*& StackInv(r, ?l2) &*& [f]cond(ne,CQueue_shared_state(this),CQueue_nonempty_state(this));
        {
            //@ close CQueue_shared_state(this)();
            try {
                nonEmpty.await();
            } catch (InterruptedException e) {}
            //@ open CQueue_nonempty_state(this)();
        }

	    int result;
        if (right.isEmpty()) {
            //@ open StackInv(left, l1);
            //@ open List(left.head, l1);
            flush();
            //@reverse_nnil(l1);
	        result = right.pop();	
        } else {
            //@ open StackInv(right, l2);
            //@ open List(right.head, l2);
        	result = right.pop();	
        }
        //@ close CQueue_shared_state(this)();
        mon.unlock();
        return result;
    }
}
