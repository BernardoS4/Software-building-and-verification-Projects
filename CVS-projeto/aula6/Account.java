package aula6;

public class Account {

    int balance;
    
    // the predicate holds of a memory configuration where the memory location this.balance contains the value b and b is non-negative

    /*@
    predicate AccountInv(int b) = this.balance |-> b &*& b >= 0;
    @*/
    public Account()
    //@ requires true;
    //@ ensures AccountInv(0);
    {
        balance = 0;
    }

    // uso do AccountInv(?b) -> diz que b e um parametro de output, que garante o seu uso no ensures como forma a referir o valor antigo do balance

    /*@
    predicate AccountInv(int b) = this.balance |-> b &*& b >= 0;
    @*/
    void deposit(int v)
    //@ requires AccountInv(?b) &*& v >= 0;
    //@ ensures AccountInv(b+v);
    {
        balance += v;
    }

    void withdraw(int v)
    //@ requires AccountInv(?b) &*& b >= v;
    //@ ensures AccountInv(b-v);
    {
        balance -= v;
    }
}