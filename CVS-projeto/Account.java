public class Account {
    private int balance;

    public Account()
    // @ requires true;

    {
        balance = 0;
    }

    public void deposit(int amount)
    // @ requires balance |-> ?v;
    // @ ensures balance |-> v + amount;
    {
        balance += amount;
    }

    public void withdraw(int amount)
    // @ requires balance |-> ?v &*& v >= amount;
    // @ ensures balance |-> v - amount;
    {
        balance -= amount;
    }

    public int getBalance()
    // @ requires balance |-> ?v;
    // @ ensures balance |-> v &*& result == v;
    {
        return balance;
    }
}

class Main {
    public static void main(String[] args)
    // @ requires true;
    // @ ensures true;
    {
        Account a = new Account();
        int x = a.getBalance();
        int y = a.getBalance();
    }
}
