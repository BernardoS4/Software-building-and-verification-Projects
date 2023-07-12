package verifast;

public class Sum {

    /*
     * @ fixpoint int sum(list<int> vs) {
     * switch(vs) {
     * case nil: return 0;
     * case cons(h, t): return h + sum(t);
     * }
     * }
     * 
     * @
     */

    /*
     * @ lemma void sum_append(list<int> xs, list<int> ys)
     * requires true;
     * ensures sum(append(xs, ys)) == sum(xs) + sum(ys);
     * {
     * switch(xs) {
     * case nil:
     * case cons(h, t):
     * sum_append(t, ys);
     * }
     * }
     * 
     */

    public static int sum(int[] a)
    // @ requires array_slice(a, 0, a.length, ?vs);
    // @ ensures array_slice(a, 0, a.length, vs) &*& result == sum(vs);
    {
        int i = 0, total = 0;
        while (i < a.length)
        /*
         * @ invariant 0 <= i &*& i <= a.length &*&
         * total == sum(take(i, vs)) &*&
         * array_slice(a, 0, a.length, vs); @
         */
        {
            total += a[i];
            // @ take_one_more(i, vs);
            // @ sum_append(take(i, vs), cons(nth(i, vs), nil));
            i++;
        }
        return total;
    }
}
