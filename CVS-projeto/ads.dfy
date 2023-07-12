class Set {

    var store: array<int>;
    var nelems: int;

    predicate RepInv()
        reads store, `store, `nelems
    {
        0 < store.Length
        && 0 <= nelems <= store.Length
        && forall i,j :: 0 <= i < j < nelems ==> store[i] !=store[j]
    }

    // creation operation given a max capacity
    constructor(n: int)
        requires 0 < n
        ensures RepInv()
    {
        store := new int[n];
        nelems := 0;
    }

    // adds a new element to the set if the set capacity permits
    method add(v: int)
        requires RepInv()
        requires size() < maxSize()
        ensures RepInv()
        modifies store, `nelems
    {
        var f: int := find(v);
        if f < 0 {
            store[nelems] := v;
            nelems := nelems + 1;
        }
    }

    // checks if a given element is in the set
    method contains(v: int) returns (b: bool)
        requires RepInv()
        ensures RepInv()
        ensures b <==> exists j :: (0 <= j < nelems) && v == store[j];
    {
        var i := find(v);
        return i ≥ 0;
    }

    // returns the number of elements in the set
    function size() : int
        requires RepInv()
        ensures RepInv()
        reads store, `store, `nelems
    {
        nelems
    }

    // returns the maximum number of elements in the set
    function maxSize() : int
        requires RepInv()
        ensures RepInv()
        reads store, `store, `nelems
    { store.Length }

    method find(x: int) returns (r: int)
        requires RepInv()
        ensures RepInv()
        ensures r < 0 ==> forall j :: (0 <= j < nelems) ==> x != store[j]
        ensures r >= 0 ==> r < nelems && store[r] == x;
    {
        var i: int := 0;
        while (i < nelems)
            decreases nelems-i
            invariant 0 <= i <= nelems;
            invariant forall j :: (0 <= j < i) ==> x != store[j]
        {
            if (store[i] == x) { return i; }
            i := i + 1;
        }
        return -1;
    }
}

//NOTAS

// reads store -> apenas le o apontador

// reads `store -> le o conteudo apontado por store