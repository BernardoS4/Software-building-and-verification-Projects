method sort(a: array<char>)
  ensures sorted(a,a.Length)
  modifies a


predicate sorted(a: array<char>, n: int)
  requires 0 ≤ n ≤ a.Length
  reads a
{ forall i, j • (0 ≤ i < j < n) ==> a[i] ≤ a[j] }


method fillK(a: array<int>, n: int, k: int, c: int) returns (b: bool)
  requires c <= n <= a.Length
  requires 0 <= c
  ensures (forall i: int :: 0 <= i < c ==> a[i] == k) <==> b
{
  var i:=0;
  b:=true;
  while i < c
    invariant 0 <= i <= c
    invariant ((forall index: int :: 0 <= index < i ==> a[index] == k) <==> b)
  {
    if(a[i] != k) {
      b := false;
    }
    i:= i + 1;
  }
}

method isSameString(a: array<char>, b: array<char>) returns (c: bool)
  requires a.Length == b.Length
  ensures c <==> (forall i: int :: 0 <= i < a.Length ==> a[i] == b[i])
{
  var i:=0;
  c:=true;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant ((forall index: int :: 0 <= index < i ==> a[index] == b[index]) <==> c)
  {
    if(a[i] != b[i]) {
      c := false;
    }
    i:= i + 1;
  }
}

method containsSubString(a: array<char>, b: array<char>) returns (pos: int)
