// Creating and verifying a method for summing the first n integers. 

function sumN(n:nat) : nat 
{
    (n * (n + 1)) / 2 
}

method SumN(n: nat) returns (ans: nat)
    ensures ans >= 0
    ensures ans == sumN(n)

{
    ans := 0;
    for i:= 1 to n + 1 
        invariant 0 <= i <= n + 1
        invariant ans == sumN(i - 1)
    {
        ans := ans + i;
    }
    return ans;
}


method testSum()
{
    var sum10 := SumN(10);
    assert sum10 == 55; 
}