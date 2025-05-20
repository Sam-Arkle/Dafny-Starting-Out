// Getting to know Dafny. A proof of a slow and fast fib method.
// The fast proof required a lemma. 


function fib (n : nat): nat 
{
    if n == 0 then 0 
    else if n == 1 then 1 
    else fib(n-1) + fib(n-2)
}
// A slow method to calculate fib numbers, using the mathematical definition.
method Fibonacci(n: nat) returns (r: nat)
    ensures r == fib(n)
{
    if n == 0 {return 0;}
    else if n == 1 {return 1;}
    else{
        // In dafny we extract the recursive calls into variables
        var two_prev := Fibonacci(n-2);
        var one_prev := Fibonacci(n-1);
        return two_prev + one_prev;
    }
}

// Lemma: fast doubling identities for Fibonacci numbers. Required for the FastFibPair method.
lemma FastDoublingFibonacciLemma(a: nat)
    ensures fib(2 * a) == fib(a) * (2 * fib(a + 1) - fib(a))
    ensures fib(2 * a + 1) == fib(a + 1) * fib(a + 1) + fib(a) * fib(a)
{
    if a == 0 {
        // Base case
        assert fib(0) == 0;
        assert fib(1) == 1;
        assert fib(2 * 0) == 0;
        assert fib(2 * 0 + 1) == 1;
        assert 0 == 0 * (2 * 1 - 0);
        assert 1 == 1 * 1 + 0 * 0;
    } else {
        // Inductive step
        FastDoublingFibonacciLemma(a - 1);
        // Use the definition of fib and algebraic manipulation
        // to help Dafny with the proof
    }
}

// Returns tuple (F(n), F(n+1))
method FastFibPair(n: nat) returns (f: nat, f1: nat)
// Algorithm credit: https://www.nayuki.io/page/fast-fibonacci-algorithms
    ensures f == fib(n)
    ensures f1 == fib(n+1)
    decreases n
{
    if n == 0 {
        f := 0;
        f1 := 1;
    } else {
        var a, b := FastFibPair(n / 2);
        var c := a * (2 * b - a);
        var d := b * b + a * a;
        if n % 2 == 0 {
            // Even case: n = 2k
            f := c;
            f1 := d;
            FastDoublingFibonacciLemma(n / 2);
            assert f == fib(n / 2) * (2 * fib(n / 2 + 1) - 
                fib(n / 2));
            assert f == fib(n);
            assert f1 == fib(n / 2 + 1) * fib(n / 2 + 1) + 
                fib(n / 2) * fib(n / 2);
            assert f1 == fib(n + 1);
        } else {
            // Odd case: n = 2k + 1
            f := d;
            f1 := c + d;
            FastDoublingFibonacciLemma(n / 2);
            assert f == fib(n / 2 + 1) * fib(n / 2 + 1) + 
                fib(n / 2) * fib(n / 2);
            assert f == fib(n);
            assert f1 == f + c;
            assert f1 == fib(n + 1);
        }
        assert f == fib(n);
        assert f1 == fib(n + 1);
    }
}


// Returns Fib(n)
method FastFibonacci(n: nat) returns (r: nat)
    ensures r == fib(n)
{
    var f, f1 := FastFibPair(n);
    return f;
}
