// Working from https://dafny.org/latest/OnlineTutorial/guide

method Abs(x: int) returns (y: int)
    ensures 0 <= y
{
    if x < 0{
        return -x;
    }   else{
        return x;
    }
}

method MultipleReturns(x: int, y: int) returns (more: int, less: int)
    requires 0 < y 
    ensures less < x < more 
{
    more := x + y; 
    less := x - y;
}


// Exercise: Write a method max that returns the max of two ints. 
method Max(a: int, b: int) returns (c: int)
    ensures a <= c && b <= c
{
    if a <= b{
        c := b;
        assert c >= a;
    }else {
        c := a;
    }
}

method Testing()
{
    var v := Abs(3);
    assert 0<=v;
    var z, z' := MultipleReturns(2, 5);
    
}
// Exercise 1: Tst the max method
method Testing2()
{   
    var x := 2;
    var y := 4;
    var v := Max(x,y);
    assert v >= x ;
    // assert v == x; This asserts to false, because Dafny doesn't know what goes on in the max method while evaluating this method. We need to construct our methods differently if we wish to obtain this assertion.

    var q := Abs2(-2);
    assert q == 2;
}


// Exercise 2: Using a precondition change Abs to say it can only be called on negative values
method Abs2 (x: int) returns (y: int)
    requires x <= 0

    ensures 0 <= y
    ensures y == -x 

{
    return -x;
}

method Abs3 (x: int) returns (y: int)
    requires x == -1    
    ensures 0 <= y
    ensures 0 <= x ==> y == x
    ensures x < 0 ==> y == -x
{
    y:= x + 2;
}

method Abs4(x: int) returns (y: int)
  // Add a precondition here so that the method verifies.
  requires false
  // Don't change the postconditions.
  ensures 0 <= y
  ensures 0 <= x ==> y == x
  ensures x < 0 ==> y == -x
{
  y:= x + 1;
}

function absF(x: int): int
{
  if x < 0 then -x else x
}

// We can use functions directly in specifications:

method m()
{
  assert absF(3) == 3;
}


function maxF(a: int, b: int): int
{
  if a > b  then a else  b // Fill in an expression here.
}
method TestingMaxF() {
  // Add assertions to check max here.
  var v := maxF(2, 4);
  assert v == 4 ;

}

method Abs5(x: int) returns (y: int)
  // Use abs here, then confirm the method still verifies.
  ensures y == absF(x)
{
  // Then change this body to also use abs.
  y := absF(x);
}

//  This is going to be an expontentially slow function, however we can use it to show that faster versions match this mathematical defn!
function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)
{
  if n == 0 {return 0;}
  var i := 1;
  var a := 0;
  b := 1;
  while i < n
    invariant 0 < i <= n
    invariant a == fib(i - 1)
    invariant b == fib(i)
  {
    a, b := b, a + b;
    i := i + 1;
  }
}

method m2(n: nat)
{
  var i: int := 0;
  while i < n
    invariant 0 <= i <= n  // Change this. What happens?
  {
    i := i + 1;
  }
  assert i == n;
}

// Exerise 8: Simplify the compute Fib method above, introduce a variable c that succeeds b. 

method ComputeFib2(n: nat) returns (b: nat)
  ensures b == fib(n)  // Do not change this postcondition
{
  // Change the method body to instead use c as described.
  // You will need to change both the initialization and the loop.
  if n == 0 { return 0; }
  var i: int := 1;
  var c := 1;
  b := 1;
  while i < n
    invariant 0 < i <= n
    invariant c == fib(i + 1)
    invariant b == fib(i)
  {
    b, c := c, c + b;
    i := i + 1;
  }
}

// Ex 9

method ComputeFib3(n: nat) returns (b: nat)
  ensures b == fib(n)
{
  var i: int := 0;
  var a := 1;
  b := 0;
  while i < n
    // Fill in the invariants here.
    invariant 0 <= i <= n 
    invariant if i == 0 then a == 1 else a == fib(i - 1)
    // invariant i == 0 ==> a == 1
    // invariant i > 0 ==> a == fib(i - 1)
    invariant b == fib(i) 
  {
    a, b := b, a + b;
    i := i + 1;
  }
}

// Exercise 10:

method m3() 
{
  var i, n := 0, 20;
  while i != n
    invariant 0 <= i <= n
    decreases n - i
  {
    i := i + 1;
  }
}

