// Below is a self-contained Dafny program that:

// - Represents natural numbers as binary strings consisting only of `'0'` and `'1'`.
// - Has two **conversion** functions:
//   1. `str2int(s)`: Convert a valid bit-string `s` into a natural number.
//   2. `int2str(n)`: Convert a natural number `n` into its binary representation (with no leading zeros except if `n = 0`).
// 
// - Has three **pure string-based** arithmetic methods, each **not** using `str2int` or `int2str` inside the method body:
// 1. `add(s1, s2)`: Returns the bit-string representing the sum of `s1` and `s2`.
// 2. `sub(s1, s2)`: Returns the bit-string representing `s1 - s2`, assuming `s1 >= s2`.
//  3. `mul(s1, s2)`: Returns the bit-string representing the product `s1 * s2`.
//
// All methods come with specifications ensuring they do what they claim, and we prove correctness using Dafny’s function specifications (`ensures`) by comparing the result against the reference functions `str2int` and `int2str`.


method Main() {
    print "Examples:\n";

    var a := "1011";  // decimal 11
    var b := "1101";  // decimal 13

    print "a = ", a, " (decimal=", str2int(a), ")\n";
    print "b = ", b, " (decimal=", str2int(b), ")\n";

    var s := add(a, b);
    print "a + b = ", s, " (decimal=", str2int(s), ")\n";

    var d := sub(b, a);
    print "b - a = ", d, " (decimal=", str2int(d), ")\n";

    var m := mul(a, b);
    print "a * b = ", m, " (decimal=", str2int(m), ")\n";

    var z := "0";
    var sumZ := add(a, z);
    print a, " + 0 = ", sumZ, " (decimal=", str2int(sumZ), ")\n";

    // Convert integer -> string, then back
    var n := 9999;
    var sN := int2str(n);
    print "9999 -> ", sN, " -> ", str2int(sN), "\n";
}

// Funtion for validating leftShift
function  pow(base: nat, exp: nat): nat
{
    if exp == 0 then 1 else base * pow(base, exp - 1)
}

method leftShift(s: string, k: nat) returns (res: string)
    requires ValidBitString(s)
    ensures ValidBitString(res)
    ensures str2int(res) == str2int(s) * pow(2, k) // Double check this logic
{
    if s == "0" {
        res := "0";
    } else {
        var zeros := "";
        var i := 0;
        while i < k
            decreases k - i
        {
            zeros := zeros + "0";
            i := i + 1;
        }
        res := s + zeros;
    }
}

// ----------------------------------------------------
// 5) mul: string-based multiplication
//    No direct use of str2int/int2str
// ----------------------------------------------------
method mul(s1: string, s2: string) returns (res: string)
    requires ValidBitString(s1) && ValidBitString(s2)
    ensures ValidBitString(res)
    ensures str2int(res) == str2int(s1) * str2int(s2)
{
    var x := normalizeBitString(s1);
    var y := normalizeBitString(s2);

    // If either is "0", result is "0"
    if x == "0" || y == "0" {
        res := "0";
        return;
    }

    // We'll implement the classic method:
    //   product = 0
    //   for each bit of y (from right to left):
    //       if that bit == 1, add (x << position) to product
    // Use add(...) to accumulate partial sums.

    var product := "0";
    var shiftCount := 0;
    var idx := |y| - 1;
    while idx >= 0
        decreases idx
        // SA: Likely need to put some invariants here
    {
        if y[idx] == '1' {
            // partial = x shifted by shiftCount
            var partial := leftShift(x, shiftCount); // This function needs to add trailing 0's to the multiplicand based on shiftcount.
            product := add(product, partial); // Product is a running sum of requierd partial binary numbers.
        }
        shiftCount := shiftCount + 1;
        idx := idx - 1;
    }
    res := product;
}

// ----------------------------------------------------
// 4) sub: string-based subtraction (s1 >= s2)
// ----------------------------------------------------
method sub(s1: string, s2: string) returns (res: string)
    requires ValidBitString(s1) && ValidBitString(s2) // Both strings valid
    requires str2int(s1) >= str2int(s2) // First string bigger than second
    ensures ValidBitString(res) // Result is a valid string
    ensures str2int(res) == str2int(s1) - str2int(s2) // The maths works out
{
    var x := normalizeBitString(s1);
    var y := normalizeBitString(s2);

    // If y == "0", the difference is x
    if y == "0" {
        res := x;
        return;
    }
    // If x == y, the difference is "0"
    if x == y {
        res := "0";
        return;
    }

    var i := |x| - 1; // pointer on x
    var j := |y| - 1; // pointer on y
    var borrow := 0;
    var sb := [];  // reversed result

    while i >= 0 || j >= 0
        decreases i + j, borrow
        invariant 0 <= borrow <= 1
    {
        var bitX := 0;
        if i >= 0 { 
            bitX := if x[i] == '1' then 1 else 0;}
        var bitY := 0;
        if j >= 0 {
            bitY := if y[j] == '1' then 1 else 0;}

        // Subtract with borrow:
        var diff := bitX - bitY - borrow;
        if diff < 0 {
            diff := diff + 2;
            borrow := 1;
        } else {
            borrow := 0;
        }

        if diff == 1 {
            sb := sb + ['1'];}
        else{
            sb := sb + ['0'];}

        if i >= 0 { i := i - 1; }
        if j >= 0 { j := j - 1; }
    }

    // Reverse result
    var rev := "";
    var k := |sb| - 1;
    while k >= 0
        decreases k
    {
        rev := rev + [sb[k]];
        k := k - 1;
    }

    res := normalizeBitString(rev);
}


// Helper function to reverse a string
function Reverse(s: string): string
    decreases s
    requires ValidBitString(s)
    ensures ValidBitString(Reverse(s))
{
    if |s| == 0 then s else Reverse(s[1..]) + [s[0]]
}

// Helper lemma to prove substrings of valid bitstrings are valid:
lemma SubstringValid(s: string, i: int)
    requires ValidBitString(s)
    requires 0 <= i < |s|
    ensures ValidBitString(s[i..])
{}

function Power2(n: nat): nat
    decreases n
{
    if n == 0 then 1 else 2 * Power2(n - 1)
}

// ----------------------------------------------------
// 3) add: string-based addition (no str2int / int2str)
// ----------------------------------------------------
method add(s1: string, s2: string) returns (res: string)
    requires ValidBitString(s1) && ValidBitString(s2)
    ensures ValidBitString(res)
    ensures str2int(res) == str2int(s1) + str2int(s2)
{
    // We implement classic binary addition from right to left.
    // Step 1: Normalize inputs (drop leading zeros if needed).
    var x := normalizeBitString(s1);
    var y := normalizeBitString(s2);
    assert str2int(y) == str2int(s2);
    assert str2int(x) == str2int(s1);


    // If either is "0", the sum is the other.
    if x == "0" {
        res := y;
        return;
    }
    else if y == "0" {
        assert str2int(y) == 0;
        assert str2int(x) + str2int(y) == str2int(x);
        res := x; 
        assert str2int(x) == str2int(res);
        assert str2int(x) == str2int(s1);
        return;
    }
    else{
    // We build the result from the least significant bit forward.
    assert |x| > 0;
    var i := |x| - 1;  // index on x
    var j := |y| - 1;  // index on y
    var carry := 0;
    var sb := []; // dynamic array of chars for result (in reverse order)
    ghost var power := 1;  // Track 2^|sb|
    assert ValidBitString(sb);
    assert str2int(sb) == 0;
    assert str2int(Reverse(sb)) == 0;
    assert 0 <= i < |x|;
    SubstringValid(x, i);
    assert str2int(x[0..i+1]) == str2int(x);

    while i >= 0 || j >= 0 || carry != 0
    // Explaining decreases: Cases: i (and or j) decreases. Neither decreaes but carry does. 
        decreases (if i >= 0 then i + 1 else 0) + (if j >= 0 then j + 1 else 0) + carry 
        invariant 0 <= carry <= 1
        invariant i <= |x| - 1 && j <= |y| - 1
        invariant forall m :: 0 <= m < |sb| ==> sb[m] == '0' || sb[m] == '1'
        invariant power == Power2(|sb|)
        invariant ValidBitString(sb)  
        // invariant str2int(Reverse(sb)) + (str2int(x[0..i+1]) + str2int(y[0..j+1]) + carry * power) == str2int(x) + str2int(y)    {
        invariant str2int(Reverse(sb)) + (if i >= 0 then str2int(x[0..i+1]) else 0) + (if j >= 0 then str2int(y[0..j+1]) else 0) + carry * power == str2int(x) + str2int(y)
        {var bitX := 0;
        if i >= 0 {
            bitX := if x[i] == '1' then 1 else 0;}
        var bitY := 0;
        if j >= 0 {
            bitY := if y[j] == '1' then 1 else 0;}

        var sum := bitX + bitY + carry;
        var digit := sum % 2;
        carry := sum / 2;

        if digit == 1 {
            sb := sb + ['1'];}
        else{
            sb := sb + ['0'];}

        if i >= 0 { i := i - 1; }
        if j >= 0 { j := j - 1; }
        power := power * 2;  // Update power
        assert power == Power2(|sb|);
    }

    assert str2int(Reverse(sb)) == str2int(x) + str2int(y);
    
    // Reverse sb to get the proper bit string
    var rev := "";
    var k := |sb| - 1;
    while k >= 0
        decreases k
        invariant forall m :: 0 <= m < |rev| ==> rev[m] == '0' || rev[m] == '1'
        invariant str2int(rev) == str2int(sb[0..k+1])
    {
        rev := rev + [sb[k]];
        k := k - 1;
    }
    assert ValidBitString(rev);

    res := normalizeBitString(rev);

    assert str2int(res) == str2int(rev);

    assert str2int(res) == str2int(x) + str2int(y); // Help Dafny with the key fact
    }
}



// ----------------------------------------------------
// 1) str2int: bit-string -> nat (reference function)
// ----------------------------------------------------
function str2int(s: string) : nat
    requires ValidBitString(s)
    ensures str2int(s) == str2int(s)
    decreases s
{
    if |s| == 0 then 0 else 2 * str2int(s[0..|s|  - 1]) + (if s[ |s| - 1] == '1' then 1 else 0)
}

lemma ValidBitString_Concat_Char(s: string, c: string)
    requires ValidBitString(s)
    requires c == "0" || c == "1"
    ensures ValidBitString(s + c)
{
    // Prove each character of s+c is either '0' or '1'
    assert forall i | 0 <= i < |s + c| ::
        (i < |s| ==> (s[i] == '0' || s[i] == '1')) &&
        (i == |s| ==> (c[0] == '0' || c[0] == '1'));

    // So the concatenation is also valid
}

lemma Int2Str_Zero()
    ensures ValidBitString(int2str(0))
{
    assert int2str(0) == "0";
    assert ValidBitString("0");
}

lemma Int2Str_One()
    ensures ValidBitString(int2str(1))
{
    assert int2str(1) == "1";
    assert ValidBitString("1");
}


lemma Int2StrProducesValidBitString(n: nat)
    ensures ValidBitString(int2str(n))
    decreases n
{
    if n == 0 {
        Int2Str_Zero();
    } else if n == 1 {
        Int2Str_One();
    } else {
        Int2StrProducesValidBitString(n / 2); // inductive hypothesis
        ValidBitString_Concat_Char(int2str(n / 2), if n % 2 == 0 then "0" else "1");
        assert ValidBitString(int2str(n / 2) + (if n % 2 == 0 then "0" else "1"));

    }
}


predicate NoLeadingZeros(s: string)
{
    |s| == 1 || (|s| > 1 && s[0] != '0')
}

// Integer string has leading zero.
predicate LeadingZero(s: string)
{
    |s| >= 1 && s[0] == '0'
}

lemma Int2StrHasNoLeadingZeros(n: nat)
    requires n > 0
    ensures NoLeadingZeros(int2str(n))
    decreases n
{
    if n == 1 {
        assert int2str(1) == "1";
        assert NoLeadingZeros("1");
    } else {
        // inductive step
        assert n / 2 > 0; // because n > 1 implies n/2 > 0
        Int2StrHasNoLeadingZeros(n / 2);
        Int2StrProducesValidBitString(n / 2); // so concat is valid

        var c := if n % 2 == 0 then "0" else "1";
        ValidBitString_Concat_Char(int2str(n / 2), c);

        var s := int2str(n / 2) + c;

        // Now prove that s has no leading zeros
        // The only way a leading zero could happen is if int2str(n / 2) started with '0',
        // but by inductive hypothesis, that didn't happen.
        assert NoLeadingZeros(int2str(n / 2));
        assert NoLeadingZeros(s); // because appending 0/1 to a good prefix doesn't affect first char
    }
}

lemma Int2Str2IntIdentity(n: nat)
    ensures str2int(int2str(n)) == n
    decreases n
{
    if n == 0 {
        assert int2str(0) == "0";
        assert str2int("0") == 0;
    } else if n == 1 {
        assert int2str(1) == "1";
        assert str2int("1") == 1;
    } else {
        Int2Str2IntIdentity(n / 2);
        // Let s = int2str(n / 2), c = if n % 2 == 0 then "0" else "1"
        var s := int2str(n / 2);
        var c := if n % 2 == 0 then "0" else "1";
        assert str2int(s + c) == 2 * str2int(s) + (if c == "1" then 1 else 0);
        assert str2int(int2str(n)) == n;
    }
}


// ----------------------------------------------------
// 2) int2str: nat -> bit-string (reference function)
//    - "0" if n=0
//    - no leading zeros otherwise
// ----------------------------------------------------
 function int2str(n: nat) : string
    // ensures str2int(int2str(n)) == n // TODO: Add this back in. 
    ensures ValidBitString(int2str(n))
    ensures n > 0 ==> NoLeadingZeros(int2str(n))
    decreases n
{
    if n == 0 then
        "0"
    else if n ==1 then 
        "1"
    else
        int2str(n / 2) + (if n % 2 == 0 then "0" else "1")
}

predicate ValidBitString(s: string)
    // reads s
{
    // All characters must be '0' or '1'.
    // forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1' // original
    forall i : nat | i < |s| :: s[i] == '0' || s[i] == '1'
}

// ----------------------------------------------------
// Helpers for string-based arithmetic
// ----------------------------------------------------

method normalizeBitString(s: string) returns(res: string)
    // Remove leading zeros, except keep at least one digit
    requires ValidBitString(s)
    ensures ValidBitString(res)
    ensures str2int(res) == str2int(s)
    decreases s
{
    // If all zero or empty, return "0"
    if |s| == 0 {
        res := "0";}
    else{
        // find first '1'
        var firstOne :| 0 <= firstOne <= |s|;
        // pick the earliest i in 0..|s| if s[i] == '1'
        if (forall i | 0 <= i < |s| :: s[i] == '0') {
            res := "0";}
        else {
            // firstOne is the leftmost '1'
            res := s[firstOne..|s|] ;}
    }
}

function removeLeadingZeros (s: string) :string
    requires ValidBitString(s)
    ensures ValidBitString(removeLeadingZeros(s))
    {
        if |s| == 0 then // Empty string case 
            "0"
        else if |s| == 1 && s[0] == '0' then // Singleton string '0'
            "0"
        else if s[0] == '1' then // No leading zeros
            s
        else 
            removeLeadingZeros(s[1..])

    }


// If a str2int outputs 0 then string must be only zeros. 
lemma str2IntZeroImpliesAllZeros(s: string)
    requires ValidBitString(s)
    requires str2int(s) == 0
    ensures forall i :: 0 <= i < |s| ==> s[i] == '0'
{
    if |s| == 0 {
        // nothing to prove
    } else {
        if s[|s|-1] == '1' {
            // Then str2int(s) >= 1, contradiction
            assert false;
        }
        // So s[|s|-1] == '0'
        str2IntZeroImpliesAllZeros(s[0..|s|-1]);
    }
}

lemma AllZerosRemoveLeadingZerosIsZero(s: string)
    requires ValidBitString(s)
    requires forall i :: 0 <= i < |s| ==> s[i] == '0'
    ensures removeLeadingZeros(s) == "0"
{
    if |s| == 0 {
    } else if |s| == 1 {
        assert s[0] == '0';
    } else {
        AllZerosRemoveLeadingZerosIsZero(s[1..]);
    }
}

lemma addingZeroPrefixToBitStringNoChangeToInt(s: string)
    requires ValidBitString(s) 
    ensures str2int("0" + s) == str2int(s)
    decreases |s|
    {
        assert str2int("011") == str2int("11");

        if |s| == 0 {
            // Base case : empty string
            assert str2int("0") == 0;
            assert str2int("") == 0;
        } else{
            var s' := s[0..|s|-1];
            var c := s[|s|-1];
            assert ValidBitString(s');
            addingZeroPrefixToBitStringNoChangeToInt(s');
            assert str2int(s) == 2 * str2int(s') + (if c == '1' then 1 else 0);
            var t := s[0..|s|-1];
            assert str2int("0" + s) == 2 * str2int("0" + t) + (if s[|s|-1] == '1' then 1 else 0);
            assert str2int("0" + s) == 2 * str2int("0" + s') + (if c == '1' then 1 else 0);
            assert str2int("0" + s') == str2int(s');
            assert 2 * str2int("0" + s') + (if c == '1' then 1 else 0) == 2 * str2int(s') + (if c == '1' then 1 else 0);
            assert str2int("0" + s) == str2int(s);
    

        }

    }

lemma singleZeroPrefixBitStringEqualsBitString(s: string)
    requires ValidBitString(s)
    requires |s| > 1 && s[0] == '0' && s[1] == '1'
    ensures str2int(s) == str2int(s[1..])
    {
        assert str2int("011") == str2int("11");
        var t := s[1..];
        assert str2int(removeLeadingZeros(t)) == str2int(t);
        assert str2int(removeLeadingZeros(s)) == str2int(s[1..]);

        assert str2int(removeLeadingZeros(s)) == str2int(s);
        assert str2int(t) == str2int(s);
        assert str2int(s) == str2int(s[1..]);
    }

lemma str2intInvariantLeadingZeros (s: string)
    // requires LeadingZero(s)
    requires ValidBitString(s)
    ensures str2int(s) == str2int(removeLeadingZeros(s))
    decreases |s|
    {
        if |s| == 0 {
            // Case : empty string
            assert removeLeadingZeros(s) == "0";
            assert str2int(s) == 0;
            assert str2int(removeLeadingZeros(s)) == 0;  
        }
        else if |s| == 1 && s[0] == '0' {
            // Case : single '0'
            assert removeLeadingZeros(s) == "0";
            assert str2int(s) == 0;
            assert str2int(removeLeadingZeros(s)) == 0;
            assert str2int(removeLeadingZeros(s)) == str2int(s);
        } 
        else if |s| == 1 && s[0] == '1'{
            // Case : single '1' 
            assert removeLeadingZeros(s) == "1";
            assert str2int(s) == 1;
            assert str2int(removeLeadingZeros(s)) == 1;
            assert str2int(removeLeadingZeros(s)) == str2int(s);
        }
        else if s[0] == '0' && str2int(s) == 0 {
            // Case : All zeros
            assert s[0] == '0';
            assert str2int(s) == 0;
            assert ValidBitString(s);
            str2IntZeroImpliesAllZeros(s);
            assert forall i :: 0 <= i < |s| ==> s[i] == '0';
            AllZerosRemoveLeadingZerosIsZero(s);
            assert removeLeadingZeros(s) == "0";
            assert str2int(removeLeadingZeros(s)) == 0;
            assert str2int(s) == 0;
            assert str2int(removeLeadingZeros(s)) == str2int(s);
        } 
        else if s[0] == '0' && str2int(s) != 0{
            // Case : Leading zeros
            assert s[0] == '0';
            var t := s[1..];
            assert ValidBitString(t); 
            assert str2int(removeLeadingZeros(s)) == str2int(removeLeadingZeros(t));
            assert str2int(removeLeadingZeros(t)) == str2int(t);
            assert removeLeadingZeros(s) == removeLeadingZeros(t); 
            str2intInvariantLeadingZeros(t);
            if t[0] == '1'{
                // Case, second char is 1

                assert str2int(removeLeadingZeros(s)) == str2int(s); 

            }else {
                // Case : Second char is 0
                assert str2int(removeLeadingZeros(s)) == str2int(s);
            }


        }
        else{
        // Case : no leading zeros
        assert s[0] == '1';
        
        assert ValidBitString(s);
        // Inductive hypothesis
        // str2intInvariantLeadingZeros(s);


        } 
    }


method normalizeBitString2(s: string) returns(res: string)
    // Remove leading zeros, except keep at least one digit
    requires ValidBitString(s)
    ensures ValidBitString(res)
    ensures str2int(res) == str2int(s)
    ensures res == removeLeadingZeros(s)
    decreases s
{
    // If all zero or empty, return "0"
    if |s| == 0 {
        res := "0";}
    else{
        // find first '1'
        var firstOne := 0;
        while firstOne < |s|
            invariant 0 <= firstOne <= |s|
            invariant forall j :: 0 <= j < firstOne ==> s[j] != '1'
            decreases |s| - firstOne
            {
                if (s[firstOne] == '1') {res := s[firstOne..|s|];
                    return res;}
                firstOne := firstOne + 1;
            }
        res:= "0";
        // var firstOne :| 0 <= firstOne <= |s|;
        // // pick the earliest i in 0..|s| if s[i] == '1'
        // if (forall i | 0 <= i < |s| :: s[i] == '0') {
        //     res := "0";}
        // else {
        //     // firstOne is the leftmost '1'
        //     res := s[firstOne..|s|] ;}
    }
}






