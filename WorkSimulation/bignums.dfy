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
// function lessThan (s1: string, s2: string) : bool
//     requires ValidBitString(s1) && ValidBitString(s2) 
// {

// }

// Helper lemma for lexicographic order

lemma lastChar0 (s: string)
    requires ValidBitString(s)
    requires |s| > 0
    requires s[|s|-1] == '0'
    ensures str2int(s) == 2 * str2int(s[0..|s|-1]) + 0
    {    
    }

lemma lastChar1 (s: string)
    requires ValidBitString(s)
    requires |s| > 0
    requires s[|s|-1] == '1'
    ensures str2int(s) == 2 * str2int(s[0..|s|-1]) + 1
    {    
    }

method Main() {
    print "Examples:\n";

    var a := "1011";  // decimal 11
    var b := "1101";  // decimal 13

    print "a = ", a, " (decimal=", str2int(a), ")\n";
    print "b = ", b, " (decimal=", str2int(b), ")\n";

    var s := add(a, b);
    print "a + b = ", s, " (decimal=", str2int(s), ")\n";
    ghost var ar := "1101";
    calc {
        str2int("1101");
        ==//{}
        str2int(ar) ;
        == { Str2IntDef(ar);
        assert ValidBitString(ar);
        assert ValidBitString("110");
        assert str2int(ar) == 2 * str2int(ar[0..|ar|-1]) + (if ar[3] == '1' then 1 else 0);}
        2 * str2int(ar[0..|ar|-1]) + (if ar[3] == '1' then 1 else 0);
        == {assert ar[3] == '1'; }
        2 * str2int(ar[0..|ar|-1]) + 1;
        == { Str2IntDef(ar[0..|ar|-1]);}
        2 * (2 * str2int("11") + (if "110"[2] == '1' then 1 else 0)) + 1;
        == { assert "110"[2] == '0'; }
        2 * (2 * str2int("11") + 0) + 1;
        == { Str2IntDef("11"); }
        2 * (2 * (2 * str2int("1") + (if "11"[1] == '1' then 1 else 0))) + 1;
        == { assert "11"[1] == '1'; }
        2 * (2 * (2 * str2int("1") + 1)) + 1;
        == { Str2IntDef("1"); assert str2int("1") == 1;}
        2 * (2 * (2 * 1 + 1)) + 1;
        == { assert str2int("") == 0; assert "1"[0] == '1'; }
         13;
    }
    assert str2int("1101") == 13;
    ghost var bs := "1011";
    calc {
    str2int(bs);
    == { Str2IntDef(bs); assert ValidBitString(bs);}
    2 * str2int(bs[0..|bs|-1]) + 1;
    == { Str2IntDef(bs[0..|bs|-1]); }
    2 * (2 * str2int("10") + 1) + 1;
    == { Str2IntDef("10"); }
    2 * (2 * (2 * str2int("1") + 0) + 1) + 1;
    == { assert str2int("1") == 1; }
    2 * (2 * (2 * 1 + 0) + 1) + 1;
    == {}
    2 * (2 * 2 + 1) + 1;
    == {}
    2 * 5 + 1;
    == {}
    10 + 1;
    == {}
    11;
    }
    assert str2int("1011") == 11;
    assert str2int(b) >= str2int(a);
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
    // ensures str2int(res) == str2int(s) * Power2(k) // Double check this logic
{
    if s == "0" {
        res := "0";
        assert ValidBitString(res);
    } else {
        var zeros := "";
        var i := 0;
        while i < k
            decreases k - i
            invariant |zeros| > 0 ==> ValidBitString(zeros)
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
    var x := normalizeBitString2(s1);
    var y := normalizeBitString2(s2);

    // If either is "0", result is "0"
    if x == "0" || y == "0" {
        res := "0";
        assert ValidBitString(res);
        assert str2int(res) == str2int(s1) * str2int(s2);
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
        invariant ValidBitString(product)
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
    var x := normalizeBitString2(s1);
    var y := normalizeBitString2(s2);

    // If y == "0", the difference is x
    if str2int(y) == 0 {
        res := x;
        assert str2int(res) == str2int(s1) - str2int(s2);
        assert ValidBitString(res);
        return;
    }
    // If x == y, the difference is "0"
    if x == y {
        res := "0";
        assert ValidBitString(res);
        assert str2int(res) == str2int(s1) - str2int(s2);
        return;
    }

    var i := |x| - 1; // pointer on x
    assert i < |x|;
    var j := |y| - 1; // pointer on y
    assert j < |y|;
    var borrow := 0;
    var sb := [];  // reversed result

    ghost var RHS := str2int(x) - str2int(y);
    ghost var LHS := str2int(Reverse(sb)) + ((if i >= 0 then str2int(x[0..i+1]) else 0) - (if j >= 0 then str2int(y[0..j+1]) else 0 - borrow))  * Power2(|sb|);
    assert LHS == 0 +  str2int(x[0..i+1]) - str2int(y[0..j+1]) * 1;
    assert LHS == str2int(x[0..i+1]) - str2int(y[0..j+1]);
    assert |x| > 0;
    assert |y| > 0;
    bitStringSumEqualsWholeSubstringSum(x);
    SubstringValid(x);
    assert str2int(x[0..i+1]) == str2int(x) by {
      calc {
        str2int(x[0 .. i + 1]);
        =={assert x == x[0.. i + 1];}
        str2int(x);
      }
    }
    assert y == y[0..j+1];
    assert str2int(y[0..j+1]) == str2int(y);
    assert LHS == str2int(x) - str2int(y);
    assert LHS == RHS;

    while i >= 0 || j >= 0
        // decreases remaining, borrow
        decreases (if i >= 0 then i + 1 else 0) + (if j >= 0 then j + 1 else 0) , borrow 
        invariant 0 <= borrow <= 1
        invariant ValidBitString(sb)
        invariant i <= |x| - 1 && j <= |y| - 1
        invariant LHS == str2int(x) - str2int(y)
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
        
        LHS := str2int(Reverse(sb)) + ((if i >= 0 then str2int(x[0..i+1]) else 0) - (if j >= 0 then str2int(y[0..j+1]) else 0 - borrow))  * Power2(|sb|);
    }

    assert (if i >= 0 then str2int(x[0..i+1]) else 0) == 0;
    assert (if j >= 0 then str2int(y[0..j+1]) else 0) == 0;
    assert borrow == 0;
    assert str2int(Reverse(sb)) == str2int(x) - str2int(y);

    // Reverse result
    var rev := "";
    var k := |sb| - 1;
    while k >= 0
        decreases k
        invariant ValidBitString(rev)
    {
        rev := rev + [sb[k]];
        k := k - 1;
    }

    res := normalizeBitString2(rev);
    assert str2int(res) == str2int(s1) - str2int(s2);
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
lemma SubstringValid(s: string)
    requires ValidBitString(s)
    ensures forall i : nat :: i < |s| ==> ValidBitString(s[i..])
{}

// Lemma to prove whole substring of string is equal to string.
lemma substringEqual(s: string)
    requires ValidBitString(s)
    ensures forall i :: 0 <= i <= |s| ==> s[0..i] + s[i..|s|] == s
    {
            assert s == s[0..|s|]; 
    }

lemma bitStringSumEqualsWholeSubstringSum(s : string)
    requires ValidBitString(s)
    ensures forall i :: 0 <= i <= |s| ==> str2int(s[0..i] + s[i..|s|]) == str2int(s)
    {
        substringEqual(s); 

        assert forall i :: 0 <= i <= |s| ==> 
            s[0..i] + s[i..|s|] == s &&
            str2int(s[0..i] + s[i..|s|]) == str2int(s);

    }

function Power2(n: nat): nat
    decreases n
{
    if n == 0 then 1 else 2 * Power2(n - 1)
}
lemma Power2Shift(n: nat)
  ensures Power2(n + 1) == 2 * Power2(n)
{
  // By unfolding Power2:
  //   Power2(n+1) = 2 * Power2(n).
}

// ----------------------------------------------------
// 3) add: string-based addition (no str2int / int2str)
// ----------------------------------------------------
lemma Str2IntPrepend(c: char, s: string)
    requires ValidBitString(s) && (c == '0' || c == '1')
    ensures str2int([c] + s) == (if c == '1' then 1 else 0) * Power2(|s|) + str2int(s)
{
    if |s| == 0 {
        // Base case: str2int([c]) == (if c == '1' then 1 else 0)
        // Power2(0) == 1, str2int("") == 0
        // (if c == '1' then 1 else 0) * 1 + 0 == (if c == '1' then 1 else 0)
    } else {
        // Inductive step using str2int definition:
        // str2int([c]+s) = 2 * str2int(([c]+s)[0..|([c]+s)|-1]) + (if ([c]+s)[|([c]+s)|-1] == '1' then 1 else 0)
        // ([c]+s)[0..|([c]+s)|-1] is [c] + s[0..|s|-1]
        // ([c]+s)[|([c]+s)|-1] is s[|s|-1]
        Str2IntPrepend(c, s[0..|s|-1]); // Inductive hypothesis
        calc {
            str2int([c] + s);
        ==  // Definition of str2int
            2 * str2int(([c] + s)[0..|s|]) + (if s[|s|-1] == '1' then 1 else 0);
        ==  // String slicing
            assert (([c] + s)[0..|s|]) == [c] + s[0..|s|-1];
            2 * str2int([c] + s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0);
        ==  // Inductive Hypothesis: Str2IntPrepend(c, s[0..|s|-1])
            2 * ((if c == '1' then 1 else 0) * Power2(|s|-1) + str2int(s[0..|s|-1])) + (if s[|s|-1] == '1' then 1 else 0);
        ==  // Distribute 2* and apply Power2Shift
            (if c == '1' then 1 else 0) * Power2(|s|) + (2 * str2int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0));
        ==  { Str2IntDef(s); } // Fold str2int(s)
            (if c == '1' then 1 else 0) * Power2(|s|) + str2int(s);
        }
    }
}
lemma Str2IntAppend(s: string, c: char)
    requires ValidBitString(s)
    requires c == '0' || c == '1'
    ensures str2int(s + [c]) == 2 * str2int(s) + (if c == '1' then 1 else 0)
{
    // By definition of str2int:
    if |s| == 0 {
        // str2int("" + [c]) == str2int([c])
        // str2int([c]) == (if c == '1' then 1 else 0)
        // 2 * 0 + (if c == '1' then 1 else 0) == (if c == '1' then 1 else 0)
    } else {
        // Inductive step:
        Str2IntAppend(s[0..|s|-1], c);
        calc {
            str2int(s + [c]);
        == { Str2IntDef(s + [c]); }
            2 * str2int((s + [c])[0..|s|]) + (if (s + [c])[|s|] == '1' then 1 else 0);
        == { assert (s + [c])[0..|s|] == s; }
            2 * str2int(s) + (if c == '1' then 1 else 0);
        }
    }
}


method add(s1: string, s2: string) returns (res: string)
    requires ValidBitString(s1) && ValidBitString(s2)
    ensures ValidBitString(res)
    ensures str2int(res) == str2int(s1) + str2int(s2)
{
    // We implement classic binary addition from right to left.
    // Step 1: Normalize inputs (drop leading zeros if needed).
    var x := normalizeBitString2(s1);
    var y := normalizeBitString2(s2);
    assert str2int(y) == str2int(s2);
    assert str2int(x) == str2int(s1);


    // If either is "0", the sum is the other.
    if str2int(x) == 0 {
        res := y;
        assert str2int(s1) + str2int(s2) == str2int(res);
        return;
    }
    else if str2int(y) == 0 {
        res := x; 
        assert str2int(s1) + str2int(s2) == str2int(res);
        return; 
    }
    else{
    // We build the result from the least significant bit forward.
    assert |x| > 0;
    assert |y| > 0;
    var i := |x| - 1;  // index on x
    // var xSub := x[0..i+1];
    var j := |y| - 1;  // index on y
    var carry := 0;
    var sb := []; // dynamic array of chars for result (in reverse order)
    ghost var power : nat := 1;  // Track 2^|sb|
    ghost var RHS := str2int(x) + str2int(y);
    ghost var LHS :=  str2int(Reverse(sb)) + (if i >= 0 then str2int(x[0..i+1]) else 0)
         + (if j >= 0 then str2int(y[0..j+1]) else 0)
         + carry * power;
    ghost var new_LHS := LHS;
    ghost var old_LHS := LHS;
    ghost var old_xi_val := str2int(x[0..i+1]);
    ghost var new_xi_val := str2int(x[0..i+1]);
    ghost var old_yj_val := str2int(y[0..j+1]);
    ghost var new_yj_val := str2int(y[0..j+1]);
    ghost var old_sb := sb;

    
    assert ValidBitString(sb);
    assert x[0..i+1] == x;
    assert y[0..j+1] == y;
    assert str2int(x[0..i+1]) == str2int(x);
    assert str2int(y[0..j+1]) == str2int(y);
    assert LHS == RHS;
    // assert str2int(x[0..i+1]) + str2int(y[0..j+1]) == str2int(x) + str2int(y);

    while i >= 0 || j >= 0 || carry != 0
    // Explaining decreases: Cases: i (and or j) decreases. Neither decreaes but carry does. 
        decreases (if i >= 0 then i + 1 else 0) + (if j >= 0 then j + 1 else 0) + carry 
        invariant 0 <= carry <= 1
        invariant i <= |x| - 1 && j <= |y| - 1
        // invariant forall m :: 0 <= m < |sb| ==> sb[m] == '0' || sb[m] == '1'
        // invariant power == Power2(|sb|)
        invariant ValidBitString(sb)  
        invariant LHS == RHS
        invariant LHS == new_LHS
        invariant old_LHS == new_LHS
        // invariant str2int(Reverse(sb)) + (str2int(x[0..i+1]) + str2int(y[0..j+1]) + carry * power) == str2int(x) + str2int(y)    {
        // invariant str2int(Reverse(sb)) + (if i >= 0 then str2int(x[0..i+1]) else 0) + (if j >= 0 then str2int(y[0..j+1]) else 0) + carry * power == str2int(x) + str2int(y)
        // invariant str2int(Reverse(sb)) + (if i >= 0 then str2int(x[0..i+1]) else 0) + (if j >= 0 then str2int(y[0..j+1]) else 0) + carry * power == str2int(x) + str2int(y)
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

        if i >= 0 { i := i - 1; 
        new_xi_val := str2int(x[0..i+1]);}
        if j >= 0 { j := j - 1;
        new_yj_val := str2int(y[0..j+1]); }
        power := power * 2;  // Update power
        Power2Shift(power);

        new_LHS :=  str2int(Reverse(sb)) + (if i >= 0 then str2int(x[0..i+1]) else 0)
         + (if j >= 0 then str2int(y[0..j+1]) else 0)
         + carry * power;
        // assert old_LHS == new_LHS;
         if i >= 0 && x[i] == '0'{
            if j >= 0 && y[j] == '0'{
                if carry == 0{
                    calc{
                        new_LHS;
                        == //{Carry = 0}
                        str2int(Reverse(sb)) + (if i >= 0 then str2int(x[0..i+1]) else 0)
                            + (if j >= 0 then str2int(y[0..j+1]) else 0)
                            + 0;
                        ==  //{ we know i and j >= 0}
                             str2int(Reverse(sb)) + str2int(x[0..i+1]) 
                            +  str2int(y[0..j+1]);
                        == //{Plugging in updated values}
                        str2int(Reverse(sb)) + new_xi_val + new_yj_val;
                        == 

                        old_LHS;
                    }
                    assert old_LHS == new_LHS;
                }else{// carry == 1
                    calc{
                        new_LHS == old_LHS;
                    }
                }
            }
         }
        //  if i == |x | - 2  && j == |y| - 2{
        //     // First stage
        //     if carry == 0{
        //         calc{
        //             new_LHS;
        //             == { assert carry * power == 0 ;}
        //             str2int(Reverse(sb)) + (if i >= 0 then str2int(x[0..i+1]) else 0)
        //             + (if j >= 0 then str2int(y[0..j+1]) else 0)
        //             + 0;
        //             == //{ we know i and j >= 0}
        //             str2int(Reverse(sb)) + str2int(x[0..i+1]) 
        //             +  str2int(y[0..j+1]);

        //             == 


        //             LHS;
        //         }
        //     }
        //     calc {
            
        //     }
        //  }
            assert old_LHS == new_LHS;
            old_sb := sb;
            old_xi_val := new_xi_val;
            old_yj_val := new_yj_val;
            old_LHS := new_LHS;
        // assert new_LHS == LHS;
        // assert power == Power2(|sb|);
        // assert  (if i >= 0 then str2int(x[0..i+1]) else 0)
        //  + (if j >= 0 then str2int(y[0..j+1]) else 0)
        //   <= RHS;
        
         
    }
    assert (if i >= 0 then str2int(x[0..i+1]) else 0) == 0;
    assert (if j >= 0 then str2int(y[0..j+1]) else 0) == 0;
    assert carry * power == 0;
    assert new_LHS == LHS;
    assert LHS == str2int(Reverse(sb));
    assert str2int(Reverse(sb)) == RHS;
    assert str2int(Reverse(sb)) == str2int(x) + str2int(y);
    
    // Reverse sb to get the proper bit string
    var rev := "";
    var k := |sb| - 1;
    while k >= 0
        decreases k
        invariant ValidBitString(rev)
        // invariant str2int(rev) == str2int(sb[0..k+1])
    {
        rev := rev + [sb[k]];
        k := k - 1;
    }
    assert ValidBitString(rev);
    // assert str2int(rev) == str2int(s1) + str2int(s2);

    res := normalizeBitString2(rev);

    assert str2int(res) == str2int(rev);

    assert str2int(res) == str2int(s1) + str2int(s2); // Help Dafny with the key fact
    }
}

ghost function IntValue(s: string, last_idx: int): int
    requires ValidBitString(s)
    requires -1 <= last_idx < |s| // last_idx is the index of the LSB of the prefix considered
{
    if last_idx < 0 then 0
    else str2int(s[0..last_idx+1]) // Value of s[0...last_idx]
}

// Lemma for IntValue
// lemma Lemma_IntValue_Step(s: string, k: int)
//     requires ValidBitString(s) && 0 <= k < |s|
//     requires s[k] == '0' || s[k] == '1' // and other ValidBitString properties for substrings
//     ensures IntValue(s, k) == IntValue(s, k-1) * 2 + (if s[k] == '1' then 1 else 0)
//     {

//     }

// ghost function ReversedSeqCharToInt(s: seq<char>): int
//     requires forall c :: c in s ==> c == '0' || c == '1'
// {
//     str2int(Reverse(string(s))) // Assuming string(s) is valid if s only contains '0'/'1'
// }

// ----------------------------------------------------
// 1) str2int: bit-string -> nat (reference function)
// ----------------------------------------------------
function str2int(s: string) : nat
    requires ValidBitString(s)
    ensures str2int(s) == str2int(s)
    ensures ValidBitString(int2str(str2int(s)))
    // ensures |s| > 0 ==>  int2str(str2int(s)) == s // TODO: Add this in
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
    // reads s // could change this to a char array and then it'll get better access...
{
    // All characters must be '0' or '1'.
    // forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1' // original
    forall i : nat | i < |s| :: s[i] == '0' || s[i] == '1'
}


method StringToCharArray(s: string) returns (a: array<char>)
    ensures a.Length == |s|
    ensures forall i :: 0 <= i < |s| ==> a[i] == s[i]
{
    a := new char[|s|];
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> a[j] == s[j]
        decreases |s| - i
    {
        a[i] := s[i];
        i := i + 1;
    }
}
method CharArrayToString(a: array<char>) returns (s: string)
    ensures |s| == a.Length
    ensures forall i :: 0 <= i < a.Length ==> s[i] == a[i]
{
    s := "";
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant |s| == i
        invariant forall j :: 0 <= j < i ==> s[j] == a[j]
        decreases a.Length - i
    {
        s := s + [a[i]];
        i := i + 1;
    }
}


// lemma validCharArrayiffValidBitString()

// ----------------------------------------------------
// Helpers for string-based arithmetic
// ----------------------------------------------------

// method normalizeBitString(s: string) returns(res: string)
//     // Remove leading zeros, except keep at least one digit
//     requires ValidBitString(s)
//     ensures ValidBitString(res)
//     ensures str2int(res) == str2int(s)
//     decreases s
// {
//     // If all zero or empty, return "0"
//     if |s| == 0 {
//         res := "0";}
//     else{
//         // find first '1'
//         var firstOne :| 0 <= firstOne <= |s|;
//         // pick the earliest i in 0..|s| if s[i] == '1'
//         if (forall i | 0 <= i < |s| :: s[i] == '0') {
//             res := "0";}
//         else {
//             // firstOne is the leftmost '1'
//             res := s[firstOne..|s|] ;}
//     }
// }

method getFinalBit(s: string) returns (bit: char) 
    requires ValidBitString(s)
    requires |s| > 0
    ensures bit == s[|s|-1]
    {
        bit := s[|s|-1];
    }

// lemma buildingBitString (s : string)
//     requires ValidBitString(s)


lemma Str2IntDef(s: string)
requires ValidBitString(s) && |s| >= 1
ensures  str2int(s)
        == 2 * str2int(s[0..|s| - 1])
        + (if s[|s| - 1] == '1' then 1 else 0)
{
// by unfolding str2int’s definition
}  

lemma LemmaZeroPrefix(t: string)
    requires ValidBitString(t)
    ensures str2int("0" + t) == str2int(t)
{
    if |t| == 0 {
        // Base case: "0" has the same value as an empty string (both 0)
    } else {
        LemmaZeroPrefix(t[0..|t| -1]); // Inductive step
        // Calculate using the definition of str2int
       calc {
        // 1) unfold str2int on "0"+t
        str2int("0" + t);
          == { Str2IntDef("0" + t) ;}
        2 * str2int(("0" + t)[0..|t|])
          + (if t[|t|-1] == '1' then 1 else 0);

        // 2) slice‐rewrite: drop the last char of "0"+t
          == { assert ("0" + t)[0..|t|] == "0" + t[0..|t|-1]; }
        2 * str2int("0" + t[0..|t|-1])
          + (if t[|t|-1] == '1' then 1 else 0);

        // 3) by the inductive hypothesis on t[0..|t|-1]
          == { LemmaZeroPrefix(t[0..|t|-1]); }
        2 * str2int(t[0..|t|-1])
          + (if t[|t|-1] == '1' then 1 else 0);

        // 4) fold str2int on t
          == { Str2IntDef(t) ;}
        str2int(t);
      }
    }
}

lemma LemmaDropLeadingZero(s: string)
    requires ValidBitString(s) 
    requires |s| > 0 ==> s[0] == '0'
    ensures |s| > 0 ==> str2int(s) == str2int(s[1..])
{
    // Decompose s = "0" + t where t = s[1..]
    // Apply LemmaZeroPrefix to t, which proves str2int("0" + t) == str2int(t)
    if |s| > 0{
    assert "0" + s[1..] == s;
    LemmaZeroPrefix(s[1..]);}
}

method normalizeBitString2(s: string) returns(res: string)
    // Remove leading zeros, except keep at least one digit
    requires ValidBitString(s)
    ensures ValidBitString(res)
    ensures str2int(res) == str2int(s)
    // ensures res == removeLeadingZeros(s)
    decreases s
{
    // If empty, return "0"
    if |s| == 0 {
        res := "0";}
    else{
        // find first '1'
        var firstOne := 0;
        assert str2int(s[firstOne..]) == str2int(s);
        assert |s| > 0;
        while firstOne < |s| 
            invariant 0 <= firstOne <= |s|
            invariant forall j :: 0 <= j < firstOne ==> s[j] == '0'
            decreases |s| - firstOne
            invariant str2int(s[firstOne..]) == str2int(s)
            {   
                
                if (s[firstOne] == '1') {
                    res := s[firstOne.. ];
                    return res;}
                
                    LemmaDropLeadingZero(s[firstOne..]);
                    assert str2int(s[firstOne..]) == str2int(s);
                    firstOne := firstOne + 1;
                     
                    }
        res:= "0"; // No '1' in string, return '0'.
    }
}