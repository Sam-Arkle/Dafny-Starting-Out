
method Find(a: array<int>, key: int) returns (index: int)
  ensures 0 <= index ==> index < a.Length && a[index] == key
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key  // This ensures that if we give a negative index then k isn't in the array 
{
  // Can you write code that satisfies the postcondition?
  // Hint: you can do it with one statement.
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall k :: 0 <= k < index ==> a[k] != key
  {
    if a[index] == key {return;}
    index := index + 1;
  }
  index := -1;
}


// Exercise 11
/*
Write a method that takes an integer array, which it requires to have at least one element,
 and returns an index to the maximum of the array’s elements. Annotate the method with pre- and 
 postconditions that state the intent of the method, and annotate its body with loop invariant 
 to verify it.
*/

// method FindMax(a: array<int>) returns (i: int)
//   // Annotate this method with pre- and postconditions
//   // that ensure it behaves as described.
//   requires a.Length > 0
//   ensures 0 <= i < a.Length && forall k :: 0 <= k < a.Length ==> a[i] >= a[k]
// {
//   // Fill in the body that calculates the INDEX of the maximum.
//   var j := 1;
//   var max_index := 0;
//   while j < a.Length
//     invariant 1 <= j <= a.Length
//     invariant 0 <= max_index <= a.Length
//     invariant forall k :: 0 <= k < j ==> a[k] <= a[max_index]
//     {
//       if a[j] > a[max_index] { max_index := j;}
//       j := j + 1 ;     
//     }
//     i := max_index;
// }
// This solution doesn't work, try and work out why.

// Below is the solution given by the exercise writer.
method FindMax(a: array<int>) returns (max: int)
	requires 0 < a.Length
	ensures forall k :: 0 < k < a.Length ==> max >= a[k]
	// ensures exists k :: 0 < k < a.Length ==> max == a[k]
{
	var index := 0;
	max := a[0]; // assume first is max
	while index < a.Length
		invariant 0 <= index <= a.Length
		invariant forall k :: 0 <= k < index ==> max >= a[k]
	{
		if a[index] >= max { max := a[index]; }
		index := index + 1;
	}
}
// We want to use a binary search for sorted arrays. However, to do this we will introduce predicates.

// Example of a 'sorted' predicate:   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]

// predicate sorted(a: array<int>)
// {
//   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
// }

// The above predicacte will not work however, there is an issue as the predicate cannot read 'a'. We need framing to fix this.

// The reading frame of a function is all the memory locations that the function is allowed to read. 

predicate sorted(a: array<int>)
    reads a
{
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

// Along with a reads keyword there is a modify keyword. Methods don't need read permission explicitly as they already have it. They do need modify permission. 

// Framing only applies to the heap. Local variables don't go on the heap. 

// Exercise 12: Create a sorted array predicate for a sorted array with distinct elements

predicate sortedNoDupe(a: array<int>)
  reads a
{
  forall j,k :: 0 <= j < k < a.Length ==> a[j] < a[k]
}


// Ex 13: Change sorted so it allows its argument to be null but returns false if it is

predicate sortedNull(a: array?<int>)
  reads a
{
  if a == null then false else
  forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
//   Could also write: a == null ==> false && 
}


// Binary search

// method BinarySearch(a: array<int>, value: int) returns (index: int)
//   requires 0 <= a.Length && sorted(a)
//   ensures 0 <= index ==> index < a.Length && a[index] == value
//   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
// {
//   // This one is a little harder. What should go here?
//   var lower : int := 0 ;
//   var upper : int := a.Length - 1 ;  

//   var mid : int := a.Length / 2;
//   while a[mid] != value
//     invariant 0 <= lower < upper < a.Length
//     invariant 0 <= mid < a.Length

//     {
//         if a[mid] > value {
//             upper := mid; 
//             mid  := (lower + upper) / 2 ;
//         }else{
//             lower := mid ;
//             mid := (lower + upper) / 2 ; 
//         }

//     }   
//     index := mid; 
// }

// The above solution has a few faults, see if you can remember them. 


method BinarySearch(a: array<int>, value: int) returns (index: int)
  requires 0 <= a.Length && sorted(a)
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  var low, high := 0, a.Length;
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i ::
      0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
  {
    var mid := (low + high) / 2;
    if a[mid] < value {
      low := mid + 1;
    } else if value < a[mid] {
      high := mid;
    } else {
      return mid;
    }
  }
  return -1;
}

// Ex 14:Change the assignments in the body of BinarySearch to set low to mid or to set high to mid - 1. In each case, what goes wrong?

method BinarySearch2(a: array<int>, value: int) returns (index: int)
  requires 0 <= a.Length && sorted(a)
  ensures 0 <= index ==> index < a.Length && a[index] == value
  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
  var low, high := 0, a.Length;
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i ::
         0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
  {
    var mid := (low + high) / 2;
    if a[mid] < value {
      low := mid + 1;
    } else if value < a[mid] {
      high := mid;
    } else {
      return mid;
    }
  }
  return -1;
}