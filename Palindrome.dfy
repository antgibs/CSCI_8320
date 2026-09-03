/* 
Palindrome Checker 

Given an array as input, return true if array is the same read back and forth, false if not.
*/

method isPalindrome(s: string) returns (b: bool)
requires |s| > 1
{
    /* Setup */
    b := true;
    var j := |s| / 2;
    var i := j;
    // If s has even number of chars, move i back 1
    if |s| % 2 == 0 { i := i - 1; }

    // Loop
    while i >= 0 && j < |s|
    {
        if s[i] != s[j] {return false;} // j is an index out of range. Why?
        i := i - 1;
        j := j + 1;
    }
}