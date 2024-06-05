/* https://leetcode.com/problems/longest-substring-without-repeating-characters/
Given a string s, find the length of the longest substring without repeating characters.

Example 1:
Input: s = "abcabcbb"
Output: 3
Explanation: The answer is "abc", with the length of 3.
*/


// a left-inclusive right-exclusive interval:
type interval = iv: (int, int) | iv.0 <= iv.1 witness (0, 0)

ghost function length(iv: interval): int {
  iv.1 - iv.0
}

ghost predicate valid_interval(s: string, iv: interval) {
  && (0 <= iv.0 <= iv.1 <= |s|)                             // interval is in valid range
  && (forall i, j | iv.0 <= i < j < iv.1 :: s[i] != s[j])   // no repeating characters in interval
}

// Below shows an efficient solution using standard "sliding window" technique. 
// For verification simplicity, we pretend as if:
// - `set` were Python set (or even better, a fixed-size array -- if the "alphabet" is small)
//
// `best_iv` is for verification purpose, not returned by the real program, thus `ghost`.
method lengthOfLongestSubstring(s: string) returns (n: int, ghost best_iv: interval)
  ensures valid_interval(s, best_iv) && length(best_iv) == n    /** `best_iv` is valid */
  ensures forall iv | valid_interval(s, iv) :: length(iv) <= n  /** `best_iv` is longest */
{
  var lo, hi := 0, 0;             // initialize the interval [lo, hi)
  var char_set: set<char> := {};  // `char_set` stores all chars within the interval
  n, best_iv := 0, (0, 0);        // keep track of the max length and corresponding interval

  while hi < |s|
    decreases |s| - hi, |s| - lo
    // Below are "mundane" invariants, maintaining the relationships between variables:
    invariant 0 <= lo <= hi <= |s|
    invariant valid_interval(s, (lo, hi))
    invariant char_set == set i | lo <= i < hi :: s[i]
    invariant valid_interval(s, best_iv) && length(best_iv) == n
    // The invariant below reflects the insights behind the "sliding window":
    invariant forall iv: interval | iv.1 <= hi && valid_interval(s, iv) :: length(iv) <= n  /* (A) */
    invariant forall iv: interval | iv.1 > hi && iv.0 < lo :: !valid_interval(s, iv)        /* (B) */
  {
    if s[hi] !in char_set {  // sliding `hi` to lengthen the interval:
      char_set := char_set + {s[hi]};
      hi := hi + 1;
      if hi - lo > n {  // update the max length: 
        n := hi - lo;
        best_iv := (lo, hi);
      }
    } else {  // sliding `lo` to shorten the interval: 
      char_set := char_set - {s[lo]};
      lo := lo + 1;
    }
  }
}


/* Discussions
1. The "sliding window" technique is the most "fancy" part of the solution,
  ensuring an O(n) time despite the O(n^2) search space.
  The reason why it works lies in the last two invariants: (A) and (B).

  Invariant (A) is simply a "partial" guarantee for the longest valid substring in `s[..hi]`,
  so once the loop finishes, as `hi == |s|`, this "partial" guarantee becomes "full".

  Invariant (B) is crucial: it encodes why we can monotonically increase `lo` as we increase `hi`.
  What's the "intuition" behind that? Let me share an "informal proof" below:
  
    Let `sub(i)` be the longest valid substring whose last character is `s[i]`.
    Apparently, the final answer will be "the longest among the longests", i.e.
    `max(|sub(0)|, |sub(1)|, ..., |sub(|s|-1)|)`.

    Now, notice that the "starting position" of `sub(i)` is monotonically increasing regarding `i`!
    Otherwise, imagine `sub(i+1)` started at `j` while `sub(i)` started at `j+1` (or even worse),
    then `sub(i)` could be made longer (by starting at `j` instead).
    This is an obvious contradiction.

    Therefore, when we search for the starting position of `sub(i)` (the `lo`) for each `i` (the `hi`),
    there's no need to "look back".

2. The solution above can be made more efficient, using "jumping window" instead of "sliding window".
  Namely, we use a dict (instead of set) to look up the "position of repetition",
  and move `lo` right after that position at once.

  You can even "early terminate" (based on `lo`) when all remaining intervals are doomed "no longer",
  resulting in even fewer number of loop iterations.
  (Time complexity will still be O(n), though.)

  The corresponding verification code is shown below:
*/


// For verification simplicity, we pretend as if:
// - `map` were Python dict (or even better, a fixed-size array -- if the "alphabet" is small)
method lengthOfLongestSubstring'(s: string) returns (n: int, ghost best_iv: interval)
  ensures valid_interval(s, best_iv) && length(best_iv) == n
  ensures forall iv | valid_interval(s, iv) :: length(iv) <= n
{
  var lo, hi := 0, 0;
  var char_to_index: map<char, int> := map[];  // records the "most recent" index of a given char
  n, best_iv := 0, (0, 0);        

  // Once |s| - lo <= n, there will be no more chance, so early-terminate:
  while |s| - lo > n                    /* (C) */
  // while hi < |s| && |s| - lo > n     /* (D) */
    decreases |s| - hi
    invariant 0 <= lo <= hi <= |s|
    invariant valid_interval(s, (lo, hi))
    invariant forall i | 0 <= i < hi :: s[i] in char_to_index
    invariant forall c | c in char_to_index ::
      var i := char_to_index[c];  // the "Dafny way" to denote `char_to_index[c]` as `i` for brevity
      0 <= i < hi && s[i] == c
      && (forall i' | i < i' < hi :: s[i'] != c)  // note: this line captures that `i` is the "most recent"
    invariant valid_interval(s, best_iv) && length(best_iv) == n
    invariant forall iv: interval | iv.1 <= hi && valid_interval(s, iv) :: length(iv) <= n
    invariant forall iv: interval | iv.1 > hi && iv.0 < lo :: !valid_interval(s, iv)
  {
    if s[hi] in char_to_index && char_to_index[s[hi]] >= lo {  // has repetition!
      lo := char_to_index[s[hi]] + 1;
    }
    char_to_index := char_to_index[s[hi] := hi];
    hi := hi + 1;
    if hi - lo > n {
      n := hi - lo;
      best_iv := (lo, hi);
    }
  }
}

// Bonus Question:
//   "Why can we safely use (C) instead of (D) as the loop condition? Won't `hi` go out-of-bound?"
// Can you figure it out?

