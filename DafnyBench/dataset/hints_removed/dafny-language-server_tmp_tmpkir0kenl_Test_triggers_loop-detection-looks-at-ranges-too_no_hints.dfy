// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file checks that loops between the range and the term of a quantifier
// are properly detected.

predicate P(x: int)

method M(x: int) {
  // This will be flagged as a loop even without looking at the range
  // This requires checking the range for looping terms
}

