--Bugs and notes:

1. Many routines implicitly assume that the base ring is nice, but the documentation doesn't
say so. For example, decompose (I think) assumes a polynomial ring. Certainly top and 
minimalPrimes do. 

2. The current function rank(Module) requires a singly graded domain, since
it computes things in terms of multiplicities.

In general, rank should
probably only be defined for modules that are generically free of constant rank;
that is, there should be a nonzerodivisor such that after inverting it, the module
becomes free (in the graded or local situation.) An error message should be returned
otherwise.

If the dimension of the module is zero, it must be
free to even have a rank.

Suppose the dimension of the module is > 0, and the module has k generators.
Then the module has a rank, (and the value is k-p)
if and only if the p x p minors of a presentation 
matrix contain a nozerodivisor x, while the (p+1) x (p+1) minors are nilpotent.

When the rank is defined AND the ring is singly graded, then the 
degree M/degree R used in the current function rank is correct.

Is there a better algorithm in general??

----------


