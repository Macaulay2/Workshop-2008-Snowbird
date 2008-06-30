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
 RTar := (flattenRing (R[z_1..z_(rank target f), Degrees => tarDegs]))_0;
  RTarNewVars := matrix{{RTar_0..RTar_((rank target f)-1)}};
 --puts the vars in the wrong ring!

---------

newRing R

resets the Heft vector and won't take the Heft option seriously.
restart
R=ZZ[x,y, Degrees => {{0,1},{0,1}}, Heft=>{0,1}]	 
S=newRing(R, Heft=>{0,1})	 
monoid S
S=newRing(R, Heft=>{1,0})	 
monoid S
S=newRing(R, Degrees=> {{0,0,1}, {0,0,1}}, Heft=>{0,0,1})	 
monoid S

-------------

Need a function that takes a ring (maybe a quotient of a quotient of a...) and
makes a minimal presentation (maybe flattening as an option) -- this would display better etc.
