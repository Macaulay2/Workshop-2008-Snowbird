--
-- Free Resolutions of Ideals of Points
--
-- DE+SP 96--97, last updated 01/99

-- Routines:
--                points
--                randomPoints
--                canonicalPoints
--                expectedBettiMRC
--                minmaxBetti
--                selfAssociated
--                macaulayRep
--                macaulayRepToInteger
--                numLexSeg
--                lexSeg


points = method()
points Matrix := (M) -> (
        V := vars ring M;
	if not isPolynomialRing(ring M) then error "expected a matrix over a polynomial ring";
	if rank source V =!= rank target M then 
	               error "given matrix has not expected number of rows";
	Points := ideal(V*(gens ker transpose M_{0}));
	scan(rank(source M)-1, i -> Points = intersect(Points,ideal(V*(gens ker transpose M_{i+1}))));
	Points
	)


randomPoints = method()
randomPoints (Ring, ZZ) := (R,n) -> (
        if not isPolynomialRing(R) then error "expected a polynomial ring";
        if (n<=0) then error "expected a positive integer"; 
	d := numgens R;	
	points(random(R^d,R^n))
        )

randomPoints (ZZ, ZZ) := (r,n) -> (
        if (n < 1) or (r < 1) then error "expected a positive integers"; 
	R := ZZ/101[x_0..x_r];
	randomPoints(R,n)
	)

randomPoints (Ring,ZZ,ZZ) := (R,n,whatever) -> (
        if not isPolynomialRing(R) then error "expected a polynomial ring";
        if (n<=0) then error "expected a positive integer"; 
        d := numgens R;        
        M := id_(R^d) | transpose matrix(R,{toList(d:1)}) | random(R^d,R^(n-d-1));
        points(M)
        )




EXAMPLE lines ///
R=ZZ/101[x_0..x_6]
I=randomPoints(R,11)
hilbertPolynomial(R/I)
betti res I
-- total: 1 17 46 46 30 18 4          -The first counterexample to the MRC
--        0: 1 .  .  .  .  .  .
--        1: . 17 46 45 5  .  .   
--        2: . .  .  1  25 18 4
///

EXAMPLE lines ///
R=ZZ/101[x_0..x_8]
I=randomPoints(R,13,1)
hilbertPolynomial(R/I)
betti res I
-- total: 1 32 136 266 280 150 51 24 4  -Another counterexample to the MRC
--     0: 1 .   .   .   .   .  .  .  .
--     1: . 32 136 266 280 140 2  .  .
--     2: . .   .   .   .  10  49 24 4
///

canonicalPoints = method() 
canonicalPoints Matrix := (M) -> (
        R := ring M;
        if not isPolynomialRing(R) then error "expected a polynomial ring";
        r := (rank target M)-1;
        if (numgens R =!= r+1) then error "given matrix has wrong size";
        V := vars R;
	dualmat := gens ker M;
	s := (rank source dualmat)-1;
	n := rank source M;
	mult := matrix(R, table(n,n^2,(i,j)->(if ((j//n==j%n) and (j%n==i)) then 1 else 0)));
	prod := mult*((transpose M)**dualmat);
	V = id_(R^{1})**V;
	(V**id_(R^(s+1)))*(gens ker prod)
	)





EXAMPLE lines ///
R = ZZ/101[x_0..x_6]
M = random(R^7,R^(11))
omega = canonicalPoints(M)
betti res coker omega
--    total: 4 18 30 46 46 17 1           The first counterexample to MRC
--       -1: 4 18 25 1  .  .  .    
--        0: . .  5  45 46 17 .
--        1: . .  .  .  .  .  1
///


expectedBettiMRC = (r,n) -> (
	-- define the integer d = e-1
	e := 1;
	while binomial(r+e,e)<= n do e=e+1;
	d := e-1;
	a := n-binomial(r+d,d);
	toprow := apply(1..r,i->
	     max((binomial(d+i-1,i-1))*(binomial(r+d,d+i))-a*(binomial(r,i-1)),
		0));
	bottomrow := apply(1..r, i->
		max(a*(binomial(r,i))-(binomial(d+i,i))*(binomial(r+d,d+i+1)),
		0));
	R := ZZ/2[t];
	C := new ChainComplex;
	C.ring = R;
	C#0 = R^{0};
	apply(1..r, i->C#i = R^({toprow#(i-1):-d-i,bottomrow#(i-1):-d-i-1}));
	betti C
	)


	
EXAMPLE lines ///
R=ZZ/101[x_0..x_6]
I=randomPoints(R,11)
hilbertPolynomial(R/I)
betti res I
-- total: 1 17 46 46 30 18 4          -The first counterexample to the MRC
--        0: 1 .  .  .  .  .  .
--        1: . 17 46 45 5  .  .   
--        2: . .  .  1  25 18 4
expectedBettiMRC(6,11)  --gives
-- total: 1 17 46 46 30 18 4          
--        0: 1 .  .  .  .  .  .
--        1: . 17 46 45 4  .  .   
--        2: . .  .  .  25 18 4
///

selfAssociated = method()
selfAssociated (Ring, Matrix) := (Q,V) -> (
     if not (isAffineRing(Q) and (dim Q==0))  then 
                     error "expected a finite dimensional algebra";
     B := (basis Q)**Q;
     n := rank source B;
     k := coefficientRing Q;
     S := k[A_0..A_(n-1)];
     G := S^n;
     -- Make the multiplication table, over Q
     use ring B;
     m1 := 1*(B**B);
     -- and the row of elements of V*V
     vv1 := 1*(V**V);
     -- (the operation ** does not automatically reduce its entries;
     -- mult by 1 corrects this.)
     --
     -- The columns of m2 are the coefficients of the 
     -- elements of the row matrix m1 in terms of the basis B
     m2 := transpose substitute(contract(transpose m1,B),0);
     m2 = lift(m2,k);
     -- m3 is the same, expressed as a row matrix of linear forms
     m3 := (vars S)*m2;
     -- and finally the table
     m := adjoint(m3,G,G);
     -- Now do the same for VV
     vv2 := transpose substitute(contract(transpose vv1,B),0);
     vv2 = lift(vv2,k);
     vv := (vars S)*vv2;
     mbar := m**(S/ideal(vv));
     (kernel mbar)==0
     )

selfAssociated Ring := (Q) -> (
     if not (isAffineRing(Q) and (dim Q==1) and isHomogeneous(Q))  then 
         error "expected the homogeneous coordinate ring of a finite scheme";
     u := ideal(1-(vars Q) * random(source vars Q, Q^{-1}));
     Qbar := Q/u;
     selfAssociated(Qbar,(vars Q)**Qbar)
     )







macaulayRep = method()
macaulayRep (ZZ,ZZ) :=(a,d) -> (
	if (a < 0 or d < 0) then
		error "expected positive integers";
	if a == 0 then {} else
	    if d == 1 then {a} else (
        	b := d;
		while (binomial(b,d) <= a) do b = b+1;
		prepend(b-1, macaulayRep(a-binomial(b-1,d),d-1)))
	)



macaulayRepToInteger =method()
macaulayRepToInteger (List, ZZ) := (L,d) -> (
        if d<0 then error "expected  positive integers";
	sum(#L, i -> binomial(L_i,d-i))
	)


numLexSeg = method()
numLexSeg (ZZ,ZZ,ZZ) := (a,d,e) -> (
        if (e<d or d<1 or a<0) then error "numerically impossible";
	macaulayRepToInteger(apply(macaulayRep(a,d), i -> i+e-d),e)
	)


makeHilbertFcn = L -> (
		b := 1;
		apply( #L , i -> 
		      if i==0 or i == 1 then b = L_i else 
			   b = min(L_i,numLexSeg(b,i-1,i))
		      )
	        )


lexSeg = method() 
lexSeg (Ring, List) := (R, L) -> (
        if not isPolynomialRing(R) then error "expected a polynomial ring";
	C := makeHilbertFcn L;
	I := matrix(R,{{}});
	mm := vars R;
	sizemm := numgens R;
        scan(# C , i -> (
             if i == 1 then (
		I = submatrix(mm,{0},{0..sizemm-C_1-1}));
		if i > 1 then  (
		   d := numLexSeg(C_(i-1),i-1,i);
		   if C_i < d then (
		      mm = symmetricPower(i,vars R);
		      sizemm = rank source mm;
		      I = I | submatrix(mm,{0},{sizemm-d..sizemm-C_i-1});
	                            )
	                        )
			     )
	       );
            ideal I)



minmaxBetti = method() 
minmaxBetti (ZZ, ZZ) := (r,n) -> (
        if (r<1 or n<1) then error "expected positive integers";       
	print expectedBettiMRC(r,n);
        e := 0;
	while (binomial(r+e,e) <= n) do e = e+1;
	-- e is the minimal degree of a generator of the ideal
	H := apply(e, i -> binomial(r+i-1,i));
	H = append(H,n-binomial(r+e-1,e-1));
	if last H =!= 0 then H = append(H,0);
	R := ZZ/2[x_0 .. x_(r-1)];	
	betti res lexSeg(R,H)
        )

minmaxBetti (Ring, ZZ) := (R,n) -> (
        if not isPolynomialRing(R) then error "expected a polynomial ring";    
        r := (numgens R) - 1;
	minmaxBetti(r,n)
	)



EXAMPLE lines ///
minmaxBetti(6,11)
minmaxBetti(7,12)
minmaxBetti(9,20)
///
end

document {ymbol points,
     TT "points(M)", " -- returns the ideal of the set of points in Proj(R)
     whose coordinates are the columns of M, a matrix over the polynomial ring R."}

document{symbol randomPoints,
	TT "randomPoints(R,n)"," -- given a ring
	R, with r+1 variables, and a number n
	the script returns the homogeneous ideal of  
        n random points.",
	BR,NOINDENT,
	TT "randomPoints(r,n)","-- given positive
	integers r and n, returns the homogeneous ideal of  
        n random points over a polynomial ring in r+1 variables.",
	BR,NOINDENT,
	TT "randomPoints(r,n, whatever)", "--given a ring
        R, with r+1 variables, and a number n >= r+1,
        the script returns an r+1 x n matrix whose
        columns represent n random points including the
        standard simplex."
	}


document {symbol canonicalPoints,
	TT "canonicalPoints(M)"," -- given an (r+1) x n matrix M
	over a ring with r+1 variables, interpreted as a set of 
	n points in P^r, the script produces the linear part
	of the presentation matrix of w_{>=-1}, where w is the
	canonical module of the affine cone over the points.  It is
	necessary for this to assume that no subset of n+1
	of the points is linearly dependent.  The presentation
	is actually a presentation of w if the points do not
	lie on a rational normal curve (so there are no
	quadratic relations on w_{>=-1}) and impose independent
	conditions on quadrics (so the homogeneous coordinate
	ring is 3-regular, and w is generated in degree -1)."}
   
   


document {symbol expectedBettiMRC,
        TT "expectedBettiMRC(r,n)"," -- computes the expected Betti 
	numbers of n points in P^r (cf. Minimal Resolution Conjecture)",
        PARA, "These are displayed  as graded Betti numbers (Net) for an 
	appropriate ", TO "ChainComplex", " over the ring  ZZ/2[t]",
	PARA, "Here is a sample display:",
	EXAMPLE {
	     "R=ZZ/101[x_0..x_3]",
             "I=randomPoints(R,10)",
	     "betti res I",
	     "expectedBettiMRC(3,10)",
	     }
        }
	

document {symbol selfAssociated,
         TT "selfAssociated(Q,V)", "-- Given a finite scheme 
	 in a projective space represented by a FINITE DIMENSIONAL 
	 algebra Q, and a row matrix V giving generators for the 
         subspace of linear forms, the function returns TRUE
         if the finite scheme is self-associated.",
	 BR,NOINDENT,
	 "The idea is to form the multiplication table of Q 
         as a matrix of linear forms over a new polynomial ring 
         S = Sym Q whose variables correspond to a basis of Q.
         We then tensor the matrix with S/(VV),
         where VV is the space of linear forms in S
         coming from the subspace V*V of Q. This reduction
         represents the generic pairing on Q that annihilates
         VV. Self-association means that it becomes an isomorphism
         on generic specialization to a symmetric matrix over
         the ground field, that is, if its rank is equal to
         the dimension of Q.",
	 BR,NOINDENT,
	 TT "-- selfAssoc(R)", "--Given the homogeneous coordinate 
	 ring R of a finite scheme in projective space,
         this function returns TRUE if the scheme is self-associated.",
	 BR,NOINDENT, "We first reduce mod a generic linear form, 
	 then call the first version of", TO "selfAssociated", 
         "to deal with the inhomogeneous case. See the 
         first aprt of the documentation for more information.",
         BR,NOINDENT, "-- CAVEATS: The linear form must not vanish
         on the scheme; if the field is too small this
         could be a problem. Could probably do it a little
         faster by replacing one of the variables by 1
         in the matrix representing the linear forms.
         Also, if one of the variables does not vanish
         at any point of x, using it as the linear form
         would probably make the computation faster.",
	 PARA,
EXAMPLE 
///
-- the set consisting of 4 points on each of 
-- two skew lines in P3 is self-associated
R=ZZ/101[a,b,c,d]
I= saturate (intersect(ideal(a,b), ideal(c,d))+ideal((a+c)^4))
hilbertPolynomial(R/I)
x=random(R^1, R^{-1})
Q=R/(I+ideal(x-1))
V=matrix{{1,b,c,d}}
selfAssociated (Q,V)
         ///,
EXAMPLE 
///
-- While  5 points on one and three points on the other
--is not.
R=ZZ/101[a,b,c,d]
use R
I=intersect(
     ideal(a,b,c),
     ideal(a,b,d),
     ideal(a,b,c+d),
     ideal(a,b,c-d),
     ideal(a,b,c+7*d),
     ideal(c,d,a),
     ideal(c,d,b),
     ideal(c,d,a+b)
     )
hilbertPolynomial(R/I)
x=random(R^1, R^{-1})
Q=R/(I+ideal(x-1))
V=matrix{{1,b,c,d}}
selfAssociated (Q,V)
///,
EXAMPLE 
///
-- the set consisting of 4 points on each of 
-- two skew lines in P3 is self-associated
S=ZZ/101[a,b,c,d]
I= saturate (intersect(ideal(a,b),
     ideal(c,d))+
     ideal((a+c)^4))
selfAssociated (S/I)
///,
EXAMPLE
///
--- The base locus of a net of quadrics in P^3 is 
--- self associated
R=ZZ/101[x_0..x_3]
I=ideal(random(R^1, R^{3:-2}))
selfAssociated (R/I)
///
}

document{symbol macaulayRep,
	TT "macaulayRep(a,d)"," -- returns the list {m_0,..,m_k} of
	positive integers such that
		a = binomial(m_0,d)+..+binomial(m_k,d-k)",
        PARA, "Here is an example:",
        EXAMPLE {
           "macaulayRep(6,2)",
           "macaulayRep(111,3)",
           } 
        }

document{symbol macaulayRepToInteger,
	TT "macaulayRepToInteger({a_0,..,a_s},d)","-- returns
	the integer binomial(a_0,d)+...+binomial(a_s, d-s). 
        Thus it is inverse to macaulayRep(a,d)."}

TEST ///
assert(macaulayRepToInteger({19, 18, 14, 11, 10, 6, 5}, 8) == 111111)
///

document{symbol numLexSeg,
	TT "numLexSeg(a,d,e)", " Returns the minimal codimension in 
	degree e of an ideal of codimension a in degree d. It
	is attained for the lexicographic segment ideal.
	Here we must have e>=d>=1."}

document{symbol makeHilbertFcn,
	TT "makeHilbertFcn {1,a1,..,as}"," -- Returns the first s terms of 
	the termwise largest Hilbert function of a cyclic module
	S/I that is termwise <= {1,a1,..,as}. The a_i's should all
	be non-negative integers"}

document{symbol lexSeg,
	TT "lexSeg(R, {1,a1,..,a_s})"," -- Given a list {1,a1,..,as} of
	nonnegative integers, and a ring R with at least a1 variables,
	the script returns the smallest lexicographic segment ideal I over R 
	such that the Hilbert function of R/I begins with
	1,a1,b2,..,bs and bi <= ai for each i. (Thus if the given
	sequence is a possible Hilbert function, bi = ai for all i,
	and the ideal I is generated in degrees <=s."}  

TEST ///
assert(macaulayRep(27,5) == {7,5,3})
assert(macaulayRepToInteger(macaulayRep(250,10),10)==250)
assert(makeHilbertFcn{3,4,3,2,3,2,1} == {3, 4, 3, 2, 2, 2, 1})
R = ZZ/31991[x_1..x_3];
assert(lexSeg(R,{1,3,2}) == ideal(x_1^2, x_1*x_2, x_1*x_3, x_2^2))
///	

document{symbol minmaxBetti,
	TT "minmaxBetti(r,n)"," -- given integers r,n, produces the
	Betti diagrams of the expected (MRC) resolution of n points
	in P^r, and the Betti diagram of the lexicographic
	segment ideal with the same hilbert function as the
	general hyperplane section of the ideal of the 
	general points (in one fewer variables); this is
	the maximum possible resolution for a purely one-dimensional 
	ideal with the same Hilbert function as the points."}	

