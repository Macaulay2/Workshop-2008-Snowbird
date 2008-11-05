---------------------------------------------------------------------------
-- PURPOSE : Compute the rees algebra of a module as it is defined in the 
--           paper "What is the Rees algebra of a module?" by Craig Huneke, 
--           David Eisenbud and Bernde Ulrich.
--           Also to compute many of the structures that require a Rees 
--           algebra, including 
-- analyticSpread
-- specialFiber
-- idealIntegralClosure
-- distinguished -- distinguished subvarieties of  a variety 
--                  (components of the support of the normal cone)
-- PROGRAMMERs : Rees algebra code written by David Eisenbud and
--               Amelia Taylor with some assistance from Sorin Popescu. 
-- UPDATE HISTORY : created 27 October 2006 
-- 	     	    updated 29 June 2008
--
-- Missing documentation and most examples are now at the end of the file
-- waiting to be included in the documentation -- more fixes to come
---------------------------------------------------------------------------
newPackage(
	"ReesAlgebra",
    	Version => "1.0", 
    	Date => "June 29, 2008",
    	Authors => {{
		  Name => "David Eisenbud",
		  Email => "de@msri.org"},
	     {Name => "Amelia Taylor",
	     HomePage => "http://faculty1.coloradocollege.edu/~ataylor/",
   	     Email => "amelia.taylor@coloradocollege.edu"},
             {Name => "Sorin Popescu",
	      Email => "sorin@math.sunysb.edu"}},  
    	Headline => "Rees algebras",
    	DebuggingMode => true
    	)



export{symmetricKernel, universalEmbedding,reesIdeal,reesAlgebra,
isLinearType, normalCone, associatedGradedRing, multiplicity,
specialFiberIdeal,analyticSpread, distinguished,distinguishedAndMult}

-- Comment : The definition of Rees algebra used in this package is 
-- R(M) = Sym(M)/(intersection over g of L_g) where the intersection 
-- ranges over all maps from M to free R-modules and L_g is the kernel 
-- of Sym(g) (where Sym(g): Sym(M) -> Sym(R)).

-- For computation the key is that R(M) = R(f) where f is any map from 
-- from M to a free module F such that the dual map F^* -> M^* is surjective
-- and R(f) is the image of Sym(f).

 
-- PURPOSE : Compute the rees ring of the image of a 
--           a matrix regarded as over a quotient ring.  
-- INPUT : 'f' a matrix and 'I' and an ideal over a polynomial ring OR 
--         a module over a polynomial or quotient ring. 
-- OUTPUT : an Ideal defining the Rees algebra of the image of f regarded 
--          as a matrix over the ring of I mod I if f is a versal embedding 
--          For the module or if f is not a versal embedding it naively computes 
--          the defining ideal of the Rees algebra and the output may be correct 
--          and it may be nonsense.
-- COMMENT : If I is the zero ideal and f is the generators of an ideal then 
--           the ideal is this is the usual
--           defining ideal of the usual Rees Algebra. Otherwise f 
--           corresponds to the versal embedding as defined in Eisenbud, 
--           Huneke, and Ulrich.  Also the Module version just sets up 
--           the input to use symmetric Kernel on a Module.  See "OUTPUT" 
--           for caution.

--- Assumes we have a homogeneous (multi) map

w := global w;
symmetricKernel = method(Options=>{Variable => global w})
symmetricKernel(Matrix) := Ideal => o -> (f) -> (
     if rank source f == 0 then return 0_R;
     R := ring f; 
     z := local z;
     newHeft := prepend(1,(monoid R).Options.Heft);
     sourceDegs := apply(degrees source f, i -> prepend(1,i));
     RSourceTemp:=(coefficientRing R)(
	  tensor(monoid[w_1..w_(rank ambient source f)],monoid R,Heft =>newHeft));
     RSource:=newRing(RSourceTemp, 
	  Degrees=>join(sourceDegs,drop ((monoid     RSourceTemp).Options.Degrees, 
		    rank ambient source f)));
     if rank target f == 0 then return ideal(1_RSource);
     tarDegs := apply(degrees target f, i -> prepend(1,i));
     RTar := (flattenRing (R[z_1..z_(rank target f), Degrees => tarDegs]))_0;
     RTarNewVars := matrix{
	  apply(rank target f, i->RTar_i)};
     RTarOldVars := substitute(vars R, RTar);
     fRTar := (map(RTar, R)) f;
     kernel map(RTar, RSource, RTarNewVars*fRTar|RTarOldVars)
     )

-- PURPOSE: Computes the universal embedding of the 
--          image of f, or of M or of J over a quotient ring.  
-- INPUT : 'M' a matrix and 'I' an ideal defined over a polynomial ring.
-- OUTPUT : a map that is a versal embedding of the image of M over the 
--          ring of M mod I.  
-- COMMENT : The purpose is to compute a universal embedding to be used in 
--           symmetricKernel in order to compute a Rees Algebra in the most 
--           general case possible at this time as defined in Eisenbud, Huneke 
--           and Ulrich. 

universalEmbedding = method()
universalEmbedding(Module) := Matrix => (M) -> (
     UE := transpose syz transpose presentation M;
     map(target UE, M, UE)
     )

-- PURPOSE : Front end for computing the defining ideal of the Rees algebra 
--           of a module, or an ideal defined over a polynomial ring or a 
--           quotient ring.
-- INPUT : 'M' a module OR
--         'J' an ideal 
-- Options : The computation requires additional variables.  The user 
--           can use Variable => to specify the letter used for the 
--           new indexed variable.  The default is the letter w.  The 
--           default algorithm is symmetricKernel, but in the case of 
--           an ideal over a polynomial ring the user might want to use 
--           the algorithm in reesSaturate specified by Strategy => Saturate.
-- OUTPUT : an Ideal defining the Rees algebra of the module M or of the ideal J.
-- COMMENT : Uses proposition 1.3 in Eisenbud, Huneke, Ulrich and computes 
--           the rees algebra of a versal embedding of the 
--           Module regardless of the ring and for an ideal over a quotient ring. 
--           In the case of an ideal over a polynomial ring the process is slightly 
--           streamlined, skipping the unneccessary versal computation as in that 
--           case the inclusion map is a versal map.

reesIdeal = method(Options => {Variable => w})

reesIdeal(Module) := Ideal => o -> M -> (
     P := presentation M;
     UE := transpose syz transpose P;
     symmetricKernel(UE,Variable => o.Variable)
     )

reesIdeal(Ideal) := Ideal => o-> (J) -> (
symmetricKernel(gens J, Variable => o.Variable)
     )

---- needs user-provided non-zerodivisor. 

reesIdeal (Module, RingElement) := Ideal => o -> (M,a) -> (
     R:= ring M;
     if R =!= ring a 
     then error("Expected Module and Element over the same ring");   
     P := presentation M;
     sourceDegs := apply(degrees target P, i -> prepend(1,i));
     newHeft := prepend(1,(monoid R).Options.Heft);
     RSourceTemp:=(coefficientRing R)(
	  tensor(monoid[w_1..w_(rank target P)],monoid R,Heft =>newHeft));
     RSource:=newRing(RSourceTemp, 
	  Degrees=>join(sourceDegs,drop ( (monoid RSourceTemp).Options.Degrees, rank target P)));
     NewVars:=matrix{apply(rank target P, i->RSource_i)};
     I := ideal (NewVars*(substitute(P, RSource)));
     a = substitute(a, RSource);
     saturate(I,a)
     )
reesIdeal(Ideal, RingElement) := Ideal => o -> (I,a) -> (
     reesIdeal(module I, a)
     )

reesAlgebra = method (TypicalValue=>Sequence,Options=>{Variable => w})
-- accepts a Module, Ideal, or pair (depending on the method) and
-- returns the quotient ring isomorphic to the Rees Algebra rather
-- than just the defining ideal as in reesIdeal. 

reesAlgebra Ideal := 
reesAlgebra Module := o-> M -> (
     R:=ring M;
     reesIM := reesIdeal M;
     reesAM := (ring reesIM)/reesIM;
     A:= map(reesAM, R);
     (reesAM,A)
     )

reesAlgebra(Ideal, RingElement) := 
reesAlgebra(Module, RingElement) := o->(M,a)->(
     R:=ring M;
     reesIM := reesIdeal(M,a);
     reesAM := (ring reesIM)/reesIM;
     A:= map(reesAM, R);
     (reesAM,A)
     )
       
isLinearType=method(TypicalValue =>Boolean)

isLinearType(Ideal):=
isLinearType(Module):= M->(
     if class M == Ideal then M = module M;
     I:=reesIdeal M;
     P:=substitute(presentation M, ring I);
     newVars := matrix{apply(rank target P, i -> (ring I)_i)};
     J:=ideal(newVars*P);
     ((gens I)%J)==0)
     
isLinearType(Ideal, RingElement):=
isLinearType(Module, RingElement):= (M,a)->(
     if class M == Ideal then M = module M;
     I:=reesIdeal (M,a);
     P:=substitute(presentation M, ring I);
     newVars := matrix{apply(rank target P, i -> (ring I)_i)};
     J:=ideal(newVars*P);
     ((gens I)%J)==0
     )
     
normalCone = method(TypicalValue => Ring, Options => {Variable => w})
normalCone(Ideal) := o -> I -> (
     RI := reesAlgebra(I);
     (RI_0)/(RI_1 I)
     )
normalCone(Ideal, RingElement) := o -> (I,a) -> (
     RI := reesAlgebra(I,a);
     (RI_0)/(RI_1 I)
     )
     
associatedGradedRing= method(TypicalValue => Ring, Options => {Variable => w})
associatedGradedRing (Ideal) := o -> I -> normalCone(I)
associatedGradedRing (Ideal, RingElement) := o -> (I,a) -> normalCone(I)
     

-- PURPOSE : Compute the multipicity e_I(M) and e(I) = e_I(R), 
--           the normalized leading coefficient of the corresponding 
--           associated graded ring.  
-- INPUT : 'I' an Ideal, for e(I) or 'I' and 'M' for e_I(M)
-- OUTPUT : the Hilbert-Samuel multiplicity
-- COMMENT : The associated graded ring is computed using the Rees algebra.
-- WARNING : Computing a quotient like R[It]/IR[It] requires a 
--           Groebner basis computation and thus can quickly take all of your
--           memory and time (most likely memory).   

multiplicity = method()
multiplicity(Ideal) := ZZ => I ->  (
     RI := normalCone I;
     --- This method of building the new ring with degrees to use the
     --- function degree may not be the best for all examples. 
     RIring := ring presentation RI; 
     RInew := (coefficientRing(RIring))[gens RIring, MonomialOrder => (monoid RIring).Options.MonomialOrder];
     degree (RInew/(substitute(ideal presentation RI, RInew)))
     )
multiplicity(Ideal,RingElement) := ZZ => (I,a) ->  (
     RI := normalCone (I,a);
     RIring := ring presentation RI; 
     RInew := (coefficientRing(RIring))[gens RIring, MonomialOrder => (monoid RIring).Options.MonomialOrder];
     degree (RInew/(substitute(ideal presentation RI, RInew)))
     )
--- RInew = newRing(ring presentation RI, Degrees => apply(#gens RI,i -> {1}));

///
restart
load "ReesAlgebra.m2"

kk=ZZ/101
S=kk[x,y]
I = ideal(x^2, y^3)
assert (multiplicity I == 6)
use S
I=ideal(x^2, x*y+y^3)
assert(multiplicity I == 6)
use S
I = ideal(x^2+x^3)
assert(multiplicity I == 3)
normalCone I
use S
isLinearType I

use S
I = ideal((x+1)^2, (x+1)*(y+1)+(y+1)^3)
multiplicity I

use S
I = ideal"x3, x2y,y3"
multiplicity I
degree(S^1/I)
viewHelp TEST
///

--Special fiber is here defined to be the fiber of the blowup over the
--homogeneous maximal ideal of the original ring.

specialFiberIdeal=method(TypicalValue=>Ideal, Options=>{Variable=>w})

specialFiberIdeal(Ideal):= 
specialFiberIdeal(Module):= o->i->(
     Reesi:= reesIdeal(i, Variable=>o.Variable);
     trim (Reesi + substitute(ideal vars ring i, ring Reesi))
     )
 
specialFiberIdeal(Ideal, RingElement):=
specialFiberIdeal(Module,RingElement):= o->(i,a)->(
     Reesi:= reesIdeal(i, a, Variable=>o.Variable);
     trim (Reesi + substitute(ideal vars ring i, ring Reesi))
     )

-- PURPOSE : Analytic spread of a module as defined in M2 by a matrix, 
--           a module or ideal over a quotient ring R/I.
-- INPUT : 'M' a module OR
--         'J' an ideal  
-- Options : The ring R can be a quotient ring, or, the user can define 
--           f, M or J over a polynomial ring R and an ideal I can be given 
--           as the option Strategy and the special fiber is then computed 
--           over the quotient ring R/I.
-- OUTPUT : The analytic spread of f/M/or J over over the ring R, or if 
--          the option is given, R/I.
analyticSpread = method()

analyticSpread(Ideal) := 
analyticSpread(Module) := ZZ => (M) -> dim specialFiberIdeal(M)

analyticSpread(Ideal,RingElement) :=
analyticSpread(Module,RingElement) := ZZ => (M,a) -> dim specialFiberIdeal(M,a)
 
----- distinguished and Mult still does not work!!!!!
   
--We can use this to compute the distinguished subvarieties of
--a variety (components of the support of the normal cone).
--In the following routine i must be an ideal of a polynomial ring, not a 
--quotient ring.

-- PURPOSE : Compute the distinguised subvarieties of a variety 
--           (components of the support of the normal cone).
-- INPUT : 'i' an ideal over a polynomial ring. 
-- OUTPUT : the components of the support of the normal cone of V(i).
-- COMMENT : I have a note stating that "right now" this computation 
--           requires a polynomial ring over a finite field - written 
--           in 2000/2001.  I have no idea why.  I suspect that at the 
--           time decompose required this.  But I think it is not necessary 
--           now. 

distinguished = method(Options => {Variable => w})
distinguished(Ideal) := List => o -> i -> (
     R:=ring i;
     (reesAi,A) := reesAlgebra (i,Variable=>o.Variable);
     (T,B) := flattenRing reesAi;
     L:=decompose substitute(i,T);
     apply(L, p->kernel(map(T/p, T)*B*A))
     )

distinguished(Ideal,RingElement) := List => o -> (i,a) -> (
     R:=ring i;
     (reesAi,A) := reesAlgebra (i,a,Variable=>o.Variable);
     (T,B) := flattenRing reesAi;
     L:=decompose substitute(i,T);
     apply(L, p->kernel(map(T/p, T)*B*A))
     )
     
-- PURPOSE : Compute the distinguised subvarieties of a variety  
--           (components of the support of the normal cone) WITH their 
--           multiplicities.
-- INPUT : 'i' an ideal over a polynomial ring. 
-- OUTPUT : ideals that are the components of the support of the normal 
--          cone of V(i) and integers that are their corresponding 
--          multiplicities.
-- CAVEAT: R must be a polynomial ring.


///

restart
installPackage "ReesAlgebra"
loadPackage "ReesAlgebra"
T=ZZ/101[c,d]
D = 4
P = product(D, i -> random(1,T))
R = ZZ/101[a,b,c,d]
I = ideal(a^2, a*b*(substitute(P,R)), b^2)
ass I -- there is one minimal associated prime (a thick line in PP^3) and D embedded primes (points on the line) 
primaryDecomposition I
distinguished I -- only the minimal prime is a distinguished component


K = distinguishedAndMult(I) -- get multiplicity 2 
J=intersect apply(K, i-> i_1^(i_0)) -- checks the Geometric Nullstellensatz on Ein-Lazarsfeld
(gens J)% (gb I)

R=ZZ/32003[x,y,z]
I=intersect(ideal(x),(ideal(x,y))^2, (ideal(x,y,z))^3)
ass I
decompose top intersect(ideal(x), ideal(y,z))

distinguished  I
K = distinguishedAndMult I
intersect apply(K, i-> i_1^(i_0)) 

viewHelp top


///

distinguishedAndMult = method(Options => {Variable => w})
distinguishedAndMult(Ideal) := List => o -> i -> (
    R:=ring i;
    ReesI := reesIdeal( i, Variable => o.Variable);
    (S,toFlatS) := flattenRing ring ReesI;
     I:=(toFlatS ReesI)+substitute(i,S);
--     Itop:=top I;
--     L:=decompose Itop;
     L:=decompose I;
     apply(L,P->(Pcomponent := I:(saturate(I,P)); 
--     apply(L,P->(Pcomponent := Itop:(saturate(Itop,P)); 
	       --the P-primary component. The multiplicity is
	       --computed as (degree Pcomponent)/(degree P)
       	  {(degree Pcomponent)/(degree P), kernel(map(S/P, R))})))

distinguishedAndMult(Ideal,RingElement) := List => o -> (i,a) -> (
    R:=ring i;
    ReesI := reesIdeal( i,a, Variable => o.Variable);
    (S,toFlatS) := flattenRing ring ReesI;
     I:=(toFlatS ReesI)+substitute(i,S);
--     Itop:=top I;
--     L:=decompose Itop;
     L:=decompose I;
     apply(L,P->(Pcomponent := I:(saturate(I,P)); 
--     apply(L,P->(Pcomponent := Itop:(saturate(Itop,P)); 
	       --the P-primary component. The multiplicity is
	       --computed as (degree Pcomponent)/(degree P)
       	  {(degree Pcomponent)/(degree P), kernel(map(S/P, R))})))
 
 
------------------------------------------------------------------
--- We include the code from newrg.m2 in the Snowbird respository
--- This version of newRing is necessary for the code in this package 
--- and should be removed once a new distribution of M2 is released
--- as this version of newRing will be in that distribution. 
---
--- We are not exporting any of these functions as they will be in the
--- main distribution once released. 
 
nothing = first values options newRing

mergeOptions = (x,y) -> merge(x, y, (a,b) -> if b === nothing then a else b)

newRing Ring := Ring => opts -> (R) -> (
     -- First check the type of ring of R
     -- The following is for the case when R is a polynomial ring,
     -- or a quotient of a polynomial ring

     if    (instance(opts.Variables,List) 
              and #( opts.Variables ) =!= numgens R)
        or (instance(opts.Variables,ZZ) 
              and opts.Variables =!= numgens R)
     then
         error "cannot change the number of variables using 'newRing'";

     if opts.DegreeRank =!= nothing and opts.Degrees === nothing then opts = first override(opts, Degrees => null);
     --if opts.DegreeRank =!= nothing or opts.Degrees =!= nothing then opts = first override(opts, Heft => null);
     if opts.DegreeRank === nothing and opts.Degrees =!= nothing then opts = first override(opts, DegreeRank => null);
     opts = mergeOptions((monoid R).Options,opts);
     opts = select(opts, v -> v =!= nothing); -- this applies especially to the MonomialSize option, no longer present in (monoid R).Options
     f := presentation R;
     A := ring f;
     k := coefficientRing A;
     S := k(monoid [opts]);
     f = substitute(f,vars S);
     S/image f
     )
------------------------------------------------------------------
 
 
beginDocumentation()

document {
     Key => ReesAlgebra,
     Headline => "compute Rees algebras",
     " The goal of this package is to provide commands to compute the 
     Rees algebra of a module as it is defined in the paper ", EM "What is 
     the Rees algebra of a module?", " by Craig Huneke, David Eisenbud and 
     Bernd Ulrich. It also includes functions for computing many of 
     the structures that require a Rees algebra.  The included functions are 
     listed below. Examples of the use of each of the functions are included 
     with their documentation."
     }

-- We may want to change the examples.  Otherwise complete except that
-- we may want to give the full reference to Eisenbud Huneke Ulrich.
document {
     Key => {symmetricKernel,(symmetricKernel, Matrix)},
     Headline => "Compute the rees ring of the image of a matrix",
     Usage => "symmetricKernel(f)",
     Inputs => {"f" => {ofClass Matrix}},
     Outputs => {{ofClass Ideal, " defining the Rees ring of ", ofClass Matrix, " ", TT "f"}},	       
     PARA{}, "This function is the workhorse of all/most of the Rees algebra 
     functions in the package.  Most users will prefer to use one of the front 
     end commands ", TO "reesAlgebra", " or ", TO "reesIdeal", " and others.",
     EXAMPLE {
	  "R = QQ[a..e]",
	  "J = monomialCurveIdeal(R, {1,2,3})",
	  "symmetricKernel (gens J)"
     },
    "Let ", TT "I", " be the ideal returned and let ", TT "S", " be the ring it lives in 
    (also printed), then ", TT "S/I", " is isomorphic to 
    the Rees algebra ", TT "R[Jt]",  ".  We can get the same information
    above 
    using ", TT "reesIdeal(J)", ", see ", TO "reesIdeal", ".  Also 
    note that ", TT "S", " is multigraded allowing Macaulay2 to correctly 
    see that the variables of R now live in degree 0 and the new variables 
    needed to describe ", TT "R[Jt]", "as a k-algebra are in degree 1.",
    EXAMPLE {
	 "S = ring oo;",
	 "(monoid S).Options.Degrees"
	 },
    PARA{ TT "symmetricKernel", " can also be computed over a quotient 
    ring.  "},     
    EXAMPLE { 
     	  "R = QQ[x,y,z]/ideal(x*y^2-z^9)",
	  "J = ideal(x,y,z)",
	  "symmetricKernel(gens J)"
	  },
     "The many ways of working with this function allows the system 
     to compute both the classic Rees algebra of an ideal over a ring 
     (polynomial or quotient) and to compute the the Rees algebra of a 
     module or ideal using a universal embedding as described in the paper 
     of Eisenbud, Huneke and Ulrich.  It also allows different ways of 
     setting up the quotient ring.",
     SeeAlso => {reesIdeal, reesAlgebra, universalEmbedding},
     }


document {
     Key => [symmetricKernel, Variable],
     Headline=> "symmetricKernel introduces new variables and the option 
     Variable allows the user to specify a variable name for this purpose, 
     the default variable is", TT  "w", "but the default value of the option 
     is null."     
     }

--- needs work....
--- we are mappimg M to the dual of the syzygy of its dual.  
document { 
     Key => {universalEmbedding, (universalEmbedding,Module)},
     Headline => "Compute the universal embedding",
     Usage =>  "universalEmbedding M", 
     Inputs => {"M" => {ofClass Module, " over ", ofClass Ring}}, 
     Outputs => {{ofClass ModuleMap, " defining the universal embedding 
	       of the module ", TT "M", " given into a free module
 	       over the same ring as ", TT "M", "."}},
      PARA{}, "This function uses the transpose (dual) of the .  We
      first give a simple example looking at a syzygy matrix of the cube of
      the maximial ideal of a polynomial ring.",
      EXAMPLE {
 	  "S = ZZ/101[x,y,z];",
	  "FF=res ((ideal vars S)^3);",
	  "M=coker (FF.dd_2)",
	  "universalEmbedding M"
	  },
      PARA{},
     "A more complicated example.",
     EXAMPLE { 
	  "x = symbol x;",
	  "R=QQ[x_1..x_8];",
	  "m1=genericMatrix(R,x_1,2,2); m2=genericMatrix(R,x_5,2,2);",
	  "m=m1*m2",
	  "d1=minors(2,m1); d2=minors(2,m2);",
	  "M=matrix{{0,d1_0,m_(0,0),m_(0,1)},
               {0,0,m_(1,0),m_(1,1)},
	       {0,0,0,d2_0},
	       {0,0,0,0}}",
	  "M=M-(transpose M);",
	  "N= coker(res coker transpose M).dd_2",
	  "universalEmbedding(N)"
	  }
     }

document {
     Key => {reesIdeal, (reesIdeal,Ideal), (reesIdeal, Module), 
	  (reesIdeal,Ideal, RingElement), (reesIdeal,Module, RingElement)},
     Headline => "compute the defining ideal of the Rees Algebra",
     Usage =>  "reesIdeal(M)\n reesIdeal(I) \n reesIdeal(M,f) \n reesIdeal(I,f)",
     Inputs => {"M" => Module => "Any module over a quotient ring", 
	  "I" => Ideal => "Any ideal over a quotient ring",
	  "f" => RingElement => "Any non-zerodivisor 
	  mod the ideal or module"},
     Outputs => {{ofClass Ideal, " defining the Rees algebra of  
	       the ", ofClass Module, " ", TT "M"}},
     PARA{},
     "There are effectively two methods implemented in this package
     for computing the definiting ideal of a Rees algebra of a module or
     ideal over a quotient ring.  The first uses the code
     symmetricKernel which is based on Eisenbud, Huneke, Ulrich, and for
     ideals works as one might naively expect it to.  The second
     implementation can be much faster, but requires a user provided
     non-zerodivisor mod the ideal or module.  This algorithm saturates
     the ideal of the new variables times a presentation of the module with
     respect to the non-zerodivisor. We provide several examples below that
     include some meaningful time comparisons. ",
     EXAMPLE {
     	  "kk = ZZ/101;",
     	  "S=kk[x_0..x_4];",
     	  "i=monomialCurveIdeal(S,{2,3,5,6})",
     	  "time V1 = reesIdeal i;", -- 2.25 sec
     	  "time V2 = reesIdeal(i,i_0);" --.3 sec
     	  },
     "This example is particularly interesting upon a bit more
     exploration.",
     EXAMPLE { 
	  "numgens V1",
	  "numgens V2"
	  },
     "The difference is striking and, at least in part, explains the
     difference in computing time.  Furthermore, if we compute a Grobner
     basis for both and compare the two matrices, we see that we indeed got
     the same ideal.",
     EXAMPLE {
	  "M1 = gens gb V1;",
	  "M2 = gens gb V2;",
	  "use ring M2",
	  "M1 = substitute(M1, ring M2);",
	  "M1 == M2",
	  "numgens source M2"
	  },
     "Another example illustrates the power and usage of the code.  We
     also show the output in this example.  While a bit messy, the
     user can see how we handle the degrees in both cases.",
     EXAMPLE { 
	  "S=kk[a,b,c]",
	  "m=matrix{{a,0},{b,a},{0,b}}",
	  "i=minors(2,m)",
	  "time reesIdeal i",
	  "res i",
	  "m=random(S^3,S^{4:-1})",
	  "i=minors(3,m);",
	  "time I=reesIdeal (i,i_0);", -- .05 sec
	  "transpose gens I",
	  "i=minors(2,m);",
	  "time I=reesIdeal (i,i_0);" -- 22 sec
	  },
     "There is good evidence here, if we use reesIdeal i in the latter
cases, they take less time, but have more generators.",
     SeeAlso => {symmetricKernel, reesAlgebra}
     }

--I don't know
--the goal of haveing the first part of this example

-- needs updating, like most of this documentation.
document {
     Key => [reesIdeal, Variable],
     Headline=> "symmetricKernel introduces new variables and the option 
     Variable allows the user to specify a variable name for this purpose, 
     the default variable is", TT  "w", "but the default value of the option 
     is null."     
     }

-- the output is a sequence pair and loadpackage is yelling at us. 
document {
     Key => {reesAlgebra, (reesAlgebra, Module), (reesAlgebra, Ideal), 
	  (reesAlgebra, Module, RingElement), (reesAlgebra, Ideal, RingElement)},
     Headline => "determine if the image of a matrix is of linear type",
     Usage =>  "isLinearType(M)",
     Inputs =>  {"M", "a"},
     Outputs => {{ofClass Sequence, "true if the module is of linear 
	  type and false otherwise."}},
     "Stuff."
     }

document {
     Key => [reesAlgebra, Variable],
     Headline=> "rees introduces new variables and the option 
     Variable allows the user to specify a variable name for this purpose, 
     the default is", TT  "w"     
     }

document {
     Key => {isLinearType, (isLinearType, Module), (isLinearType, Ideal), 
	  (isLinearType,Module, RingElement), (isLinearType, Ideal, RingElement)},
     Headline => "determine if the image of a matrix is of linear type",
     Usage =>  "isLinearType(M)",
     Inputs =>  {"M", "a"},
     Outputs => {{"true if the module is of linear 
	  type and false otherwise."}},
     "Stuff."
     }

document {
     Key => {normalCone, (normalCone, Ideal), (normalCone, Ideal, RingElement)},
     Headline => "",
     Usage =>  "normalCone(J)",
     Inputs =>  {"J" => Ideal => "input",
	  "a" => RingElement => "also input"},
     Outputs => {{"true if the ideal is of linear 
	  type and false otherwise."}},
     "Stuff."
     }

document {
     Key => [normalCone, Variable],
     Headline=> "symmetricKernel introduces new variables and the option 
     Variable allows the user to specify a variable name for this purpose, 
     the default variable is", TT  "w", "but the default value of the option 
     is null."     
     }


document {
     Key => {associatedGradedRing, (associatedGradedRing, Ideal),
	  (associatedGradedRing, Ideal, RingElement)},
     Headline => "",
     Usage =>  "associatedGradedRing(J)",
     Inputs =>  {"J" => Ideal => "input",
	  "a" => RingElement => "otherinput"},
     Outputs => {{"true if the ideal is of linear 
	  type and false otherwise."}},
     "Stuff."
     }

document {
     Key => [associatedGradedRing, Variable],
     Headline=> "symmetricKernel introduces new variables and the option 
     Variable allows the user to specify a variable name for this purpose, 
     the default variable is", TT  "w", "but the default value of the option 
     is null."     
     }

document {
     Key => {multiplicity, (multiplicity, Ideal), (multiplicity, Ideal, RingElement)},
     Headline => "compute the Hilbert-Samuel multiplicty of an ideal",
     Usage =>  "multiplicity I",
     Inputs =>  {"I" => Ideal => "input",
	  "a" => RingElement => "other input"},
     Outputs => {{"  that is the normalized leading 
	  coefficient of the associated graded ring of ", TT "R", 
	  " with respect to ", TT "I"}},
     "Stuff."
     }

document { 
     Key => {specialFiberIdeal, (specialFiberIdeal, Module), 
	  (specialFiberIdeal, Ideal), (specialFiberIdeal, Module, RingElement), 
	  (specialFiberIdeal, Ideal, RingElement)},
     Headline => "compute the special fiber of the image of a matrix over a", 
     "a quotient ring",
     Usage =>  "specialFiber(M)",
     Inputs =>  {"M","a"},
     Outputs => {{"defining the special fiber of ", TT "M"}},
     "Stuff."
     }


document {
     Key => [specialFiberIdeal, Variable],
     Headline=> "symmetricKernel introduces new variables and the option 
     Variable allows the user to specify a variable name for this purpose, 
     the default variable is", TT  "w", "but the default value of the option 
     is null."     
     }


document {
     Key => {analyticSpread, (analyticSpread,Module),(analyticSpread, Ideal), 
	  (analyticSpread, Module, RingElement), 
	  (analyticSpread, Ideal, RingElement)},  
     Headline => "compute the analytic spread of a module over a 
     quotient ring",
     Usage => "analyticSpread(M)",
     Inputs => {"M","a"},
     Outputs => {{"the dimension of the special fiber of ", TT "M"}},
               "trouble Shooting documentation - stuff."
     }	   

document {
     Key => {distinguished, (distinguished, Ideal), 
	  (distinguished, Ideal, RingElement)},
     Headline => "computes the distinguished subvarieties of a scheme",
     Usage => "distinguished I" ,
     Inputs =>  {"I" => {ofClass Ideal, " in ", ofClass PolynomialRing}},
     Outputs => {{ofClass List, " of prime ideals defining the components 
	  of the support of the normal cone over ", TT "I"}},
     "Stuff."
     }

document {
     Key => [distinguished, Variable],
     Headline=> "distinguished introduces new variables and the option 
     Variable allows the user to specify a variable name for this purpose, 
     the default is", TT  "w"     
     }

document {
     Key => {distinguishedAndMult, (distinguishedAndMult,Ideal),
	  (distinguishedAndMult, Ideal, RingElement)},
     Headline => "compute the distinguished subvarieties of a variety along 
     with their multiplicities",
     Usage => "distinguishedAndMult I" ,
     Inputs => {"I" => {ofClass Ideal, " in ", ofClass PolynomialRing}, 
	  "a" => {ofClass RingElement, "stuff."}},
     Outputs => {{ofClass List, " of pairs where the first entry 
	       is the multiplicity of the second entry which is one 
	       of the ideals defining a component of the support of 
	       the normal cone over ", TT "I"}},
     "Stuff."
     }

document {
     Key => [distinguishedAndMult, Variable],
     Headline=> "distinguishedAndMult introduces new variables and the option 
     Variable allows the user to specify a variable name for this purpose, 
     the default is", TT  "w"     
     }


end    

///
restart
loadPackage "ReesAlgebra"
///

--- Some Very Basic Tests/Examples
TEST///
S=ZZ/101[x,y]
i=ideal"x5,y5, x3y2"
V1 = reesIdeal(i)
use ring V1
assert(V1 == ideal(-w_1*y^2+w_3*x^2,w_1*w_2*x-w_3^2*y,w_2*x^3-w_3*y^3,-w_1^2*w_2*y+w_3^3*x,w_1^3*w_
     2^2-w_3^5))
V2 = reesIdeal(i,i_0)
use ring V2
assert(V2 == ideal(-w_1*y^2+w_3*x^2,w_1*w_2*x-w_3^2*y,w_2*x^3-w_3*y^3,-w_1^2*w_2*y+w_3^3*x,w_1^3*w_
     2^2-w_3^5))
///

-- 3 very simple tests.  The first tests just reesIdeal, the second
-- just reesAlgebra and the third tests both. 
TEST///
S = ZZ/101[x,y]
M = module ideal(x,y)
V = reesIdeal M
use ring V
assert(V == ideal (-w_1*y+w_2*x))
use S
M = module (ideal(x,y))^2
R = reesAlgebra M
assert(numgens R_0 == 5)
use ring ideal R_0
assert(ideal R_0 == ideal (-w_2*y+w_3*x, -w_1*y + w_2*x, w_2^2 - w_1*w_3))
F = map(R_0, S, {x,y})
assert(F == R_1)
use S
M = module (ideal (x,y))^3
V = reesIdeal M
use ring V
assert(V == ideal (-w_3*y+w_4*x,-w_2*y+w_3*x,-w_1*y+w_2*x,w_3^2-w_2*w_4,w_2*w_3-w_1*w_4,w_2^2-w_1*w_3))
R = reesAlgebra M
assert(numgens R_0 == 6)
use ring ideal R_0
assert(ideal R_0 == ideal (-w_3*y+w_4*x,-w_2*y+w_3*x,-w_1*y+w_2*x,w_3^2-w_2*w_4,w_2*w_3-w_1*w_4,w_2^2-w_1*w_3))
F = map(R_0, S, {x,y})
assert(F == R_1)
///

--- Checking that the two methods for getting a Rees Ideal yields the
--- same answer.  Note that in this case M1 takes much longer than
--- M2.  Also, initially, the first one has 119 gens and the second
--- only 15!!  but both have 84 in the GB and have the same GB. This
--- is now an example as well. 
TEST///
x = symbol x
S=ZZ/101[x_0..x_4]
i=monomialCurveIdeal(S,{2,3,5,6})
M1 = gens gb reesIdeal i; 
M2 = gens gb reesIdeal(i,i_0);
use ring M2
M1 = substitute(M1, ring M2);
assert(M2 == M1)
///



///
--- Our working example
restart
loadPackage "ReesAlgebra"
S = kk[x_1,x_2, Degrees => {{1,1}, {1,-3}}]
I = ideal(x_1^4*x_2^3)
f = matrix{{x_1,x_2, 0, 0, 0}, {0, 0 , x_1^2, x_1*x_2, x_2^2}}
F = map(S^{{-2, 1}, {2, 2}}, S^{{-3, 0},{ -3, 4},{0,0}, {0, 4}, {0,8}}, f)
R = S/I
M = (image F)**R
symmetricKernel F
degrees ring oo
/// 


///
restart
loadPackage "ReesAlgebra"
kk=ZZ/101
R=kk[x,y]
i=(ideal vars R)^2
i = ideal(x^2, y^2)
isLinearType i -- error!
///

     
///
restart
loadPackage "ReesAlgebra"
kk=ZZ/101
R=kk[x,y]
i=(ideal vars R)^2
reesAlgebra i
reesIdeal i
specialFiberIdeal i
assert (isLinearType i==false) -- error
isLinearType (ideal vars R) -- error
normalCone i

restart
loadPackage "ReesAlgebra"
kk=ZZ/101
R=kk[x,y]
i = ideal(x^2,y^2)
-- need to reset ring
i = ideal(x+y^2)
multiplicity i 

R = ZZ/101[x,y]/ideal(x^3-y^3)
I = ideal(x^2,y^2)
multiplicity I

///

---------------------

restart
loadPackage "ReesAlgebra"

R=QQ[a..e]
j=monomialCurveIdeal(R, {1,2,3,5})
IS = symmetricKernel(gens j)
time L = reesAlgebra(j)
use R
M = coker gens j
reesAlgebra M
universalEmbedding M

(IM,A) = reesAlgebra(M)
IR= time reesIdeal(j)
betti gens IR
degrees source vars ring IR
specialFiberIdeal j
analyticSpread j
----


--TEST 
restart
loadPackage "ReesAlgebra"
R=QQ[a,b,c,d,e,f]
M=matrix{{a,c,e},{b,d,f}}
image M
analyticSpread image M


restart
loadPackage "ReesAlgebraNew"
--kk=ZZ/32003
R=QQ[x_1..x_8]
m1=genericMatrix(R,x_1,2,2)
m2=genericMatrix(R,x_5,2,2)
m=m1*m2
flatten m
i= ideal flatten m
d1=minors(2,m1)
d2=minors(2,m2)
j=i+d1+d2
codim j
d1_0
m_(0,0)
M=matrix{{0,d1_0,m_(0,0),m_(0,1)},
         {0,0,m_(1,0),m_(1,1)},
	 {0,0,0,d2_0},
	 {0,0,0,0}}
M=M-(transpose M)
minors(4,M)

I=ideal(0_R)
N=transpose (res coker transpose M).dd_2

uN=universalEmbedding(N)
symmetricKernel(uN)
IR=reesIdeal(N)

SIR= specialFiber(N)
*}

{*
fu=universalEmbedding(I,f)   -- f = ????
betti symmetricKernel(I,fu)
betti symmetricKernel(I,f)
*}

{*
restart
loadPackage "ReesAlgebraNew"
R = ZZ/32003[x,y,z]
I = ideal(x,y)
cusp = ideal(x^2*z-y^3)
RI = reesIdeal(I)
S = ring RI
totalTransform = substitute(cusp, S) + RI
D = decompose totalTransform -- the components are the proper transform of the cuspidal curve and the exceptional curve 
L = primaryDecomposition totalTransform 
apply(L, i -> (degree i)/(degree radical i))
-- the total transform of the cusp contains the exceptional with multiplicity two 
-- the proper transform of the cusp is a smooth curve but tangent to the exceptional curve 
singular = ideal(singularLocus(L_0));
SL = saturate(singular, ideal(x,y,z));
saturate(SL, ideal(w_0,w_1)) -- we get 1 so it is smooth.
degree(D_0+D_1)/(degree radical(D_0+D_1))
*}

{*
restart
loadPackage "ReesAlgebraNew"
R = ZZ/32003[x,y,z]
I = ideal(x,y)
tacnode = ideal(x^2*z^2-x^4-y^4)
RI = reesIdeal(I)
S = ring RI
totalTransform = substitute(tacnode, S) + RI
D = decompose totalTransform -- the components are the proper transform of the cuspidal curve and the exceptional curve 
L = primaryDecomposition totalTransform 
apply(L, i -> (degree i)/(degree radical i))
-- the total transform of the tacnode contains the exceptional with multiplicity two 
-- the proper transform of the tacnode is not yet smooth.  We compute the singular point of the proper 
-- transform and blow up again. 
singular = ideal(singularLocus(L_0));
SL = saturate(singular, ideal(x,y,z));
J = saturate(SL, ideal(w_0,w_1)) -- we get 1 so it is smooth.
RJ = reesIdeal(J,Variable => v)
SJ = ring RJ
totalTransform = substitute(L_0, SJ) + RJ
D = decompose totalTransform -- the components are the proper transform of the cuspidal curve and the exceptional curve 
L = primaryDecomposition totalTransform 
(degree L_1)/(degree radical L_1) -- multiplicity of the second exceptional curve is 1
-- the second blow-up desingularizes the tacnode. 
singular = ideal(singularLocus(L_0));
SL = saturate(singular, ideal(x,y,z));
J = saturate(SL, ideal(w_0,w_1))
J2 = saturate(J, ideal(v_0,v_1, v_2))


-- however blowing-up (x^2,y) desingularlizes the tacnode x^2-y^4 in a single step.
R = ZZ/32003[x,y,z]
I = ideal(x^2,y)
tacnode = ideal(x^2*z^2-y^4)
RI = reesIdeal(I)
S = ring RI
totalTransform = substitute(tacnode, S) + RI
D = decompose totalTransform -- the components are the proper transform of the cuspidal curve and the exceptional curve 
L = primaryDecomposition totalTransform 
singular = ideal(singularLocus(D_0));
SL = saturate(singular, ideal(x,y,z));
saturate(SL, ideal(w_0,w_1)) -- we get 1 so it is smooth.


-- two singularities (x^2+y^2-3x*z)^2 -4*x^2*(2z-x)*z -- blowup both singularities
R = ZZ/32003[x,y,z]
curve = ideal((x^2+y^2-3*x*z)^2 -4*x^2*(2*z-x)*z)
sings = radical saturate(ideal(singularLocus(curve)), ideal (vars R))
decompose sings -- there is a tacnode at (0:0:1) and a cusp at (1:0:1) 
-- we blow up P2 at both points. 
RI = reesIdeal(sings) 
S = ring RI
totalTransform = substitute(curve, S) + RI
D = decompose totalTransform -- the components are the proper transform of the curve and two exceptional curves
singular = ideal(singularLocus(D_0));
SL = saturate(singular, ideal(x,y,z));
J = saturate(SL, ideal(w_0,w_1))

-- we resolved the cusp, but need a second blow-up to resolve the tacnode (at a point on the exceptional divisor). 
 
RJ = reesIdeal(J, Variable => v)
SJ = ring RJ
totalTransform = substitute(D_0, SJ) + RJ
D = decompose totalTransform -- the components are the next proper transform and the new exceptional curve.
-- the second blow-up desingularizes the original curve.
singular = ideal(singularLocus(D_0));
SL = saturate(singular, ideal(x,y,z));
J = saturate(SL, ideal(w_0,w_1))
J2 = saturate(J, ideal(v_0,v_1, v_2))

*}

{*
--- Example of non-distinguished components to test distinguished code.
restart 
loadPackage "ReesAlgebra"
T=ZZ/101[c,d]
D = 4
P = product(D, i -> random(1,T))
R = ZZ/101[a,b,c,d]
I = ideal(a^2, a*b*(substitute(P,R)), b^2)
ass I -- there is one minimal associated prime (a thick line in PP^3) and D embedded primes (points on the line) 
primaryDecomposition I
distinguished(I) -- only the minimal prime is a distinguished component
K = distinguishedAndMult(I) -- get multiplicity 2 
intersect apply(K, i-> i_1^(i_0)) -- checks the Geometric Nullstellensatz on Ein-Lazarsfeld
I
decompose I
*}

{*
R=ZZ/32003[x,y,z]
I=intersect(ideal(x),(ideal(x,y))^2, (ideal(x,y,z))^3)
ass I
distinguished I
K = distinguishedAndMult I
intersect apply(K, i-> i_1^(i_0)) 
*}



{*
-- Check multiplicities of the distinguished components versus the effective Nullstellenstaz

n = 5
S = ZZ/101[u,v]
R = ZZ/101[x_0..x_3]
f=map(S, R, matrix {{u^n, u^2, u*v,v}})
I = kernel f
*}

///
T. Roemer,  "Homological Properties of Bigraded Modules"
Römer, Tim(D-ESSN)
Homological properties of bigraded algebras. (English summary) 
Illinois J. Math. 45 (2001), no. 4, 1361--1376. 
 Thm 5.3
shows that if i is and ideal in the polynomial ring,
generated in degree d (and maybe i is 
primary to the maximal ideal) then
  reg(I^j) = jd + b for m>-=j0
where j0 is the max degree in the "new variables" of
a bigeneric initial ideal of reesIdeal(i)
(bigeneric means we allow general changes of coords in
the new vars alone and in the old vars alone.)

Eisenbud and Ulrich have shown that there is a similar bound
in terms of the regularity with respect to the variables y
(graded with the degrees of the generators of i). This is proven
only in the case of ideals generated in a single degree and
primary to the maximal ideal. 

Research Problem: what's the situation in general?
///


end
restart
installPackage "ReesAlgebra"
viewHelp installPackage
viewHelp ReesAlgebra
