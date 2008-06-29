newPackage(
     "Bruns",
     Version => "2.0",
     Date => "June 28, 2008",
     Authors =>{{Name => "David Eisenbud",
	       Email => "de@msri.org",
	       HomePage=>"http://www.msri.org/~de"}},
     Headline => "make a 3-generator ideal with an \"any\" resolution",
     DebuggingMode => true
     )
loadPackage "SimpleDoc"
export{isSyzygy, elementary, evansGriffith, bruns}

isSyzygy=method(TypicalValue=>Boolean)
isSyzygy(Matrix,ZZ) := (f,d)->(
     --tests whether coker f is a d-th syzygy
     --You would THINK that the LenghtLimit bounds below 
     --would SPEED things up, but
     --in fact they SLOW things a little, at least in the example below.
--     F:=res (coker transpose f, LengthLimit => d+1);
--     G:=res (coker transpose F.dd_(d+1), LengthLimit=>d+1);
     F:=res coker transpose f;
     G:=res coker transpose F.dd_(d+1);
     value:=true;
     for i from 2 to d+1 do value = value and 
          sort flatten degrees G_i == sort(-flatten degrees F_(d+1-i));
     value
     )
isSyzygy(Module, ZZ):=(M,d)->(
     f:=presentation M;
     isSyzygy(f,d)
     )

EXAMPLE lines///
S=kk[a..e]
F=res (ideal vars S)^2
isSyzygy(F.dd_3,3)==false
isSyzygy(F.dd_4,3)==true
///


elementary=method(TypicalValue=>Matrix)
elementary(Matrix, ZZ, ZZ) := (f,k,m)->(
     --Takes a matrix f, an integer k whose value is strictly less than the 
     --number of rows of f, and a positive  integer m  The routine
     --adds rand multiples of the last row, whose coefficients are polynomials
     --in the first m variables,  to the k preceding rows
     --and drops the last row. For this to be effective, the target degrees of f
     --must be in ascending order.
     S:=ring f;
     L  :=-flatten degrees target f;
     b := #L;
     if k>=b then error("value of k is too large");
     L0 :=L_{b-1};
     L1 :=L_{0..b-2};
     L2 :=L_{0..b-2-k};
     L3 :=L_{b-1-k..b-2};
     m11 := map(S^L1,S^L1,(i,j)-> if i==j then 1_S else 0_(ring f));
     m12 := map(S^L2,S^L0,(i,j)->0_(ring f));
     Sk=(coefficientRing S)[S_0..S_(m-1)];
     m22k:=random(Sk^L3, Sk^L0);
     m22:=substitute(m22k, S);
--     g:=transpose gens ideal (vars S)_{0..m-1};
--     m22 := random(S^L3, (target g)**S^L0) * (map((target g)**S^L0, (source g)**S^L0, g));
--     m22 := random(S^L3,S^L0);
--    error("debug");
     (m11|(m12||m22))*f
     )


evansGriffith = method(TypicalValue => Matrix)
evansGriffith(Matrix, ZZ) := (f,n)->(
     --f must be a matrix over a polynomial ring S
     --whose cokernel is an n-th syzygy.
     --The result f1=evansGriffith(f,n) 
     --is a matrix with the same source and kernel as f but
     --such that coker f1 is an nth syzygy of rank n.
     --rank target f1 = (rank f)+n. 
     --The routine reduces the target of f by elementary moves 
     --involving just n+1 variables.
     --The outcome is probabalistic, but if the routine fails, it 
     --gives an error message.
     N:=numgens ring f;
     f1:=transpose sort(transpose f, DegreeOrder=>Descending); -- this is f with rows sorted so that the degrees are ascending.
     if flatten degrees target f1 =!= sort flatten degrees target f then error("target degrees not ascending");
     if not isSyzygy(f1,n) then error("cokernel of input matrix is not an appropriate syzygy");
     r:=rank f1;
     b:=rank target f1;
     loopcount=0;
     while r+n<b do(
	  j:=0;
	  ftemp=elementary(f1,j,n+1);
	  while (rank ftemp =!= r or not isSyzygy(ftemp,n)) do(
	       if j<b-1 then j=j+1 
	            else (loopcount=loopcount+1; 
			 print(loopcount);
			 if loopcount>5 then error("Transformation is not random enough");
			 );
		    	       ftemp=elementary(f1,j, n+1));
	 b=b-1;
	 f1=ftemp);
    f1)


bruns = method(TypicalValue => Ideal)
bruns Matrix := f->(
     --given a matrix f, whose cokernel is a 2-rd syzygy,
     --bruns f returns a 3-generator ideal whose second syzygy is the image of f
     f1:=evansGriffith(f,2);
     FF:=res coker(transpose f1);
     g:=transpose FF.dd_2;
     --the row degrees of g are in the reverse order for bruns 1, so reverse them
     Lsource := flatten degrees source g;
     Ltar := flatten degrees target g;
     grev=map((ring g)^(-reverse Ltar), (ring g)^(-Lsource), g^(reverse splice {0..#Ltar-1}));
     h:=evansGriffith(grev,1);
     KK:=res coker transpose h;
     ideal transpose KK.dd_2)

bruns Module := M->(
     --Given a module M that is at least a 3rd syzygy, 
     --the function returns a 3-generator ideal with 2nd syzygy
     --isomorphic to M.
     --It does this by constructing a matrix f whose image is M and 
     --whose cokernel is a second syzygy, and then calling 
     --bruns f.
ff:=presentation M;
ft:= syz transpose ff;
bruns transpose ft)

beginDocumentation()
document { 
	Key => Bruns,
	Headline => " \"Every\" free resolution is the resolution of a 3-generator ideal",
	EM "a package of functions for transforming syzygies"}
doc ///
Key
  bruns
Headline
  Makes 3-generator ideal whose 2nd syz is a given 3rd syzygy
Usage
 j= bruns M \n  j= bruns f
Inputs
  M:Module
    M is a third syzygy (graded)
  f:Matrix
    f is a matrix whose cokernel is a second syzygy (graded)
Outputs
  j:Ideal
   j is a homogeneous three-generator ideal whose second syzygy is M, or image f.
Description
  Text
    A famous paper of Winfried Bruns is called
   {\bf  ``Jede'' freie Aufl\"osung ist
    freie Aufl\"osung eines drei-Erzeugenden Ideals} (Journal reference).
    More precisely, Bruns shows that every 3rd syzygy is the 2nd syzygy
    of a three generator ideal. This function takes a graded module M over a polynomial ring S that
    is a third syzygy, and returns a three-generator ideal j whose second syzygy is M, 
    so that the resolution of S/j, from the third step, is isomorphic to the resolution of M.
    Alternately {\tt bruns} takes
    a matrix whose cokernel is a second syzygy, and finds a 3-generator
    ideal whose 2nd syzygy is the image of that matrix.
  Example
    kk=ZZ/32003
    S=kk[a..d]
    i=ideal(a^2,b^3,c^4, d^5)
    betti (F=res i)
    M = image F.dd_3
    f=F.dd_3
    j=bruns M;
    betti res j 
    j1=bruns f; 
    betti res j1  
  Text
    The general context of this result uses the theory of ``basic elements'', a
    commutative algebra version of the general position arguments of the algebraic
    geometers. The ``Syzygy Theorem'' of Evans and Griffiths (**citation**) asserts that if
    a module M over a regular local ring S containing a field (the field is conjecturally not
    necessary), or a graded modules over polynomial ring S, is a k-th syzygy but not a free module,
    then M has rank at least k. The theory of basic elements shows that if M is a k-th syzygy
    of rank >k, then for a ``sufficiently general'' element m of M the module M/Sm is again
    a k-th syzygy. 

    The idea of Bruns theorem is if M is a second syzygy, then factoring out rank M - 2 general elements gives
    a second syzygy N of rank 2. It turns out that 3 general homomorphisms from M to S together
    embed N in S^3 in such a way that the quotient S^3/N is a three generator ideal.

    This is the method implemented in this package.
    ///

end 

restart
installPackage ("Bruns", UserMode=>true)
--loadPackage "Bruns"
viewHelp Bruns

--brunsification of a complete intersection
kk=ZZ/32003
S=kk[a..e]
i=ideal(a^2,b^3,c^4, d^5)
betti (F=res i)
F.dd_4
time (j=bruns coker F.dd_4)
betti res j
time j=bruns image F.dd_3;
betti res j
f=F.dd_3
time j=bruns f; -- 25 sec on macbook pro
betti gens j
betti res j 
time (f1=evansGriffith(f,3);)
time (f1=evansGriffith(f,2);)



kk=ZZ/32003
S=kk[x_0..x_5]
i=ideal (vars S)^[2]
--i=(ideal(vars S))^2
betti (F=res i)
f=F.dd_(codim i-1)
isSyzygy(f, 4) --true
betti res coker f

evansGriffith(f,2)
time j=bruns f;

betti (G=res j) 
r=rank G.dd_3
j3=minors(r,G.dd_3);
codim j3==3

restart
loadPackage "Bruns"
kk=ZZ/32003
S=kk[a..f]
m=matrix"a,b,c,d,e,0;0,a,b,c,d,e"
n=transpose syz m
time j= bruns n; -- 20 sec on macbook pro
betti (G=res j)
r=rank G.dd_3

---

S=QQ[a,b,c,d]
j=ideal"b2d2+d4,b2c2+a2d2+c2d2,b4-b2d2-d4"
betti (G=res j)
codim minors(3, G.dd_3)
bruns G.dd_4

--try a small field
kk=ZZ/2
S=kk[a..e]
i=ideal(a^2,b^3,c^4, d^5)
betti (F=res i)
f=F.dd_3;
time f1=evansGriffith(f,2);
time j=bruns f;

--5 variables
kk=ZZ/101
S=kk[a..e]
i=ideal(a^3,b,c,d,e)
betti (F=res i)
f=F.dd_4;
--time f1=evansGriffith(f,2);
time j=bruns f;
betti res j
--(ass j)/codim
k=top j;
betti res k

--brunsification of a monomial curveideal
kk=ZZ/32003
S=kk[a..e]
i=monomialCurveIdeal(S, {1,3,6,7})
betti (F=res i)
--          0: 1 .  . . .
--          1: . 2  . . .
--          2: . 3  5 1 .
--          3: . 1  6 7 2
time j=bruns F.dd_3
--229 sec v 2.0 does it in 60 sec
betti res j
--          0: 1 . . . .
--          1: . . . . .
--          2: . . . . .
--          3: . . . . .
--          4: . . . . .
--          5: . . . . .
--          6: . . . . .
--          7: . 3 . . .
--          8: . . . . .
--          9: . . . . .
--         10: . . . . .
--         11: . . . . .
--         12: . . . . .
--         13: . . 5 1 .
--         14: . . 3 7 2



--Oddity: setting LengthLimit slows things down instead of speeding them up. 
--this used to run MUCH more slowly!
restart 
loadPackage "Bruns"
S=kk[a..e]
i=ideal(a^2,b^3,c^4, d^5)
betti (F=res i)
f=F.dd_3
f1=elementary(f,3,5);
g=transpose syz transpose f1;
time FF=res (coker transpose g, LengthLimit=>2)
betti FF
time GG=res (coker transpose FF.dd_2, LengthLimit=>2)
--237 sec -- 2008: now 1.7 sec
time GG=res (coker transpose FF.dd_2)
-- 55 seconds -- now 1.09 sec                                                                      

restart
--how to make a matrix whose elements are random elements of a given ideal I
S=kk[a..e]
L0 = {-6}
L3={-2,-3,-4,-5}
I=ideal (vars S)_{0,1})^2
g=transpose gens I
random(S^L3, (target g)**S^L0) * (map((target g)**S^L0, (source g)**S^L0, g))
betti oo


----------------------

