newPackage(
	"BGG0",
    	Version => "0.1", 
    	Date => "June 23, 2008",
    	Authors => {
	     {Name => "David Eisenbud", Email => "de@msri.org", HomePage => "http://www.msri.org/~de/"},
	     {Name => "Wolfram Decker", Email => "", HomePage => ""},	     
	     {Name => "Frank Schreyer", Email => "", HomePage => ""},
	     {Name => "Mike Stillman", Email => "", HomePage => ""}
	     },
    	Headline => "Bernstein-Gelfand-Gelfand correspondence",
    	DebuggingMode => true
    	)

needsPackage "BoijSoderberg"

export {
     symExt, bgg, tateResolution, sheafCohomology, beilinson, UU,
     cohomologyTable, cohomologyTable1
     }

symExt = (m,E) ->(
     ev := map(E,ring m,vars E);
     mt := transpose jacobian m;
     jn := gens kernel mt;
     q  := vars(ring m)**id_(target m);
     ans:= transpose ev(q*jn);
     --now correct the degrees:
     map(E^{(rank target ans):1}, E^{(rank source ans):0}, 
         ans));

bgg = (i,M,E) ->(
     S :=ring(M);
     numvarsE := rank source vars E;
     ev:=map(E,S,vars E);
     f0:=basis(i,M);
     f1:=basis(i+1,M);
     g :=((vars S)**f0)//f1;
     b:=(ev g)*((transpose vars E)**(ev source f0));
     --correct the degrees (which are otherwise
     --wrong in the transpose)
     map(E^{(rank target b):i+1},E^{(rank source b):i}, b));

tateResolution = (m,E,loDeg,hiDeg)->(
     M := coker m;
     reg := regularity M;
     bnd := max(reg+1,hiDeg-1);
     mt  := presentation truncate(bnd,M);
     o   := symExt(mt,E);
     --adjust degrees, since symExt forgets them
     ofixed   :=  map(E^{(rank target o):bnd+1},
                E^{(rank source o):bnd},
                o);
     res(coker ofixed, LengthLimit=>max(1,bnd-loDeg+1)));

sheafCohomology = (m,E,loDeg,hiDeg)->(
     T := tateResolution(m,E,loDeg,hiDeg);
     k := length T;
     d := k-hiDeg+loDeg;
     if d > 0 then 
        chainComplex apply(d+1 .. k, i->T.dd_(i))
     else T);

sortedBasis = (i,E) -> (
     m := basis(i,E);
     p := sortColumns(m,MonomialOrder=>Descending);
     m_p);

beilinson1=(e,dege,i,S)->(
     E := ring e;
     mi := if i < 0 or i >= numgens E then map(E^1, E^0, 0)
           else if i === 0 then id_(E^1)
           else sortedBasis(i+1,E);
     r := i - dege;
     mr := if r < 0 or r >= numgens E then map(E^1, E^0, 0)
           else sortedBasis(r+1,E);
     s = numgens source mr;
     if i === 0 and r === 0 then
          substitute(map(E^1,E^1,{{e}}),S)
     else if i>0 and r === i then substitute(e*id_(E^s),S)
     else if i > 0 and r === 0 then
          (vars S) * substitute(contract(diff(e,mi),transpose mr),S)
     else substitute(contract(diff(e,mi), transpose mr),S));

UU = (i,S) -> (
     if i < 0 or i >= numgens S then S^0
     else if i === 0 then S^1
     else cokernel koszul(i+2,vars S) ** S^{i});

beilinson = (o,S) -> (
     coldegs := degrees source o;
     rowdegs := degrees target o;
     mats = table(numgens target o, numgens source o,
              (r,c) -> (
                   rdeg = first rowdegs#r;
                   cdeg = first coldegs#c;
                   overS = beilinson1(o_(r,c),cdeg-rdeg,cdeg,S);
                   -- overS = substitute(overE,S);
                   map(UU(rdeg,S),UU(cdeg,S),overS)));
     if #mats === 0 then matrix(S,{{}})
     else matrix(mats));

cohomologyTable = method()
cohomologyTable1 = method()

cohomologyTable1(CoherentSheaf, ZZ, ZZ) := (F,lo,hi) -> (
     -- this is the stoopid version
     n := numgens ring F - 1;
     L := flatten (
       for i from 0 to n list
         for d from lo-i to hi-i list
	      ((i,d),rank HH^i(F(d)))
	 );
     new CohomologyTally from select(L, (k,v) -> v != 0)
     )

tateToCohomTable = (T) -> (
     C := betti T;
     n := max apply(keys C, (i,d,d1) -> i-d1);
     new CohomologyTally from apply(keys C, (i,d,d1) -> (
	       ((n-(i-d1), -d1), C#(i,d,d1))
	       ))
     )

cohomologyTable(CoherentSheaf, ZZ, ZZ) := (F,lo,hi) -> (
     M := module F;
     S := ring M;
     E := (coefficientRing S)[Variables=>numgens S, SkewCommutative=>true];
     T := tateResolution(presentation M, E, lo, hi);
     tateToCohomTable T
     )

beginDocumentation()

end

restart
loadPackage "BGG0"
loadPackage "BoijSoderberg"
loadPackage "SchurFunctors"

kk = ZZ/32003
S = kk[x_0..x_2]
E = kk[e_0..e_2, SkewCommutative=>true]

M = ker vars S
N = coker schur({2,1},syz vars S);
betti res N
poincare N
apply(-10..10, d -> hilbertFunction(d,N))
res N
betti oo
tateResolution(presentation N, E, -5, 5)
betti oo
F = sheaf N
cohomologyTable(F, -5, 5)

HH^0(F)
HH^0(F(1))
HH^0(F(2))
HH^0(F(3))
HH^0(F(4))

HH^1(F)
HH^1(F(1))
HH^1(F(2))
HH^1(F(3))
HH^1(F(4))

HH^2(F(-2))
HH^2(F(-1))
HH^2(F)
HH^2(F(1))
HH^2(F(2))
HH^2(F(3))
HH^2(F(4))


hilbertPolynomial(F, Projective=>false)
factor oo
3 * pureCohomologyTable({2,0},-5,5)

cohomologyTable(CoherentSheaf, ZZ, ZZ) := (F,lo,hi) -> (
     -- this is the stoopid version
     n := numgens ring F - 1;
     new CohomologyTally from flatten (
     for i from 0 to n list
       for d from lo-i to hi-i list ((i,d) => rank HH^i(F(d)))
     ))

tateToCohomTable = (T) -> (
     C := betti T;
     n := max apply(keys C, (i,d,d1) -> i-d1);
     new CohomologyTally from apply(keys C, (i,d,d1) -> (
	       (n-(i-d1), -d1)
	       ))
     )
time cohomologyTable(F,-5,5)

betti tateResolution(presentation N, E, -5, 5)
peek oo
