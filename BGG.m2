newPackage(
	"BGG",
    	Version => "0.2", 
    	Date => "June 30, 2008",
    	Authors => {
	     {Name => "Hirotachi Abo", Email => "abo@uidaho.edu", HomePage => "http://www.webpages.uidaho.edu/~abo/"},
	     {Name => "Wolfram Decker", Email => "decker@math.uni-sb.de", HomePage => "http://www.math.uni-sb.de/ag/decker/"},
	     {Name => "David Eisenbud", Email => "de@msri.org", HomePage => "http://www.msri.org/~de/"},	     
	     {Name => "Frank Schreyer", Email => "schreyer@math.uni-sb.de", HomePage => "http://www.math.uni-sb.de/ag/schreyer/"},
	     {Name => "Gregory G. Smith", Email => "ggsmith@mast.queensu.ca", HomePage => "http://www.mast.queensu.ca/~ggsmith/"},
	     {Name => "Mike Stillman", Email => "mike@math.cornell.edu", HomePage => "http://www.math.cornell.edu/~mike/"}
	     },
    	Headline => "Bernstein-Gelfand-Gelfand correspondence",
    	DebuggingMode => true
    	)

needsPackage "BoijSoederberg"

export {
     symExt, bgg, tateResolution, beilinson, UU, cohomologyTable
     }

symExt = method()
symExt(Matrix, PolynomialRing) := Matrix => (m,E) ->(
     ev := map(E,ring m,vars E);
     mt := transpose jacobian m;
     jn := gens kernel mt;
     q  := vars(ring m)**id_(target m);
     ans:= transpose ev(q*jn);
     --now correct the degrees:
     map(E^{(rank target ans):1}, E^{(rank source ans):0}, 
         ans));

bgg = method()
bgg(ZZ,Module,PolynomialRing) := Matrix => (i,M,E) ->(
     S :=ring(M);
     numvarsE := rank source vars E;
     ev:=map(E,S,vars E);
     f0:=basis(i,M);
     f1:=basis(i+1,M);
     g :=((vars S)**f0)//f1;
     b:=(ev g)*((transpose vars E)**(ev source f0));
     --correct the degrees (which are otherwise wrong in the transpose)
     map(E^{(rank target b):i+1},E^{(rank source b):i}, b));

tateResolution = method(TypicalValue => ChainComplex)
tateResolution(Matrix, PolynomialRing, ZZ, ZZ) := ChainComplex => (m,E,loDeg,hiDeg)->(
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

--sheafCohomology = method()
--sheafCohomology = (m,E,loDeg,hiDeg)->(
--     T := tateResolution(m,E,loDeg,hiDeg);
--     k := length T;
--     d := k-hiDeg+loDeg;
--     if d > 0 then 
--        chainComplex apply(d+1 .. k, i->T.dd_(i))
--     else T);

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


tateToCohomTable = (T) -> (
     C := betti T;
     n := max apply(keys C, (i,d,d1) -> i-d1);
     new CohomologyTally from apply(keys C, (i,d,d1) -> (
	       ((n-(i-d1), -d1), C#(i,d,d1))
	       ))
     )

cohomologyTable = method(TypicalValue => CohomologyTally)
cohomologyTable(CoherentSheaf, ZZ, ZZ) := CohomologyTally => (F,lo,hi) -> (
     M := module F;
     S := ring M;
     E := (coefficientRing S)[Variables=>numgens S, SkewCommutative=>true];
     T := tateResolution(presentation M, E, lo, hi);
     tateToCohomTable T
     )
cohomologyTable(Matrix, PolynomialRing, ZZ, ZZ) := CohomologyTally => (m,E,lo,hi) -> (
     T := tateResolution(m, E, lo, hi);
     tateToCohomTable T
     )


beginDocumentation()

document { 
     Key => {symExt,(symExt,Matrix,PolynomialRing)}, 
     Headline => "the first differential of the complex R(M)",
     Usage => "symExt(m,E)",
     Inputs => {
	  "m" => Matrix => "a presentation matrix for a positively graded module M over a polynomial ring",
	  "E" => PolynomialRing => "exterior algebra"
	  },
     Outputs => {
	  Matrix => {"a matrix representing the map ",  TT "M_1 ** omega_E <-- M_0 ** omega_E"}  
	  },
     "This function takes as input a matrix ", TT "m", " with linear entries, which we think of as 
     a presentation matrix for a positively graded ", TT "S", "-module ", TT "M", " matrix representing 
     the map " , TT "M_1 ** omega_E <-- M_0 ** omega_E", " which is the first differential of 
     the complex ", TT "R(M)",    ".", 
     EXAMPLE lines ///
	  S = ZZ/32003[x_0..x_2]; 
	  E = ZZ/32003[e_0..e_2, SkewCommutative=>true];
	  M = coker matrix {{x_0^2, x_1^2}};
	  m = presentation truncate(regularity M,M);
	  symExt(m,E)
     	  ///,
     Caveat => "This function is a quick-and-dirty tool which requires little computation. However 
     if it is called on two successive truncations of a module, then the maps it produces may NOT 
     compose to zero because the choice of bases is not consistent.",   
     SeeAlso => {bgg}
     }

document { 
     Key => {bgg,(bgg,ZZ,Module,PolynomialRing)}, 
     Headline => "the ith differential of the complex R(M)",
     Usage => "bgg(i,M,E)",
     Inputs => {
	  "i" => ZZ => "the cohomological index",
	  "M" => Module => {"graded ", TT "S", "-module"},  
	  "E" => PolynomialRing => "exterior algebra"
	  },
     Outputs => {
	  Matrix => {"a matrix representing the ith differential"}  
	  },
     "This function takes as input an integer ", TT "i", " and a finitely generated graded ", TT "S", 
     "-module ", TT "M", ", and returns the ith map in ", TT "R(M)", ", which is an adjoint 
     of the multiplication map between ", TT "M_i", " and ", TT "M_{i+1}", ".",    
     EXAMPLE lines ///
	  S = ZZ/32003[x_0..x_2]; 
	  E = ZZ/32003[e_0..e_2, SkewCommutative=>true];
	  M = coker matrix {{x_0^2, x_1^2, x_2^2}};
	  bgg(1,M,E)
	  bgg(2,M,E)
     	  ///,
     SeeAlso => {symExt}
     }

document { 
     Key => {tateResolution,(tateResolution, Matrix,PolynomialRing,ZZ,ZZ)}, 
     Headline => "finite piece of the Tate resolution",
     Usage => "tateResolution(m,E,l,h)",
     Inputs => {
	  "m" => Matrix => "a presentation matrix for a module",
	  "E" => PolynomialRing => "exterior algebra",
	  "l" => ZZ => "lower cohomological degree", 
	  "h" => ZZ => "upper bound on the cohomological degree"
	  },
     Outputs => {
	  ChainComplex => {"a finite piece of the Tate resolution"}  
	  },
     "This function takes as input a presentation matrix ", TT "m", " of a finitely generated graded "
     , TT "S", "-module ", TT "M", " an exterior algebra ", TT "E", " and two integers ", TT "l", 
     " and ", TT "h", ". If ", TT "r", " is the regularity of ", TT "M", ", then this function 
     computes the piece of the Tate resolution from cohomological degree ", TT "l", 
     " to cohomological degree ", TT "max(r+2,h)", ". For instance, for the homogeneous 
     coordinate ring of a point in the projective plane:",  
     EXAMPLE lines ///
	  S = ZZ/32003[x_0..x_2]; 
	  E = ZZ/32003[e_0..e_2, SkewCommutative=>true];
	  m = matrix{{x_0,x_1}};
	  regularity coker m
	  T = tateResolution(m,E,-2,4)
	  betti T
	  T.dd_1
     	  ///,
     SeeAlso => {symExt}
     }

end
document { 
     Key => {cohomologyTable,(cohomologyTable,Matrix,PolynomialRing,ZZ,ZZ),(cohomologyTable,CoherentSheaf,ZZ,ZZ)}, 
     Headline => "dimensions of cohomology groups",
     Usage => "cohomologyTable(m,E,l,h) or cohomologyTable(F,l,h)",
     Inputs => {
	  "m" => Matrix => "a presentation matrix for a module",
	  "E" => PolynomialRing => "exterior algebra",
	  "l" => ZZ => "lower cohomological degree", 
	  "h" => ZZ => "upper bound on the cohomological degree",
	  "F" => CoherentSheaf => "a coherent sheaf on a projective scheme"
	  },
     Outputs => {
	  CohomologyTable => {"dimensions of cohomogy groups"}  
	  },
     "This function takes as input a presentation matrix ", TT "m", " of a finitely generated graded "
     , TT "S", "-module ", TT "M", " an exterior algebra ", TT "E", " and two integers ", TT "l", 
     " and ", TT "h", ". If ", TT "r", " is the regularity of ", TT "M", ", then this function 
     computes the piece of the Tate resolution from cohomological degree ", TT "l", 
     " to cohomological degree ", TT "max(r+2,h)", ". For instance, for the homogeneous 
     coordinate ring of a point in the projective plane:",  
     EXAMPLE lines ///
	  S = ZZ/32003[x_0..x_2]; 
	  E = ZZ/32003[e_0..e_2, SkewCommutative=>true];
	  PP2 = Proj S; 
	  F = OO_PP2
          cohomologyTable(F,10,5)
     	  ///,
     SeeAlso => {symExt}
     }

end
uninstallPackage "BGG"
restart
path = append(path, homeDirectory | "Snowbird/")
installPackage("BGG", UserMode => true) 

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
