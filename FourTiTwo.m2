----------------------------------------------------
----------------------------------------------------
-- previous version: 0.2 30Jun08, submitted by Josephine Yu.
-- author: Mike Stillman -- 
--     	    	      	   core
-- author: Josephine Yu -- 
--     	    	      	   all remaining functions; documentation
-- editor: Sonja Petrovic -- 
--     	    	      	   interface for windows; edited documentation; tests
--     	    	      	   
-- latest update: 2Jul08
----------------------------------------------------
----------------------------------------------------

newPackage(
	"FourTiTwo",
    	Version => "0.3", 
    	Date => "July 2, 2008",
    	Authors => {
	     {Name => "Mike Stillman", Email => "mike@math.cornell.edu", HomePage => ""},
	     {Name => "Josephine Yu", Email => "jyu@math.mit.edu", HomePage => ""},
	     {Name => "Sonja Petrovic", Email => "petrovic@ms.uky.edu", HomePage => ""}
	     },
    	Headline => "Interface to 4ti2",
	Configuration => { "path" => "",
	     "keep files" => true
	      },
    	DebuggingMode => true
    	)

export {
     toBinomial,
     getMatrix,
     putMatrix,
     markovBasis,
     toricGB,
     circuits,
     graverBasis,
     hilbertBasis,
     rays,
     InputType
     }


path'4ti2 = (options FourTiTwo).Configuration#"path"
-- NOTE: the absolute path should be put into the .init file for 4ti2 inside the .Macaulay2 directory.


-- the following command is necessary to be run under windows-cygwin:
-- externalPath = value Core#"private dictionary"#"externalPath"
-- Note: outside of cygwin (linux/mac), this string is just the null string. 
-- But under Windows machines this is necessary (the value of the string is C:/cygwin).
externalPath = replace("/","\\",value Core#"private dictionary"#"externalPath")
-- Without this command, the temporary files won't be found and there will be a ton of error messages.


getFilename = () -> (
     filename := temporaryFileName();
     while fileExists(filename) or fileExists(filename|".mat") or fileExists(filename|".lat") do filename = temporaryFileName();
     filename)

putMatrix = method()
putMatrix(File,Matrix) := (F,B) -> (
     B = entries B;
     numrows := #B;
     numcols := #B#0;
     F << numrows << " " << numcols << endl;
     for i from 0 to numrows-1 do (
	  for j from 0 to numcols-1 do (
	       F << B#i#j << " ";
	       );
	  F << endl;
	  );
     )

getMatrix = method()
getMatrix String := (filename) -> (
     L := lines get filename;
     l := toString first L;
     v := value("{" | replace(" +",",",l)|"}"); 
     dimensions := select(v, vi -> vi =!= null);
     if dimensions#0 == 0 then ( -- matrix has no rows
	  matrix{{}}
     ) else(
     	  L = drop(L,1);
     	  --L = select(L, l-> regex("^[:space:]*$",l) === null);--remove blank lines
     	  matrix select(
	       apply(L, v -> (w := value("{" | replace(" +",",",v)|"}"); w = select(w, wi -> wi =!= null))),
	       row -> row =!= {}
     	       ) 
     ))    

toBinomial = method()
toBinomial(Matrix,Ring) := (M,S) -> (
     toBinom := (b) -> (
       pos := 1_S;
       neg := 1_S;
       scan(#b, i -> if b_i > 0 then pos = pos*S_i^(b_i)
                   else if b_i < 0 then neg = neg*S_i^(-b_i));
       pos - neg);
     ideal apply(entries M, toBinom)
     )

markovBasis = method(Options=> {InputType => null})
markovBasis Matrix := Matrix => o -> (A) -> (
     filename := getFilename();
     << "using temporary file name " << filename << endl;
     if o.InputType === "lattice" then
     	  F := openOut(filename|".lat")
     else 
       	  F = openOut(filename|".mat");
     putMatrix(F,A);
     close F;
     execstr = path'4ti2|"markov -q " |externalPath |filename; --added externalPath
     -- execstr = path'4ti2|"4ti2int32 markov -q "|filename; -- for windows!!! (if not w/ cygwin)
     ret := run(execstr);
     if ret =!= 0 then error "error occurred while executing external program 4ti2: markov";
     getMatrix(filename|".mar")
     )
--markovBasis(Matrix,Ring) := o -> (A,S) -> toBinomial(markovBasis(A,o), S)

toricGB = method(Options=>{Weights=>null})
toricGB Matrix := o -> (A) -> (
     filename := getFilename();
     << "using temporary file name " << filename << endl;
     F := openOut(filename|".mat");
     putMatrix(F,A);
     close F;
     if o.Weights =!= null then (
	  cost = concatenate apply(o.Weights, x -> (x|" "));
	  (filename|".cost") << "1 " << #o.Weights << endl << cost << endl  << close;
	  );
     execstr = path'4ti2|"groebner -q "|externalPath|filename; 
          -- execstr command changed to incorporate cygwin options (added string externalPath)
     ret := run(execstr);
     if ret =!= 0 then error "error occurred while executing external program 4ti2: groebner";
     getMatrix(filename|".gro")
     )
toricGB(Matrix,Ring) := o -> (A,S) -> toBinomial(toricGB(A,o), S)

circuits = method()
circuits Matrix := Matrix => (A ->(
     filename := getFilename();
     << "using temporary file name " << filename << endl;
     F := openOut(filename|".mat");
     putMatrix(F,A);
     close F;
     execstr = path'4ti2|"circuits -q " | externalPath | filename;--added externalPath
     ret := run(execstr);
     if ret =!= 0 then error "error occurred while executing external program 4ti2: circuits";
     getMatrix(filename|".cir")
     ))

graverBasis = method()
graverBasis Matrix := Matrix => (A ->(
     filename := getFilename();
     << "using temporary file name " << filename << endl;
     F := openOut(filename|".mat");
     putMatrix(F,A);
     close F;
     execstr = path'4ti2|"graver -q " | externalPath | filename;
     ret := run(execstr);
     if ret =!= 0 then error "error occurred while executing external program 4ti2: graverBasis";
     getMatrix(filename|".gra")
     ))
graverBasis (Matrix,Ring) := Ideal => ((A,S)->toBinomial(graverBasis(A),S))

hilbertBasis = method(Options=> {InputType => null})
hilbertBasis Matrix := Matrix => o -> (A ->(
     filename := getFilename();
     << "using temporary file name " << filename << endl;
     if o.InputType === "lattice" then
     	  F := openOut(filename|".lat")
     else 
       	  F = openOut(filename|".mat");
     putMatrix(F,A);
     close F;
     execstr = path'4ti2|"hilbert -q " |externalPath | filename;
     ret := run(execstr);
     if ret =!= 0 then error "error occurred while executing external program 4ti2: hilbertBasis";
     getMatrix(filename|".hil")
     ))


rays = method()
rays Matrix := Matrix => (A ->(
     filename := getFilename();
     << "using temporary file name " << filename << endl;
     F := openOut(filename|".mat");
     putMatrix(F,A);
     close F;
     execstr = path'4ti2|"rays -q " |externalPath | filename;
     ret := run(execstr);
     if ret =!= 0 then error "error occurred while executing external program 4ti2: rays";
     getMatrix(filename|".ray")
     ))

-- SP: the output command interface
--output = method()



beginDocumentation()
needsPackage "SimpleDoc";

doc ///
     Key 
          FourTiTwo
     Headline
     	  Interface for 4ti2
     Description
          Text
	       Interfaces most of the functionality of the software {\tt 4ti2} available at  {\tt http://www.4ti2.de/}.
	        
	       A {\tt d\times n} integral matrix {\tt A} (with nonnegative entries) specifies a map from a polynomial 
	       ring in d variables to a polynomial ring with n variables by specifying exponents of the variables indexing
	       its columns. For example, if {\tt A} is a matrix <br>
	       3 2 1 0<br>
	       0 1 2 3<br>
	       the map from {\tt k[s,t]} to {\tt k[a,b,c,d]} is given by <br> 
	       {\tt (s,t)-> (s^3, s^2t,st^2,t^3)}. <br>
	       
	       The toric ideal I_A is the kernel of this map. 
	       It is minimally generated by the 2-minors of the matrix <br>
	       x y z<br>
	       y z w<br>
	       Given the matrix {\tt A}, one can compute its lattice basis ideal specified by the integral basis
	       of the lattice {\tt A}, the toric ideal I_A, its Groebner bases, etc. In practice, however, 
	       these are nontrivial computational tasks. 
	       The software 4ti2 is very efficient in computing these objects. 	      
	       
	       For more theoretical details (and more generality), see the standard reference: 
	       B. Sturmfels, {\bf Gr\"obner bases and convex polytopes.} 
	       American Mathematical Society, University Lectures Series, No 8, Providence, Rhode Island, 1996. 
	       
               {\bf Note for cygwin users:}  set the path for 4ti2 inside .Macaulay2/init-FourTiTwo.m2 
///;

doc ///
    Key
	getMatrix
	(getMatrix, String)
    Headline
	reads a matrix from a 4ti2 format input file
    Usage
	getMatrix s
    Inputs
    	s:String
	     file name
    Outputs
	A:Matrix
    Description
	Text
	     The file should contain a matrix in the format such as<br>
	     2 4<br>
	     1 1 1 1<br>
	     1 2 3 4<br>
	     The first two numbers are the numbers of rows and columns.
    SeeAlso
	putMatrix
///;

doc ///
     Key 
	  putMatrix
     	  (putMatrix,File,Matrix)
     Headline
     	  writes a matrix into a file formatted for 4ti2
     Usage
     	  putMatrix(F,A)
     Inputs
     	  F:File
       	  A:Matrix
     Description
     	  Text
		Write the matrix {\tt A} in file {\tt F} in 4ti2 format.
	  Example
		A = matrix "1,1,1,1; 1,2,3,4"
		s = temporaryFileName()
		F = openOut(s)
		putMatrix(F,A)
		close(F)
		getMatrix(s)
     SeeAlso
     	  getMatrix
///;

doc ///
     Key
          toBinomial
     	  (toBinomial, Matrix, Ring)	  
     Headline
     	  creates a toric ideal from a given exponents of its generators
     Usage
     	  toBinomial(M,R)
     Inputs
     	  M: Matrix
	  R: Ring
	       ring with as least as many generators as the columns of {\tt M}
     Outputs
     	  I: Ideal
     Description
     	  Text
	       Returns the ideal in the ring {\tt R} generated by the binomials corresponding to rows of {\tt M}
	  Example
	       A = matrix "1,1,1,1; 1,2,3,4"
	       B = syz A 
	       R = QQ[a..d]	     
	       toBinomial(transpose B,R)
///;

doc ///
     Key
     	  toricGB
          (toricGB, Matrix)
     	  (toricGB, Matrix, Ring)
     	  [toricGB, Weights]
     Headline
     	  calculates a Groebner basis of the toric ideal I_A, given A; equivalent to "groebner" in 4ti2
     Usage
     	  toricGB(A) or toricGB(A,R)
     Inputs
      	  A:Matrix    
	       whose columns parametrize the toric variety. The toric ideal I_A is the kernel of the map defined by {\tt A}.
     	  R:Ring
	       ring with as least as many generators as the columns of {\tt A}
     Outputs
     	  B:Matrix 
	       whose rows give binomials that form a Groebner basis of the toric ideal of {\tt A}
     	  I:Ideal
	       whose generators form a Groebner basis for the toric ideal
     Description
	  Example
	       A = matrix "1,1,1,1; 1,2,3,4"
	       toricGB(A)
	       R = QQ[a..d]
	       toricGB(A,R)
	       toricGB(A,Weights=>{1,2,3,4})
 ///;
 
 doc ///
     Key
     	  markovBasis
          (markovBasis, Matrix)
	  [markovBasis, InputType]
     Headline
     	  calculates a generating set of the toric ideal I_A, given A; equivalent to "markov" in 4ti2
     Usage
     	  markovBasis(A) or markovBasis(A, InputType => "lattice")
     Inputs
      	  A:Matrix
	       whose columns parametrize the toric variety; the toric ideal is the kernel of the map defined by {\tt A}.
	       Otherwise, if InputType is set to "lattice", the rows of {\tt A} are a lattice basis and the toric ideal is the 
	       saturation of the lattice basis ideal.	       
	  s:InputType
	       which is the string "lattice" if rows of {\tt A} specify a lattice basis
     Outputs
     	  B:Matrix 
	       whose rows form a Markov Basis of the lattice \{z integral : A z = 0\}
	       or the lattice spanned by the rows of {\tt A} if the option InputType => "lattice" is used
     Description
	  Example
	       R = QQ[a..d]
	       M = markovBasis(A)
      	       I = toBinomial(M,R)
     	       B = syz A
	       N = markovBasis(transpose B, InputType => "lattice")
	       J = toBinomial(N,R)-- markovBasis(transpose B, R, InputType => "lattice")
     	       I == J	       
///;

doc ///
     Key
     	  graverBasis
          (graverBasis, Matrix)
     	  (graverBasis, Matrix, Ring)
     Headline
     	  calculates the Graver basis of the toric ideal; equivalent to "graver" in 4ti2
     Usage
     	  graverBasis(A) or graverBasis(A,R)
     Inputs
      	  A:Matrix    
	       whose columns parametrize the toric variety. The toric ideal I_A is the kernel of the map defined by {\tt A}
     Outputs
     	  B:Matrix 
	       whose rows give binomials that form the Graver basis of the toric ideal of {\tt A}, or
     	  I:Ideal
	       whose generators form the Graver basis for the toric ideal
     Description
	  Example
	       A = matrix "1,1,1,1; 1,2,3,4"
	       graverBasis(A)
	       R = QQ[a..d]
	       graverBasis(A,R)
///;

doc ///
     Key
     	  hilbertBasis
          (hilbertBasis, Matrix)
	  [hilbertBasis, InputType]
     Headline
     	  calculates the Hilbert basis of the cone; equivalent to "hilbert" in 4ti2
     Usage
     	  hilbertBasis(A) or hilbertBasis(A, InputType => "lattice")
     Inputs
      	  A:Matrix    
	       defining the cone \{z : Az = 0, z >= 0 \}
     Outputs
     	  B:Matrix 
	       whose rows form the Hilbert basis of the cone \{z : Az = 0, z >= 0 \}      
	       or the cone \{z A : z is an integral vector and z A >= 0\} if {\tt InputType => "lattice"} is used
     Description
	  Example
	       A = matrix "1,1,1,1; 1,2,3,4"
	       B = syz A
	       hilbertBasis(transpose B)
     	       hilbertBasis(A, InputType => "lattice")     	       
///;


doc ///
     Key
     	  rays
          (rays, Matrix)
     Headline
     	  calculates the extreme rays of the cone; equivalent to "rays" in 4ti2
     Usage
     	  rays(A)
     Inputs
      	  A:Matrix   
	       defining the cone \{z : Az = 0, z >= 0 \}
     Outputs
     	  B:Matrix 
	       whose rows are the extreme rays of the cone \{z : Az = 0, z >= 0 \}
     Description
	  Example
	       A = matrix "1,1,1,1; 1,2,3,4"
	       B = syz A
	       rays(transpose B)
///;



doc ///
     Key
     	  circuits
          (circuits, Matrix)
     Headline
     	  calculates the circuits of the toric ideal; equivalent to "circuits" in 4ti2
     Usage
     	  circuits(A)
     Inputs
      	  A:Matrix    
               whose columns parametrize the toric variety. The toric ideal I_A is the kernel of the map defined by {\tt A} 
     Outputs
     	  B:Matrix 
	       whose rows form the circuits of A
     Description
	  Example
	       needsPackage "FourTiTwo"
	       A = matrix "1,1,1,1; 1,2,3,4"
	       circuits A
///;

doc ///
     Key
     	  InputType
     Description
          Text
     	      Put {\tt InputType => "lattice"} as a argument in the functions markovBasis and hilbertBasis
     SeeAlso
     	  markovBasis
	  hilbertBasis
///;


TEST/// 
  loadPackage "FourTiTwo"    --testing markovBasis w/ matrix inputt
  A = matrix "1,1,1,1; 1,2,3,4"
  M = markovBasis(A)
  R = QQ[x_0,x_1,x_2,x_3]
  I = toBinomial(M,R)
  Irnc3 = ideal(x_0*x_2-x_1^2,x_1*x_3-x_2^2,x_0*x_3-x_1*x_2)
  assert(I==Irnc3)
///
TEST ///   
  loadPackage "FourTiTwo"   --testing markovBasis w/ lattice input
  B = matrix "1,-2,1,0; 0,1,-2,1"
  M = markovBasis(B, InputType => "lattice")
  R = QQ[x_0,x_1,x_2,x_3]
  I = toBinomial(M,R)
  Irnc3 = ideal(x_0*x_2-x_1^2,x_1*x_3-x_2^2,x_0*x_3-x_1*x_2)
  assert(I== Irnc3)  
///
TEST ///     
  loadPackage "FourTiTwo"   --testing circuits
  R=CC[x_0,x_1,x_2,x_3]
  A = matrix "1,1,1,1; 1,2,3,4"
  C = circuits(A)  --circuits returned by 4ti2
  Icir = toBinomial(C,R) -- circuit ideal returend by 4ti2
  Ctrue = matrix{{0,1,-2,1},{1,-2,1,0},{1,0,-3,2},{2,-3,0,1}} --known: all circuits
  IcirTrue = toBinomial(Ctrue,R) --known: circuit ideal
  Irnc3 = ideal(x_0*x_2-x_1^2,x_1*x_3-x_2^2,x_0*x_3-x_1*x_2)
  assert(Icir==IcirTrue)
  shouldBeFalse = (Icir==Irnc3)
  assert(shouldBeFalse==false)
  assert(target C == target Ctrue)
  assert(source C == source Ctrue)
///
TEST ///     
  loadPackage "FourTiTwo"   --testing rays and hilbert
  B = matrix "1,-2,1,0; 0,1,-2,1"  
  R = QQ[a..d]
  I = toBinomial(B,R)
  assert(a*c-b^2 % I == 0)
  assert(a*c-d^2 %I =!= 0)
  assert(degree I == 4)
  M = hilbertBasis B
  assert(numrows M == 3)
  assert(numcols M == 4)     
  M1 = rays B
  assert(numrows M1 == 2)
  assert(numcols M1 == 4)
///
TEST///
  loadPackage "FourTiTwo"   --testing toricGB
  A = matrix "1,0,1,1,0,1,1,0,1,0,0,0,0,0,0,0,0,0;0,1,1,0,0,0,0,0,0,1,0,1,1,0,1,0,0,0;0,0,0,0,1,1,0,0,0,0,1,1,0,0,0,1,0,1;0,0,0,0,0,0,0,1,1,0,0,0,0,1,1,0,1,1;0,1,1,0,1,1,0,1,1,0,0,0,0,0,0,0,0,0;1,0,1,0,0,0,0,0,0,0,1,1,0,1,1,0,0,0;0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,1,1;0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,1,0,1;0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1"
  M = toricGB(A); --note this matrix is the design matrix for the p1 statistical model on 4 nodes using a constant rho. (see fienberg/rinaldo/petrovic; in prep-missing reference).
  assert(numrows M == 137)
  assert(numrows M == 18)
  R = QQ[x_1..x_18]
  I = toBinomial(M,R);
  assert(degree I == 192)
///
TEST///
  loadPackage "FourTiTwo"   --testing graver  
  A1 = matrix "3,2,1,0;0,1,2,3"
  G = graverBasis(A1)
  assert( numrows G==5)
  assert(numcols G==4)
  A = matrix "1,0,1,1,0,1,1,0,1,0,0,0,0,0,0,0,0,0;0,1,1,0,0,0,0,0,0,1,0,1,1,0,1,0,0,0;0,0,0,0,1,1,0,0,0,0,1,1,0,0,0,1,0,1;0,0,0,0,0,0,0,1,1,0,0,0,0,1,1,0,1,1;0,1,1,0,1,1,0,1,1,0,0,0,0,0,0,0,0,0;1,0,1,0,0,0,0,0,0,0,1,1,0,1,1,0,0,0;0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,1,1;0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,1,0,1;0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1"
  M = graverBasis(A);   --note this matrix is the design matrix for the p1 statistical model on 4 nodes using a constant rho. (see fienberg/rinaldo/petrovic; in prep-missing reference).
  assert(numrows M == 7462)
  assert(numrows M == 18)
///


end



restart
--load "4ti2.m2"
installPackage ("FourTiTwo", RemakeAllDocumentation => true, UserMode=>true)
installPackage("FourTiTwo",UserMode=>true,DebuggingMode => true)
viewHelp FourTiTwo


check FourTiTwo

debug FourTiTwo


A = matrix{{1,1,1,1},{0,1,2,3}}
A = matrix{{1,1,1,1},{0,1,3,4}}
B = syz A
time markovBasis A
A
markovBasis(A, InputType => "lattice")
R = QQ[a..d]
time toricGB(A)
toBinomial(transpose B, R)
circuits(A)
H = hilbertBasis(A)
hilbertBasis(transpose B)
toBinomial(H,QQ[x,y])
graverBasis(A)
A
markovBasis(A)

7 9
A = matrix"
1,1,1,-1,-1,-1, 0, 0, 0;
1,1,1, 0, 0, 0,-1,-1,-1;
0,1,1,-1, 0, 0,-1, 0, 0;
1,0,1, 0,-1, 0, 0,-1, 0;
1,1,0, 0, 0,-1, 0, 0,-1;
0,1,1, 0,-1, 0, 0, 0,-1;
1,1,0, 0,-1, 0,-1, 0, 0"
transpose A
markovBasis transpose A
hilbertBasis transpose A
graverBasis transpose A
circuits transpose A

27 27
A = matrix"
1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0;
0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0;
0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0;
0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0;
0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0;
0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0;
0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0;
0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0;
0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,1;
1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1,0,0;
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1,0;
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,1,0,0,1;
1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0;
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0;
0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1"
markovBasis A
R = QQ[x_1..x_27]
markovBasis(A,R)
toricGB(A,R)
gens gb oo

I = toBinomial(matrix{{}}, QQ[x])
gens I
gens gb I
