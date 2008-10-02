----------------------------------------------------
----------------------------------------------------
-- previous version: 0.2 30Jun08, submitted by Josephine Yu.
-- author: Mike Stillman -- 
--     	    	      	   core
-- author: Josephine Yu -- 
--     	    	      	   all remaining functions; documentation
-- Sonja Petrovic -- 
--     	    	      	   interface for windows; edited documentation; tests
--     	    	      	   
-- latest update: 6Jul08;  small revision in Documentation: 2oct08.
----------------------------------------------------
----------------------------------------------------

newPackage(
	"FourTiTwo",
    	Version => "0.3", 
    	Date => "July 2, 2008",
    	Authors => {
	     {Name => "Mike Stillman", Email => "mike@math.cornell.edu", HomePage => ""},
	     {Name => "Josephine Yu", Email => "jyu@math.mit.edu", HomePage => ""},
	     {Name => "Sonja Petrovic", Email => "petrovic@math.uic.edu", HomePage => ""}
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
     toricMarkov,
     toricGroebner,
     toricCircuits,
     toricGraver,
     hilbertBasis,
     rays,
     InputType,
     toricGraverDegrees
     }


path'4ti2 = (options FourTiTwo).Configuration#"path"
-- NOTE: the absolute path should be put into the .init file for 4ti2 inside the .Macaulay2 directory.


-- the following command is necessary to be run under windows-cygwin:
-- externalPath = value Core#"private dictionary"#"externalPath"
-- Note: outside of cygwin (linux/mac), this string is just the null string. 
-- But under Windows machines this is necessary (the value of the string is C:/cygwin).
--externalPath = replace("/","\\",value Core#"private dictionary"#"externalPath")
externalPath = replace("\\\\","/",value Core#"private dictionary"#"externalPath")
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

toricMarkov = method(Options=> {InputType => null})
toricMarkov Matrix := Matrix => o -> (A) -> (
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
toricMarkov(Matrix,Ring) := o -> (A,S) -> toBinomial(toricMarkov(A,o), S)

toricGroebner = method(Options=>{Weights=>null})
toricGroebner Matrix := o -> (A) -> (
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
toricGroebner(Matrix,Ring) := o -> (A,S) -> toBinomial(toricGroebner(A,o), S)

toricCircuits = method()
toricCircuits Matrix := Matrix => (A ->(
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

toricGraver = method()
toricGraver Matrix := Matrix => (A ->(
     filename := getFilename();
     << "using temporary file name " << filename << endl;
     F := openOut(filename|".mat");
     putMatrix(F,A);
     close F;
     execstr = path'4ti2|"graver -q " | externalPath | filename;
     ret := run(execstr);
     if ret =!= 0 then error "error occurred while executing external program 4ti2: graver";
     getMatrix(filename|".gra")
     ))
toricGraver (Matrix,Ring) := Ideal => ((A,S)->toBinomial(toricGraver(A),S))

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
     if ret =!= 0 then error "error occurred while executing external program 4ti2: hilbert";
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
-- I would like to have a command that gives the list of degrees of Graver/Groebner/Circuit/Markov file;
-- the way 4ti2 does this is you tell it the whatever.mar or whatever.cir file and it writes the degrees
-- to the screen.
toricGraverDegrees = method()
toricGraverDegrees Matrix := Matrix => (A ->(
     filename := getFilename();
     << "using temporary file name " << filename << endl;
     F := openOut(filename|".mat");
     putMatrix(F,A);
     close F;
     execstr = path'4ti2|"graver -q " | externalPath | filename;
     ret := run(execstr);
     if ret =!= 0 then error "error occurred while executing external program 4ti2: graver"; -- getMatrix(filename|".gra")
     execstr = path'4ti2|"output --degrees " | externalPath | filename|".gra";
     ret = run(execstr);
     if ret =!= 0 then error "error occurred while executing external program 4ti2: output";
     ))


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
	       (The user needs to have 4ti2 installed on his/her machine.)
	        
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
	       
               {\bf Note for cygwin users:} 
	       If a problem occurs during package installation and/or loading, it should be fixed 
	       by setting the path inside the file .Macaulay2/init-FourTiTwo.m2  to whatever folder 4ti2 is installed.
	       For example, if  4ti2 has been installed in C:/cygwin/4ti2/win32 , then the line 
	       inside the init-FourTiTwo.m2 file will look like this:  "path" => "C:/cygwin/4ti2/win32/"  .<br>
	       Alternately, the path for 4ti2 may be set when loading the package using the following command:<br>
	       loadPackage("FourTiTwo", Configuration=>{"path"=>"C:/cygwin/4ti2/win32/"})  <br>
	       assuming that 4ti2 has been installed in C:/cygwin/4ti2/win32.
      	       
	       {\bf Caveat:}   
      	       If package SimpleDoc is not found when installing FourTiTwo.m2, 
	       see questions and answers 6, 7, and 8 on the Macaulay 2 web site.	       
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
     	  creates a toric ideal from a given set of exponents of its generators
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
     	  toricGroebner
          (toricGroebner, Matrix)
     	  (toricGroebner, Matrix, Ring)
     	  [toricGroebner, Weights]
     Headline
     	  calculates a Groebner basis of the toric ideal I_A, given A; equivalent to "groebner" in 4ti2
     Usage
     	  toricGroebner(A) or toricGroebner(A,R)
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
	       toricGroebner(A)
	  Text
	       Note that the output of the command is a matrix whose rows are the exponents of the binomials that for a Groebner basis of the toric ideal I_A.
	       As a shortcut, one can ask for the output to be an ideal instead:
	  Example
	       R = QQ[a..d]
	       toricGroebner(A,R)
	  Text
	       4ti2 offers the use of weight vectors representing term orders, as follows:
	  Example
	       toricGroebner(A,Weights=>{1,2,3,4})
 ///;
 
 doc ///
     Key
     	  toricMarkov
          (toricMarkov, Matrix)
	  (toricMarkov, Matrix, Ring)
	  [toricMarkov, InputType]
     Headline
     	  calculates a generating set of the toric ideal I_A, given A; equivalent to "markov" in 4ti2
     Usage
     	  toricMarkov(A) or toricMarkov(A, InputType => "lattice") or toricMarkov(A,R)
     Inputs
      	  A:Matrix
	       whose columns parametrize the toric variety; the toric ideal is the kernel of the map defined by {\tt A}.
	       Otherwise, if InputType is set to "lattice", the rows of {\tt A} are a lattice basis and the toric ideal is the 
	       saturation of the lattice basis ideal.	       
	  s:InputType
	       which is the string "lattice" if rows of {\tt A} specify a lattice basis
	  R:Ring
	       polynomial ring in which the toric ideal I_A should live
     Outputs
     	  B:Matrix 
	       whose rows form a Markov Basis of the lattice \{z integral : A z = 0\}
	       or the lattice spanned by the rows of {\tt A} if the option InputType => "lattice" is used
     Description
     	  Text
	       Suppose we would like to comput the toric ideal defining the variety parametrized by the following matrix:
	  Example
	       A = matrix"1,1,1,1;0,1,2,3"
	  Text
	       Since there are 4 columns, the ideal will live in the polynomial ring with 4 variables.
	  Example
	       R = QQ[a..d]
	       M = toricMarkov(A)
	  Text
	       Note that rows of M are the exponents of minimal generators of I_A.  To get the ideal, we can do the following:
	  Example
      	       I = toBinomial(M,R)
	  Text
	       Alternately, we might wish to give a lattice basis ideal instead of the matrix A. The lattice basis will be specified 
	       by a matrix, as follows:
	  Example
	       B = syz A 
	       N = toricMarkov(transpose B, InputType => "lattice")	  
	       J = toBinomial(N,R) -- toricMarkov(transpose B, R, InputType => "lattice")	     
	  Text
	       We can see that the two ideals are equal:
	  Example
     	       I == J
	  Text
	       Also, notice that instead of "toBinomial" command we could have used the following:
	  Example
	       toricMarkov(A,R)	       
///;

doc ///
     Key
     	  toricGraver
          (toricGraver, Matrix)
     	  (toricGraver, Matrix, Ring)
     Headline
     	  calculates the Graver basis of the toric ideal; equivalent to "graver" in 4ti2
     Usage
     	  toricGraver(A) or toricGraver(A,R)
     Inputs
      	  A:Matrix    
	       whose columns parametrize the toric variety. The toric ideal I_A is the kernel of the map defined by {\tt A}
	  R:Ring
	       polynomial ring in which the toric ideal I_A should live
     Outputs
     	  B:Matrix 
	       whose rows give binomials that form the Graver basis of the toric ideal of {\tt A}, or
     	  I:Ideal
	       whose generators form the Graver basis for the toric ideal
     Description
     	  Text
	       The Graver basis for any toric ideal I_A contains (properly) the union of all reduced Groebner basis of I_A.  
	       Any element in the Graver basis of the ideal is called a primitive binomial.
	  Example
	       A = matrix "1,1,1,1; 1,2,3,4"
	       toricGraver(A)
	  Text
	       If we prefer to store the ideal instead, we may use:
	  Example
	       R = QQ[a..d]
	       toricGraver(A,R)
	  Text
	       Note that this last ideal equals the toric ideal I_A since every Graver basis element is actually in I_A.
///;

doc ///
     Key
     	  toricGraverDegrees
          (toricGraverDegrees, Matrix)
     Headline
     	  displays the degrees of all Graver basis elements for the toric ideal I_A; equivalent to "output --degrees foo.gra" in 4ti2
     Usage
     	  toricGraverDegrees(A) 
     Inputs
      	  A:Matrix    
	       whose columns parametrize the toric variety. The toric ideal I_A is the kernel of the map defined by {\tt A}
     Description
     	  Text
	       Very often the Graver basis consits of too many binomials, and one is only interested in their degrees. In this case,
	       instead of looking at the Graver basis of I_A, we may just want to look for the degrees of binomials which show up:
	  Example
	       A = matrix "1,1,1,1; 1,2,3,4"
	       toricGraver(A) -- the Graver basis
	       toricGraverDegrees(A) -- just the degrees
	  Text
	       Note that these are all 1-norms of the vectors. Since I_A is homogeneous, there are 3 binomials of degree 2 (norm 4) 
	       and 2 binomials of degree 3 (norm 6).
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
     	  toricCircuits
          (toricCircuits, Matrix)
     Headline
     	  calculates the circuits of the toric ideal; equivalent to "circuits" in 4ti2
     Usage
     	  toricCircuits(A)
     Inputs
      	  A:Matrix    
               whose columns parametrize the toric variety. The toric ideal I_A is the kernel of the map defined by {\tt A} 
     Outputs
     	  B:Matrix 
	       whose rows form the circuits of A
     Description
     	  Text
	       The cicruits are contained in the Graver basis of I_A. In fact, they are precisely the primitive binomials in the ideal
	       with  minimal support.
	  Example
	       A = matrix "1,1,1,1; 1,2,3,4"
	       toricCircuits A
	  Text 
	       The ideal generated by the circuits of A in general differs from the toric ideal of A.
///;

doc ///
     Key
     	  InputType
     Description
          Text
     	      Put {\tt InputType => "lattice"} as a argument in the functions toricMarkov and hilbertBasis
     SeeAlso
     	  toricMarkov
	  hilbertBasis
///;


TEST/// 
  loadPackage "FourTiTwo"    --testing toricMarkov w/ matrix inputt
  A = matrix "1,1,1,1; 1,2,3,4"
  M = toricMarkov(A)
  R = QQ[x_0,x_1,x_2,x_3]
  I = toBinomial(M,R)
  Irnc3 = ideal(x_0*x_2-x_1^2,x_1*x_3-x_2^2,x_0*x_3-x_1*x_2)
  assert(I==Irnc3)
///
TEST ///   
  loadPackage "FourTiTwo"   --testing toricMarkov w/ lattice input
  B = matrix "1,-2,1,0; 0,1,-2,1"
  M = toricMarkov(B, InputType => "lattice")
  R = QQ[x_0,x_1,x_2,x_3]
  I = toBinomial(M,R)
  Irnc3 = ideal(x_0*x_2-x_1^2,x_1*x_3-x_2^2,x_0*x_3-x_1*x_2)
  assert(I== Irnc3)  
///
TEST ///     
  loadPackage "FourTiTwo"   --testing circuits
  R=CC[x_0,x_1,x_2,x_3]
  A = matrix "1,1,1,1; 1,2,3,4"
  C = toricCircuits(A)  --circuits returned by 4ti2
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
  loadPackage "FourTiTwo"   --testing toricGroebner
  A = matrix "1,0,1,1,0,1,1,0,1,0,0,0,0,0,0,0,0,0;0,1,1,0,0,0,0,0,0,1,0,1,1,0,1,0,0,0;0,0,0,0,1,1,0,0,0,0,1,1,0,0,0,1,0,1;0,0,0,0,0,0,0,1,1,0,0,0,0,1,1,0,1,1;0,1,1,0,1,1,0,1,1,0,0,0,0,0,0,0,0,0;1,0,1,0,0,0,0,0,0,0,1,1,0,1,1,0,0,0;0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,1,1;0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,1,0,1;0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1"
  M = toricGroebner(A); --note this matrix is the design matrix for the p1 statistical model on 4 nodes using a constant rho. (see fienberg/rinaldo/petrovic; in prep-missing reference).
  assert(numrows M == 137)
  assert(numcols M == 18)
  R = QQ[x_1..x_18]
  I = toBinomial(M,R);
  assert(degree I == 192)
///
TEST///
  loadPackage "FourTiTwo"   --testing graver  
  A1 = matrix "3,2,1,0;0,1,2,3"
  G = toricGraver(A1)
  assert( numrows G==5)
  assert(numcols G==4)
  A = matrix "1,0,1,1,0,1,1,0,1,0,0,0,0,0,0,0,0,0;0,1,1,0,0,0,0,0,0,1,0,1,1,0,1,0,0,0;0,0,0,0,1,1,0,0,0,0,1,1,0,0,0,1,0,1;0,0,0,0,0,0,0,1,1,0,0,0,0,1,1,0,1,1;0,1,1,0,1,1,0,1,1,0,0,0,0,0,0,0,0,0;1,0,1,0,0,0,0,0,0,0,1,1,0,1,1,0,0,0;0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,1,1;0,0,0,0,0,0,1,0,1,0,0,0,1,0,1,1,0,1;0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1"
  M = toricGraver(A);   --note this matrix is the design matrix for the p1 statistical model on 4 nodes using a constant rho. (see fienberg/rinaldo/petrovic; in prep-missing reference).
  assert(numrows M == 7462)
  assert(numcols M == 18)
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
time toricMarkov A
A
toricMarkov(A, InputType => "lattice")
R = QQ[a..d]
time toricGroebner(A)
toBinomial(transpose B, R)
toricCircuits(A)
H = hilbertBasis(A)
hilbertBasis(transpose B)
toBinomial(H,QQ[x,y])
toricGraver(A)
A
toricMarkov(A)

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
toricMarkov transpose A
hilbertBasis transpose A
toricGraver transpose A
toricCircuits transpose A

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
toricMarkov A
R = QQ[x_1..x_27]
toricMarkov(A,R)
toricGroebner(A,R)
gens gb oo

I = toBinomial(matrix{{}}, QQ[x])
gens I
gens gb I
