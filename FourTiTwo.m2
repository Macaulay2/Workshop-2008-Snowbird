----------------------------------------------------
----------------------------------------------------
-- previous version: 0.2 30Jun08, submitted by Josephine Yu.
-- author: Mike Stillman -- 
--     	    	      	   core
-- author: Josephine Yu -- 
--     	    	      	   all remaining functions; documentation
-- editor: Sonja Petrovic -- 
--     	    	      	   interface for windows; edited documentation; tests
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
	     {Name => "editor: Sonja Petrovic", Email => "petrovic@ms.uky.edu", HomePage => ""}
	     },
    	Headline => "Interface to the 4ti2 package",
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
     InputType,
     setPath
     }


-- this is the option working on MacOS and Linux(?):
path'4ti2 = FourTiTwo#Options#Configuration#"path" --we will keep it here to be the default value. 

-- on the other hand, windows/cygwin is different. 
-- for eample: this is where I've put the 4ti2 executables (inside the cygwin directory):
-- path'4ti2 = " 4ti2_v1.3.1/win32/"
-- (sidenote i can see "cygdrive/c" ....and the rest of c-drive!! it is located ABOVE "home" directory of cygwin.)
-- 
-- However, if the package can't find the 4ti2 directory using the above path, 
-- we will allow the user to set their own path by invoking the following command:
setPath = method()
setPath(String):=(p)->(
     path'4ti2 = p;  --  " 4ti2_v1.3.1/win32/"
     )


-- the following command is necessary to be run under windows-cygwin:
-- externalPath = value Core#"private dictionary"#"externalPath"
-- Note: outside of cygwin (linux/mac), this string is just the null string. 
-- But under Windows machines this is necessary (the value of the string is C:/cygwin).
temppath = value Core#"private dictionary"#"externalPath"
externalPath = demark("/",separate(///\///, value ///temppath/// )) --this is to ensure 
               --  that the slashes/backslashes are not the wrong way.
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
	       its columns. For example, if 
	  Example
	       A=matrix{{3,2,1,0},{0,1,2,3}}
	  Text	       
	       the map from k[s,t] to k[a,b,c,d] is given by 
	       
	       {\tt (s,t)-> (s^3, s^2t,st^2,t^3)}.
	       
	       The toric ideal I_A is the kernel of this map. 
	       It is minimally generated by the 2-minors of the matrix
    	  Example
	       matrix{{a, b, c},{b, c, d}}
	  Text	
	       Given the matrix {\tt A}, one can compute its lattice basis ideal specified by the integral basis
	       of the lattice {\tt A}, the toric ideal I_A, its Groebner bases, etc. In practice, however, 
	       these are nontrivial computational tasks. 
	       The software 4ti2 is very efficient in computing these objects. 	      
	       
	       For more theoretical details (and more generality), see the standard reference: 
	       B. Sturmfels, {\bf Gr\"obner bases and convex polytopes.} 
	       American Mathematical Society, University Lectures Series, No 8, Providence, Rhode Island, 1996.  
     SeeAlso
     	  setPath
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
	        needsPackage "FourTiTwo"
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
	       needsPackage "FourTiTwo"
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
     Outputs
     	  B:Matrix 
	       whose rows give binomials that form a Groebner basis of the toric ideal of {\tt A}
     	  I:Ideal
	       whose generators form a Groebner basis for the toric ideal
     Description
	  Example
 	       needsPackage "FourTiTwo"
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
 	       needsPackage "FourTiTwo"
	       A = matrix "1,1,1,1; 0,1,2,3"
	       markovBasis(A)
     	       B = syz A
	       markovBasis(transpose B, InputType => "lattice")
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
 	       needsPackage "FourTiTwo"
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
 	       needsPackage "FourTiTwo"
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
 	       needsPackage "FourTiTwo"
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


doc ///
     Key
     	  setPath
	  (setPath, String)
     Headline
     	  IF FourTiTwo can't find your 4ti2 directory, this should be called *once* after loading the pacakge.
     Usage
     	  setPath(p)
     Inputs
      	  p:String
              specifying the location of the 4ti2 directory on your local machine
     Description
          Text
     	      FourTiTwo is designed to interface with 4ti2 installed on your local machine. 
	      For most users, the package will locate 4ti2 automatically. 
	      
	      Warning: if while running the package you get an error describing that 4ti2 cannot be run,
	      then invoke the command setPath and pass it a string which specifies the location of the 4ti2 
	      executables. For example, on a particular windows machine runnning cygwin, the first attempt at 
	      the package produces an error:
     	  Example 
	      restart;
	      needsPackage "FourTiTwo"    
	      A = matrix "1,1,1,1; 1,2,3,4"
	  Text
	      If our next command is one of the functions calling 4ti2, for example:
	  Example
	      toricGB(A);
	  Text 
	      it is possible that the output looks something like this:
	      
	      {\tt  sh: groebner: command not found}
	      
	      {\tt   FourTiTwo.m2:149:24:(1):[3]: error occurred while executing external program 4ti2: groebner}
	  Text
	      To fix this, suppose that I have installed 4ti2 into a directory 
	      {\tt C:/cygwin/4ti2_v1.3.1/win32/ }. Then running the command {\tt setPath} 
	      will allow FourTiTwo to find 4ti2; thus the previous calculation will not fail:
	  Example
     	      restart;
	      needsPackage "FourTiTwo";
	      setPath( " 4ti2_v1.3.1/win32/");
	      A = matrix "1,1,1,1; 1,2,3,4"
       	      toricGB(A)
	  Text
	      Note that if you are running under cygwin, your 4ti2 directory should be in the cygwin 
	      directory. Moreover, {\tt C:/cygwin} should not be passed to the setPath function!
///;

--     toBinomial,
--     getMatrix,
--    putMatrix,
--     markovBasis,
--     toricGB,
--     circuits,
--     graverBasis,
--     hilbertBasis,
--     rays,
TEST/// 
  loadPackage "FourTiTwo"
  A = matrix "1,1,1,1; 1,2,3,4"
  I = markovBasis(A)
  assert(true==true)
///
TEST ///   
  loadPackage "FourTiTwo"
  assert(true==true)  
///
TEST ///     
  loadPackage "FourTiTwo"
  assert(true==true)
///
TEST ///     
  loadPackage "FourTiTwo"
  assert(true==true)
///


end


restart
--load "4ti2.m2"
--installPackage ("FourTiTwo", RemakeAllDocumentation => true, UserMode=>true)
installPackage("FourTiTwo",UserMode=>true)
viewHelp FourTiTwo



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
