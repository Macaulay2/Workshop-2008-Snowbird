newPackage(
	"FourTiTwo",
    	Version => "0.2", 
    	Date => "June 30, 2008",
    	Authors => {
	     {Name => "Mike Stillman", Email => "mike@math.cornell.edu", HomePage => ""},
	     {Name => "Josephine Yu", Email => "jyu@math.mit.edu", HomePage => ""}
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
     InputType
     }

path'4ti2 = FourTiTwo#Options#Configuration#"path"

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
     execstr = path'4ti2|"markov -q "|filename;
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
     execstr = path'4ti2|"groebner -q "|filename;
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
     execstr = path'4ti2|"circuits -q " | filename;
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
     execstr = path'4ti2|"graver -q " | filename;
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
     execstr = path'4ti2|"hilbert -q " | filename;
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
     execstr = path'4ti2|"rays -q " | filename;
     ret := run(execstr);
     if ret =!= 0 then error "error occurred while executing external program 4ti2: rays";
     getMatrix(filename|".ray")
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
	       Interfaces most of the functionality of the software {\tt 4ti2} available at  {\tt http://www.4ti2.de/}
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
	     The first two numbers and the numbers of rows and columns.
    SeeAlso
	putMatrix
///;

doc ///
     Key 
	  putMatrix
     	  (putMatrix,File,Matrix)
     Headline
     	  writes a 4ti2 format matrix in a file.
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
     Usage
     	  toricGB(A) or toricGB(A,R)
     Inputs
      	  A:Matrix    
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
     Usage
     	  markovBasis(A) or markovBasis(A, InputType => "lattice")
     Inputs
      	  A:Matrix
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
     Usage
     	  graverBasis(A) or graverBasis(A,R)
     Inputs
      	  A:Matrix    
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
     Usage
     	  hilbertBasis(A) or hilbertBasis(A, InputType => "lattice")
     Inputs
      	  A:Matrix    
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
     Usage
     	  rays(A)
     Inputs
      	  A:Matrix    
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
     Usage
     	  circuits(A)
     Inputs
      	  A:Matrix    
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



TEST ///

     
///

end

restart
load "4ti2.m2"
installPackage ("FourTiTwo", RemakeAllDocumentation => true)
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
