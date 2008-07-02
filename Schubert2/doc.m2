needsPackage "SimpleDoc"

doc ///
  Key
    Schubert2
  Headline
    A package for computations in Intersection Theory
  Description
The primary purpose of this package is to help compute with intersection theory
on smooth varieties.  An @TO AbstractVariety@ is not given by equations.
Instead, one gives its intersection ring (usually mod numerical equivalence),
its dimension, and the chern class of its tangent bundle.  An @TO
AbstractSheaf@ is represented by its total chern class (or by its chern
character).  An @TO AbstractVarietyMap@ is a 'morphism' of abstract
varieties, and the information encoded is the pull-back to the corresponding intersection rings.
  SeeAlso
    AbstractSheaf
    chern
    chi
    TangentBundle
    todd
///
  


doc ///
  Key
    AbstractVariety
  Headline
    The Schubert2 data type of an abstract variety
  Description
   Text
   An Abstract Variety in Schubert 2 
   is defined by its dimension and a QQ-algebra, interpreted as the rational Chow ring.
   For example, the following code defines the abstract variety corresponding to P2,
   with its Chow ring A. Once the variety X is created, we can access its structure
   sheaf OO_X, represented by its Chern class
   
   Example
     A=QQ[t]/ideal(t^3)
     X=abstractVariety(2,A)
     OO_X
     chern OO_X
   Text
   A variable of type AbstractVariety is actually of type MutableHashTable, and can
   contain other information, such as its @TO TangentBundle@. Once this is defined,
   we can compute the Todd class.
   Example
        X.TangentBundle  = abstractSheaf(X,Rank=>2, ChernClass=>(1+t)^3)
	todd X
   Text
   If we want things like the Euler characteristic of a sheaf, we must also
   specify a method to take the @TO integral@ for the Chow ring A; in the case
   where A is Gorenstein, as is the Chow ring of a complete nonsingular variety,
   this is a functional that takes the highest degree component. 
   In the following example, The sheaf OO_X is
   the structure sheaf of X, and OO_X(2t) is the line bundle with first Chern class 2t.
   The computation of the Euler Characteristic is made using the Todd class and the 
   Riemann-Roch formula.
     Example
     integral A := f -> coefficient(t^2,f)    
     chi(OO_X(2*t))
  Text
  There are several other methods for constructing abstract varieties: the following functions
  construct basic useful varieties (often returning the corresponding structure map):
  projectiveSpace
  projectiveBundle
  flagBundle
  base
  blowup
  directProduct (**)
  bundleSection
  schubertVariety
  SeeAlso
    AbstractSheaf
    chern
    chi
    TangentBundle
    todd
///

doc ///
  Key
    AbstractSheaf 
  Headline
    the class of sheaves given by their Chern classes
  Description
   Text
     This is the class of a sheaf as defined in the package
     @TO Schubert2@.
     An abstract sheaf is really the data of its base variety
     (see @TO AbstractVariety@), @TO Rank@, @TO ChernClass@...
   Text     
     For example, the Horrocks-Mumford bundle on projective 4-space
     can be represented as follows:

   Example
X = projectiveSpace(4,pt,VariableName => h)
F = abstractSheaf(X, Rank => 2, ChernClass => 1 + 5*h + 10*h^2)

   Text
     Here in the description of X the number 4 is the rank of the trivial bundle, pt 
     is the base variety of the projective space (in general, we allow
     projective spaces over an arbitrary base AbstractVariety), and the 
     variable name specifies the variable to use to represent the first
     Chern Class of the tautological quotient line bundle on the projective space.
  SeeAlso
    AbstractVariety
///


restart
loadPackage "Schubert2"
A = QQ[h,f]/(h*f-h^2, f^2)
X = abstractVariety(2,A)
X.TangentBundle = 1+h+h^2
tangentBundle X
integral(h*f)
basis(2,A)
