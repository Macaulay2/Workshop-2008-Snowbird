"

The primary purpose of this package is to help compute with intersection theory
on smooth varieties.  An ", TO "AbstractVariety", " is not given by equations.
Instead, one gives its intersection ring (usually mod numerical equivalence),
its dimension, and the chern class of its tangent bundle.  An ", TO
"AbstractSheaf", " is represented by its total chern class (or by its chern
character).  An ", TO "AbstractVarietyMap", " is a 'morphism' of abstract
varieties, and the information encoded is the pull-back to the corresponding intersection rings.

There are several methods for constructing abstract varieties: the following functions
construct basic useful varieties (often returning the corresponding structure map):
  projectiveSpace
  projectiveBundle
  flagBundle
  base
  blowup
  directProduct (**)
  bundleSection
  schubertVariety
one can also build a variety from scratch using abstractVariety.

"     
     }

document {
     Key => AbstractSheaf,
     Headline => "the class of sheaves given by their Chern classes",
     PARA{},
     "A sheaf on an an abstract variety is represented by its total chern class.",
     EXAMPLE lines ///
     ///,
     SeeAlso => {"AbstractVariety"}
     }


restart
loadPackage "Schubert2"
A = QQ[h,f]/(h*f-h^2, f^2)
X = abstractVariety(2,A)
X.TangentBundle = 1+h+h^2
tangentBundle X
integral(h*f)
basis(2,A)
