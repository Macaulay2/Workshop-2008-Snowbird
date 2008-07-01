newPackage(
	"Posets",
    	Version => "0.1", 
    	Date => "July 7th, 2008",
    	Authors => {
	     {Name => "Sonja Mapes", Email => "mapes@math.columbia.edu", HomePage => "http://www.math.columbia.edu/~mapes/"},
	     {Name => "Gwyn Whieldon", Email => "whieldon@math.cornell.edu", HomePage => "http://www.math.cornell.edu/People/Grads/whieldon.html"},
	     {Name => "Josephine Yu", Email => "jyu@math.mit.edu", HomePage => "http://www-math.mit.edu/~jyu/"}
	     },
    	Headline => "Package for processing posets and order complexes",
    	DebuggingMode => true
    	)
 
export {
     newPoset     
     }

restart

Poset = new Type of HashTable

newPoset := (I,C) ->
     new Poset from {
	 symbol GroundSet => I,
	 symbol CoveringRelations => C,
	 symbol cache => CacheTable
	 }

I={a,b,c,d,e,f,g,h}
C={(a,b),(a,c),(a,d),(b,e),(b,f),(c,e),(c,g),(d,f),(d,g),(e,h),(f,h),(g,h)}
P=newPoset(I,C)


compare:= (P,A,B) -> (
     M:=matrix apply (#P.GroundSet, i-> apply(#P.GroundSet, j-> if member((I#i,I#j), P.CoveringRelations) then 1 else if i==j then 1 else 0));
     n:=#I;
     N:=M^n;
     Aindex:=sum apply(#P.GroundSet, i-> if P.GroundSet#i == A then i else 0);
     Bindex:=sum apply(#P.GroundSet, i-> if P.GroundSet#i == B then i else 0);
     if N_Bindex_Aindex==0 then false else true
     )
compare(P,d,e)


beginDocumentation()

document { Key => Poset,
     Headline => "Betti diagram routines",
     EM "BoijSoederberg", " is a package designed to help with the investigation of 
     the Boij-Soederberg conjectures and theorems.  For the definitions and conjectures, see
     math.AC/0611081, \"Graded Betti numbers of Cohen-Macaulay modules and 
     the Multiplicity conjecture\", by Mats Boij, Jonas Soederberg."
                    }


document { 
     Key => {},
     Headline => "",
     Usage => "",
     Inputs => {
	  },
     Outputs => {
	  },
     EXAMPLE lines ///
	  ///,
     Caveat => {},
     SeeAlso => {}
     }

installPackage "Posets" 