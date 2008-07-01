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
	 symbol CRelations => C,
	 symbol cache => CacheTable
	 }

-- some toy examples
I={b,c,d,e,a,f,g,h}
C={(a,b),(a,c),(a,d),(b,e),(b,f),(c,e),(c,g),(d,f),(d,g),(e,h),(f,h),(g,h)}
P=newPoset(I,C)

I1={a,c,d,b,e}
C1={(a,c),(a,d),(b,c),(b,d),(c,e),(d,e)}
P1=newPoset(I,C)

-- input: A poset
-- output: a matrix indexed by I that has non zero entries for each pair of relations
FullRelationMatrix:= (P) -> (
     M:=matrix apply (#P.GroundSet, i-> apply(#P.GroundSet, j-> if member((I#i,I#j), P.CRelations) then 1 else if i==j then 1 else 0));
     n:=#I;
     N:=M^n)


-- input:  A poset, and two elements A and B from I
-- output: true if A<= B, false else
compare:= (P,A,B) -> (
     FullRelationMatrix(P);
     Aindex:=sum apply(#P.GroundSet, i-> if P.GroundSet#i == A then i else 0);
     Bindex:=sum apply(#P.GroundSet, i-> if P.GroundSet#i == B then i else 0);
          if N_Bindex_Aindex==0 then false else true
     )


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
