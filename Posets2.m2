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
     Poset,
     poset,
     DirectedGraph,
     directedGraph,
     allPairsShortestPath,
     transitiveClosure,
--     FullRelationMatrix,
     RelationMatrix,
     compare,
     indexElement,
     nonnull,
     OrderIdeal,
     Filter,
     Relations
     GroundSet,
     Edges
     }



Poset = new Type of HashTable

poset = method()
poset(List,List) := (I,C) ->
     new Poset from {
	 symbol GroundSet => I,
	 symbol Relations => C,
     	 symbol RelationMatrix => transitiveClosure(I,C),
	 symbol cache => CacheTable
	 }
    
-------------
    
DirectedGraph = new Type of HashTable
 
directedGraph = method()
directedGraph(List, List) := (I,C) ->
     new DirectedGraph from {
     	  symbol GroundSet => I,
     	  symbol Edges => C,
	  symbol cache => CacheTable
     }

--------------

--inputs: (I,C), I is a List (ground set) and C is a List of pairs of elements in I
--     	     OR DirectedGraph OR Poset
--output: a matrix whose rows and columns are indexed by I, 
--     	    where (i,j) entry is infinity (i.e. 1/0.) if (i,j) is not in C
--     	    and 1 otherwise (i.e. tropicalization of the "usual" adjacency matrix)
--caveat: diagonal entries are 0

adjacencyMatrix = method()
adjacencyMatrix(List,List) := Matrix => (I, C) -> (
     M := mutableMatrix table(#I, #I, (i,j)->1/0.);
     ind := hashTable( apply(I, i-> i=> position(I,j-> j==i) )  ); --indices 
     scan(C, e -> M_(ind#(e#0), ind#(e#1))= 1);
     scan(numrows M, i-> M_(i,i) = 0);
     matrix M      
     )
adjacencyMatrix(DirectedGraph) := Matrix => (G) -> adjacencyMatrix(G.GroundSet,G.Edges)
adjacencyMatrix(Poset) := Matrix => (P) -> adjacencyMatrix(P.GroundSet,P.Relations)

--input: adjacency matrix of a directed graph
--output: a matrix whose (i,j) entry is the length of the shortest path from i to j
--algorithm: Floyd–Warshall algorithm for all pairs shortest path
allPairsShortestPath = method()
allPairsShortestPath(Matrix) := Matrix => (A) -> (
     D := mutableMatrix(A);
     n := numrows D;
     scan(n, k->
	       table(n,n,(i,j)-> D_(i,j) = min(D_(i,j), D_(i,k)+D_(k,j)))
	  );
     matrix D
     )
allPairsShortestPath(DirectedGraph) := Matrix => (G)-> allPairsShortestPath(adjacencyMatrix(G))



-- some toy examples
I={a,b,c,d,e,f,g,h}
C={(a,b),(a,c),(a,d),(b,e),(b,f),(c,e),(c,g),(d,f),(d,g),(e,h),(f,h),(g,h)}
P=poset(I,C)
G=directedGraph(I,C)
A=adjacencyMatrix(I,C)
allPairsShortestPath(A)
adjacencyMatrix(G)
adjacencyMatrix(P)
transitiveClosure(I,C)

I1={a,b,c,d,e,f}
C1={(a,c),(a,d),(b,c),(b,d),(c,e),(d,e),(e,f)}
P1=poset(I1,C1)

--Poset P1 with additional relations (a,e) and (a,f) added

I2={a,b,c,d,e,f}
C2={(a,c),(a,d),(b,c),(b,d),(c,e),(d,e),(a,e),(a,f),(e,f)}
P2=poset(I2,C2)


-- input: a poset, and an element A from I
-- output:  the index of A in the ground set of P
-- usage: compare, OrderIdeal 
indexElement:= (P,A) -> (
      sum apply(#P.GroundSet, i-> if P.GroundSet#i == A then i else 0))

-- input:  a list, potentially with nulls
-- output:  a list w/out nulls
-- usage:  OrderIdeal, Filter
nonnull:=(L) -> (
     select(L, i-> i =!= null))


--------------------------------------------------
--Transitive Closure and Element Inclusion
--------------------------------------------------

--input: (I,C).  I=List, ground set.  C=List, pairs
--output: matrix where 1 in (i,j) position where i <= j, 0 otherwise
transitiveClosure = method()
transitiveClosure(List,List) := List => (I,C)-> (
     A := adjacencyMatrix(I,C);
     D := mutableMatrix allPairsShortestPath(A);
     scan(numrows D, i-> D_(i,i) = 0);
     table(numrows D, numrows D, (i,j)->(
	  if D_(i,j) ==1/0. then D_(i,j) = 0 else D_(i,j) = 1;	  
	  )
	  );
     matrix D
     )

--FullRelationMatrix:= (P) -> (     
  --   M:=matrix apply (#P.GroundSet, i-> 
	--  apply(#P.GroundSet, j-> if member((P.GroundSet#i,P.GroundSet#j), P.CRelations) then 1 else if i==j then 1 else 0));
  --   n:=#P.GroundSet;
  --   N:=M^n 
  --     )


--input: A poset with any type of relation C (minimal, maximal, etc.)
--output:  The transitive closure of relations in C in our poset

fullPosetRelation:= (P) -> (
     M:=RelationMatrix(P);
     L = toList sum apply(numrows(M), i-> set(nonnull(apply(numrows(M), 
	       j-> if (M_j)_i=!=0 and i=!=j then (I#i,I#j)))))
     )

--input: A poset P with any type of relation C (minimal, maximal, etc.)
--output:  The poset P' on the same ground set with the transitive closure of C

fullPoset:= (P) -> (
     L = poset(P.GroundSet,fullPosetRelation(P)) 
)

-- input:  A poset, and two elements A and B from I
-- output: true if A<= B, false else
compare:= (P,A,B) -> (
     Aindex:=indexElement(P,A);
     Bindex:=indexElement(P,B);
          if P.RelationMatrix_Bindex_Aindex==0 then false else true
     )

--------------------------------------------------
--Covering Relations
--------------------------------------------------

testcover=(P,A,B) -> (
     L:=poset(P.GroundSet,fullPosetRelation(P));
     k:=#L.GroundSet-2; 
         
     if sum(nonnull(apply(k, i-> if compare(L,A,(toList(set(L.GroundSet)-{A,B}))_i)==true and
	       compare(L,(toList(set(L.GroundSet)-{A,B}))_i,B)==true
	       then 1)))=!=0 then C=C+set{(A,B)};
     C
)		

--input: A poset with any type of relation C (minimal, maximal, etc.)
--output: The minimal relations defining our poset

coveringRelations:=(P) -> (
     C=set{};
     apply(#P.CRelations,i->testcover(P,P.CRelations#i#0,P.CRelations#i#1));
     toList(set(P.CRelations)-C)
     )

--input: A poset with any type of relation C (minimal, maximal, etc.)
--output:  A new poset P with the minimal relations

coveringRelationsPoset:=(P) -> (
     L=poset(P.GroundSet,coveringRelations(P))
     )

--------------------------------------------------
--Minimal Element Construction
--------------------------------------------------

minimalElementIndex:=(P)-> (
     M:=RelationMatrix(P);
     nonnull(apply(numcols(M), k-> if (apply(numcols(M), j-> (sum((apply(numrows(M),i-> (transpose(M))_i))))_j))#k==1 then k))
     )

minimalElements:=(P) -> (
     L:=minimalElementIndex(P);
     apply(#L,i-> P.GroundSet#(L#i))
     )

PosetMinusMins:=(P)-> (
     L:=minimalElements(P);
     K:=fullPoset(P);
     N:=set{};
     S:=apply(#L, j-> apply(#K.CRelations,i->(K.CRelations#i)#0===L#j));
     E:=sum set nonnull(apply(#K.CRelations,l->if member(true,set apply(#L,k->S#k#l)) then N=N+set{K.CRelations#l}));
     C:=toList (set(K.CRelations)-N);
     I:=toList (set(K.GroundSet)-set(L));
     poset(I,C)
     )



--------------------------------------------------
--Order and Filter Ideals
--------------------------------------------------

-- input: a poset, and an element from I
-- output: the order ideal of a, i.e. all elements in the poset that are >= a
-- usage:
OrderIdeal:= (P, a) -> (
     M:=RelationMatrix (P);
     aindex := indexElement (P,a);
     GreaterThana:= entries((transpose(M))_aindex);
     nonnull(apply(#GreaterThana, i-> if GreaterThana_i == 1 then P.GroundSet#i)) 
     )	
	   

-- input: a poset, and an element from I
-- output:  the filter of a, i.e. all elements in the poset that are <= a
-- usage:
Filter:=(P,a) -> (
     M:=RelationMatrix (P);
     aindex := indexElement (P,a);
     LessThana:= entries M_aindex;
     nonnull(apply(#LessThana, i-> if LessThana_i == 1 then P.GroundSet#i))
     )



beginDocumentation()

document { Key => Poset,
     Headline => "Betti diagram routines",
     EM "BoijSoederberg", " is a package designed to help with the investigation of 
     the Boij-Soederberg conjectures and theorems.  For the definitions and conjectures, see
     math.AC/0611081, \"Graded Betti numbers of Cohen-Macaulay modules and 
     the Multiplicity conjecture\", by Mats Boij, Jonas Soederberg."
                    }
end

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


