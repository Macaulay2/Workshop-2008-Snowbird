needsPackage "SimplicialComplexes"

newPackage("EdgeIdeals", 
           Version => "0.1",
           Date => "July 1, 2008",
           Authors => {
		       {Name => "Christopher Francisco", 
                        Email => "chris@math.okstate.edu",
                        HomePage => "http://www.math.okstate.edu/~chris/"
                       },
		       {Name => "Andrew Hoefel", 
                        Email => "handrew@mathstat.dal.ca",
                        HomePage => "http://andrew.infinitepigeons.org/"
                       },
		       {Name => "Adam Van Tuyl", 
                        Email => "avantuyl@sleet.lakeheadu.ca",
                        HomePage => "http://flash.lakeheadu.ca/~avantuyl/"
                       }
                      },
           Headline => "a package for edge ideals.",
           DebuggingMode => true
          )

needsPackage "SimplicialComplexes"
needsPackage "SimpleDoc"

export {HyperGraph, 
        hyperGraph, 
	Graph,
	graph,
	adjacencyMatrix,
	allOddHoles,
	allEvenHoles,
	antiHole,
	chromaticNumber,
	cliqueComplex,
	cliqueNumber,
	coverIdeal,
	complementGraph,
	completeGraph,
	completeMultiPartite,
	connectedComponents,
	cycle,
	degreeVertex,
	deleteEdges,
	edgeIdeal,
	edges, 
	getCliques,
	getEdge,
	getEdgeIndex,
	getGoodLeaf,
	getGoodLeafIndex,
	getMaxCliques,
	hasGoodLeaf,
	hasOddHole,
	hyperGraphToSimplicialComplex,
	incidenceMatrix,
	independenceComplex,
	independenceNumber,
	inducedGraph,
      	isBipartite,
	isChordal,
	isCMHyperGraph,
	isConnected,
	isEdge,
	isGoodLeaf,
	isGraph,
	isLeaf,
	isPerfect,
	isSCMHyperGraph,
	isTree,
	lineGraph,
	neighborSet,
	numConnectedComponents,
	numTriangles,
     	randomGraph,
	randomHyperGraph,
	randomUniformHyperGraph,
	simplicialComplexToHyperGraph,
	smallestCycleSize,
	spanningTree,
	vertexCoverNumber,
	vertexCovers,
	vertices
        };

----------------------------------------------------------------------------------------
--
-- TYPES
--
----------------------------------------------------------------------------------------

----------------------------------------------------------------------------------------
-- HyperGraph
----------------------------------------------------------------------------------------

HyperGraph = new Type of HashTable;
hyperGraph = method(TypicalValue => HyperGraph);

hyperGraph (PolynomialRing, List) := HyperGraph => (R, E) -> ( 
     -- Output: HyperGraph over R with edges E
     -- Assert: R is a polynomial ring
     -- Assert: E is a List of Lists of variables of R or
     --         E is a List of square-free monomials in R 
     if any(E, e -> class e =!= List) and any(E, e -> class class e =!= PolynomialRing)
     then ( print apply(E, e -> class e) ;error "Edges must be lists of varibles or monomials.");

     V := gens R;
     --- check needed for square free 
     if any(E, e-> class class e === PolynomialRing) then E = apply(E, support);
     E = apply(E, unique); --- Enforces square-free if edges are given as lists
     H := new HyperGraph from hashTable({"ring" => R, "vertices" => V, "edges" => E});
     if any(H#"edges", e -> not instance(e, List)) then error "Edges must be lists.";
     if any(H#"edges", e -> not isSubset(e,H#"vertices")) then error "Edges must be subsets of the vertices.";
     if any(0..#(H#"edges") -1, I -> 
	  any(0..I-1, J-> isSubset(H#"edges"#I, H#"edges"#J) or isSubset(H#"edges"#J, H#"edges"#I))
     	  )
     then error "Edges satisfy a inclusion relation";
     return H;
)

hyperGraph (MonomialIdeal) := HyperGraph => (I) -> 
( 
     if not isSquareFree I then error "Ideals must be square-free.";
     hyperGraph(ring I, apply(flatten entries gens I, support))
)

hyperGraph (Ideal) := HyperGraph => (I) -> 
( 
     hyperGraph monomialIdeal I
)

hyperGraph (List) := HyperGraph => (E) -> 
( 
     M := null; 	
     if all(E, e-> class e === List) then M = monomialIdeal apply(E, product);
     if all(E, e-> class class e === PolynomialRing) then M = monomialIdeal E;
     if M === null then error "Edge must be represented by a list or a monomial.";
     if #E =!= numgens M then error "Edges satisfy an inclusion relation."; 
     hyperGraph M
)


----------------------------------------------------------------------------
-- Graph
----------------------------------------------------------------------------

Graph = new Type of HyperGraph;

graph = method(TypicalValue => Graph);

graph (PolynomialRing, List) := Graph => (R, E) ->
(
     H := hyperGraph(R, E);
     if not isGraph(H) then error "Edges must be of size two.";
     new Graph from H
)	

graph (MonomialIdeal) := Graph => (I) -> 
(
     H := hyperGraph(I);
     if not isGraph(H) then error "Ideal must have quadratic generators.";
     new Graph from H
)	

graph (Ideal) := Graph => (I) -> 
(
     H := hyperGraph(I);
     if not isGraph(H) then error "Ideal must have quadratic generators.";
     new Graph from H
)	

graph List := Graph => E -> 
(
     H := hyperGraph(E);
     if not isGraph(H) then error "Edges must be of size two.";
     new Graph from H
)	

graph (HyperGraph) := Graph => (H) -> 
(
     if not isGraph(H) then error "Edges must be of size two.";
     new Graph from H
)	

hyperGraph (Graph) := HyperGraph => (G) -> 
(
     new HyperGraph from G
)	


-------------------------------------------------------------------
--
-- FUNCTIONS
--
------------------------------------------------------------------




--------------------------------------------------------------
-- Mathematical equality 
-- return true if two graphs are equal (defined over same ring,
-- have same edge sets in some order).
--------------------------------------------------------------

HyperGraph == HyperGraph := (G,H) -> (
     G#"ring" == H#"ring" and
     set(G#"vertices") === set(H#"vertices") and
     set(apply(G#"edges", set)) === set(apply(H#"edges",set))
     ) 

--------------------------------------------------------------
-- adjacencyMatrix
-- return the adjacency matrix of a graph
--------------------------------------------------------------

adjacencyMatrix = method();

adjacencyMatrix Graph := G -> (
     vert:= G#"vertices";
     n := #vert;
     m := toList apply(0..n-1,i-> toList apply(0..n-1,j-> if isEdge(G,{vert_i,vert_j}) then 1 else 0));  
     return (matrix m)
     )


------------------------------------------------------------
-- allEvenHoles
-- returns a list of even induced cycles
-- NOTE:  this function will be SLOWWW!
-----------------------------------------------------------

allEvenHoles = method();


--------------------------------------------------------------
-- allOddHoles
-- returns a list of all the odd holes in a graph
--------------------------------------------------------------

allOddHoles = method();
allOddHoles Graph := G -> (
     coverI:=coverIdeal G;
     select(ass coverI^2,i->codim i > 3)
     )


-------------------------------------------------------------------
-- antiHole
-- return the graph of an anti-hole
-- AVT:  I think this should be anti-cycle
------------------------------------------------------------------

antiHole = method();

---------------------------------------------------------------
-- chromaticNumber
-- returns the chromatic number of a (hyper)graph
-- NOTE: based upon work in progress by Francisco-Ha-Van Tuyl
---------------------------------------------------------------

chromaticNumber = method();
chromaticNumber HyperGraph := H -> (
     Chi := 2; -- assumes graph has at least one edge
     m := product H#"vertices";
     j := coverIdeal H;
     while ((m^(Chi-1) % j^Chi) != 0) do (
	  Chi = Chi + 1;
	  );
     return (Chi); 
     )


---------------------------------------------------------------
-- cliqueComplex
-- return the simplicial complex whose faces are the cliques of a graph
---------------------------------------------------------------
cliqueComplex =method();
cliqueComplex Graph := G -> independenceComplex complementGraph G;


-------------------------------------------------
-- cliqueNumber
-- return the clique number of a graph
------------------------------------------------

cliqueNumber = method();
cliqueNumber Graph := G -> (
     #(last getCliques G)
     )


---------------------------------------------------------------
-- complementGraph
-- returns the complement of a graph or hypergraph
-- NOTE:  does something different for graphs vs hyerpergraphs
--------------------------------------------------------------

complementGraph = method();
complementGraph Graph := G -> (
     v := G#"vertices";
     alledges := set(subsets(v,2));
     gedges := set G#"edges";
     gcedges := alledges - gedges;  -- edges of the complement
     return(graph toList gcedges);
     )

complementGraph HyperGraph := H -> (
     hcedge := apply(H#"edges",e-> toList (set(H#"vertices") - set e));  -- create edge set of hypergraph
     return (hyperGraph toList hcedge);
     )




----------------------------------------------------------------------
-- completeGraph
-- return graph of complete n-graph
----------------------------------------------------------------------

completeGraph = method();
completeGraph (Ring) := Graph =>(R) -> completeGraph(generators R)

completeGraph (Ring, ZZ) := Graph =>(R, N) -> completeGraph(apply(N, i->R_i))

completeGraph (List) := Graph =>(L)-> (
     if #L === 0 then error "Cannot construct complete graph on no vertices";
     E := for i from 0 to #L -2 list
     for j from i+1 to #L-1 list
     L#i * L# j;
     graph(R, flatten E)
     )     


--------------------------------------------------------------------------
-- completeMultiPartite
-- return the complete multi-partite graph
--------------------------------------------------------------------------

completeMultiPartite = method();



-----------------------------------------------------------------------
-- connectedComponents
-- returns all the connected components of a graph
----------------------------------------------------------------------

connectedComponents = method();



----------------------------------------------------------------------
-- coverIdeal
-- return the Alexander dual of edge ideal, otherwise known as the cover ideal
------------------------------------------------------------------------
coverIdeal = method();
coverIdeal HyperGraph := H -> dual edgeIdeal H




----------------------------------------------------------------------------
-- cycle
-- return graph of the cycle on n vertices
---------------------------------------------------------------------------

cycle = method(TypicalValue=>Graph);
cycle (Ring) := Graph =>(R) -> cycle(generators R)

cycle (Ring, ZZ) := Graph =>(R, N) -> cycle(apply(N, i->R_i))

cycle (List) := Graph =>(L)-> (
     if #L < 3 then error "Cannot construct cycles of length less than three";
     graph(ring L#0,append(apply(#L-1, i-> L#i*L#(i+1)), (last L)*(first L)))
     )     	   


----------------------------------------------------------------------
-- degreeVertex
-- returns the degree of a vertex
----------------------------------------------------------------------

degreeVertex = method();
degreeVertex (HyperGraph, ZZ) := (H,N) ->	(
		degreeVertex(H, (H#"ring")_N)
	)
degreeVertex (HyperGraph, RingElement) := (H,V) ->	(
		use H#"ring";
		N := index V;
		if N === null then error "Variable is not a vertex of the given HyperGraph";
		number(H#"edges", E-> member(V,E))
	)

----------------------------------------------------------------------------------
-- deleteEdges
-- remove edges from a (hyper)graph
----------------------------------------------------------------------------------
deleteEdges = method();

deleteEdges (HyperGraph,List) := (H,E) -> (
     if (isSubset(set E,set H#"edges") =!= true) then error "Second argument must be a subset of the edges, entered as a list";
     newedges:=set(H#"edges")-set(E);
     return (hyperGraph toList newedges)
     )

deleteEdges (Graph,List) := (H,E) -> (graph deleteEdges (hyperGraph(H),E))


----------------------------------------------------------------------
-- edgeIdeal
-- return the edge ideal of a graph or hypergraph
----------------------------------------------------------------------

edgeIdeal = method();
edgeIdeal HyperGraph := H -> (monomialIdeal apply(H#"edges",product)) 


------------------------------------------------------------
-- edges
-- returns edges of a (hyper)graph
------------------------------------------------------------

edges = method();
edges HyperGraph := H -> H#"edges";


----------------------------------------------------------------
-- getCliques
-- return all cliques of the graph
----------------------------------------------------------------

getCliques = method();
getCliques (Graph,ZZ) := (G,d) -> (
     subs:=apply(subsets(G#"vertices",d),i->subsets(i,2));
     cliqueIdeals:=apply(subs,i->ideal apply(i,j->product j));
     edgeId:=edgeIdeal G;
     apply(select(cliqueIdeals,i->isSubset(i,edgeId)),j->support j)
       )

getCliques Graph := G -> (
     numVerts:=#(G#"vertices");
     cliques:={};
     count:=2;
     while count <= numVerts do (
	  newCliques:=getCliques(G,count);
	  if newCliques == {} then return flatten cliques;
	  cliques=append(cliques,newCliques);
	  count=count+1;
	  );
     flatten cliques
     )


------------------------------------------------------------
-- getEdge
-- return a specific edge
------------------------------------------------------------

getEdge = method();
getEdge (HyperGraph, ZZ) := (H,N) -> H#"edges"#N;

------------------------------------------------------------
-- getEdgeIndex
-- returns position of a given edge in a list of edges
------------------------------------------------------------

getEdgeIndex = method();
getEdgeIndex (HyperGraph, List) := (H,E) -> ( 
	if class class E === PolynomialRing then E = support E;
	N :=  select(0..#(H#"edges")-1, N -> set H#"edges"#N === set E);
  if #N === 0 then return -1; 
  return first N;
)

getEdgeIndex (HyperGraph, RingElement) := (H,E) -> ( 
	getEdgeIndex(H, support E)
)

-----------------------------------------------------------
-- getGoodLeaf
-- return a "Good Leaf" of a hypergraph
----------------------------------------------------------

getGoodLeaf = method();
getGoodLeaf HyperGraph := H ->
( return H#"edges"#(getGoodLeafIndex H);
);


------------------------------------------------------------
-- getGoodLeafIndex
-- return the index of a "Good Leaf" in a hypergraph
------------------------------------------------------------

getGoodLeafIndex = method();
getGoodLeafIndex HyperGraph := H ->
(  GL := select(0..#(H#"edges")-1, N -> isGoodLeaf(H,N));
   if #GL == 0 then return -1;
   return first GL;
);

--------------------------------------------------------------------------
-- getMaxCliques
-- return all cliques of maximal size
--------------------------------------------------------------------------

 -- return all cliques of maximal size
getMaxCliques = method();
getMaxCliques Graph := G -> (
     cliqueList:=getCliques G;
     clNum:=#(last cliqueList);
     select(cliqueList,i->#i == clNum)
     )


-----------------------------------------------------------------------------
-- hasGoodLeaf
-- checks if a hypergraph has any "Good Leaves"
----------------------------------------------------------------------------

hasGoodLeaf = method();
hasGoodLeaf HyperGraph := H -> any(0..#(H#"edges")-1, N -> isGoodLeaf(H,N));


------------------------------------------------------------------------------
-- hasOddHole
-- checks if a graph has an odd hole (not triangle)
-----------------------------------------------------------------------------

hasOddHole = method();
hasOddHole Graph := G -> (
     coverI:=coverIdeal G;
     any(ass coverI^2,i->codim i > 3)
     )     

--------------------------------------------------
-- hyperGraphToSimplicialComplex
-- change the type of a (hyper)graph to a simplicial complex
---------------------------------------------------
hyperGraphToSimplicialComplex = method()
hyperGraphToSimplicialComplex HyperGraph := H -> (
     simplicialComplex flatten entries gens edgeIdeal H
     )




-----------------------------------------------------------------------------
-- incidenceMatrix
-- return the incidence matrix of a graph
-----------------------------------------------------------------------------

incidenceMatrix = method();


-------------------------------------------------------------------------------
-- independenceComplex
-- returns the simplicial complex whose faces are the independent sets of a (hyper)graph
--------------------------------------------------------------------------------
independenceComplex =method();

independenceComplex HyperGraph := H -> (simplicialComplex edgeIdeal H)


------------------------------------------------------------------
-- independenceNumber
-- return the independence number, the size of the largest independent set of a vertices
------------------------------------------------------------------

independenceNumber = method();
independenceNumber Graph:= G -> (
     return (dim edgeIdeal G);
     )


--------------------------------------------------------------------------------
-- inducedGraph
-- given a set of vertices, return induced graph on those vertices
--------------------------------------------------------------------------------
inducedGraph = method();

inducedGraph (Graph,List) := (G,S) -> graph inducedGraph(hyperGraph(G), S)

inducedGraph (HyperGraph,List) := (H,S) -> (
     if (isSubset(set S, set H#"vertices") =!= true) then error "Second argument must be a subset of the vertices";
     ie := select(H#"edges",e -> isSubset(set e,set S));
     R := (coefficientRing H#"ring")[S];
     F := map(R,H#"ring");
     ienew := apply(ie,e -> apply(e,v->F(v)));
		 use H#"ring";
     return(hyperGraph(R,ienew));
     )


-----------------------------------------------------------
-- isBipartite
-- checks if a graph is bipartite
-----------------------------------------------------------

isBipartite = method();
isBipartite Graph := G -> (chromaticNumber G == 2); -- checks if chromatic number is 2


-------------------------------------------------------------
-- isChordal
-- check if a graph is a chordal graph
-------------------------------------------------------------

isChordal = method(); -- based upon Froberg's characterization of chordal graphs


-------------------------------------------------------------
-- isCMhyperGraph
-- checks if a (hyper)graph is Cohen-Macaulay
------------------------------------------------------------

isCMhyperGraph = method();



------------------------------------------------------------
-- isConnected
-- checks if a graph is connected
-- (the graph is connected <=> A, the adjacency the matrix,
-- and I, the identity matrix of size n, has the 
-- property that (A+I)^{n-1} has no zero entries)
------------------------------------------------------------

isConnected = method();
isConnected HyperGraph := H -> numConnectedComponents H == 1


------------------------------------------------------------
-- isEdge
-- checks if a set is an edge of a (hyper)graph
------------------------------------------------------------

isEdge = method();
isEdge (HyperGraph, List) := (H,E) -> (
		if class class E === PolynomialRing then E = support E;
		any(H#"edges", G->set G === set E)
	)
isEdge (HyperGraph, RingElement) := (H,E) -> (
		isEdge(H, support E)
	)

-------------------------------------------------------------
-- isGoodLeaf
-- checks if the n-th edge of a hypergraph is a "Good Leaf"
----------------------------------------------------------

isGoodLeaf = method();
isGoodLeaf (HyperGraph, ZZ) := (H,N) -> ( 
     intersectEdges := (A,B) -> set H#"edges"#A * set H#"edges"#B;
     overlaps := apply(select(0..#(H#"edges")-1, M -> M =!= N), M -> intersectEdges(M,N));
     overlaps = sort(overlaps);
     --Check if the overlaps are totally ordered
     all(1..(#overlaps -1), I -> overlaps#(I-1) <= overlaps#I)
     );

------------------------------------------------------------
-- isGraph
-- checks if a hypergraph is a graph
------------------------------------------------------------

isGraph = method();
isGraph HyperGraph := Boolean => (H) -> (
		all(H#"edges", e-> #e === 2 )
	)


--------------------------------------------------------------
-- isLeaf
-- checks if the n-th edge of the (hyper)graph is a leaf
--------------------------------------------------------------

isLeaf = method();
isLeaf (HyperGraph, ZZ) := (H,N) -> ( 
     intersectEdges := (A,B) -> set H#"edges"#A * set H#"edges"#B;
     overlaps := apply(select(0..(#(H#"edges")-1), M -> M =!= N), M -> intersectEdges(M,N));
     overlapUnion := sum toList overlaps;
     any(overlaps, branch -> isSubset(overlapUnion,branch))
     );     

isLeaf (Graph, ZZ) := (G,N) -> ( 
     any(G#"edges"#N, V -> degreeVertex(G,V) === 1)
     ---Note N refers to an edge index
     );

isLeaf (Graph, RingElement) := (G,V) -> ( 
     isLeaf(G,index V)
     ---Note V refers to a vertex
);


------------------------------------------------------------
-- isPerfect
-- checks if a graph is a perfect graph
------------------------------------------------------------

isPerfect = method();
isPerfect Graph := G -> (
     if hasOddHole G then return false;
     if hasOddHole complementGraph G then return false;
     return true;
     )

------------------------------------------------------------
-- isSCMhyperGraph
-- checks if (hyper)graph is Sequentially Cohen-Macaulay
-------------------------------------------------------------

isSCMhyperGraph = method();


-------------------------------------------------------------
-- isTree
-- checks if a graph is a tree
-- NOTE:  should write a function for simplicial trees
------------------------------------------------------------

isTree = method();
isTree Graph := G -> (smallestCycleSize G == 0);

------------------------------------------------------------------
-- lineGraph
-- return the graph with E(G) as its vertices where two
--  vertices are adjacent when their associated edges are adjacent in G.
------------------------------------------------------------------

lineGraph = method();


-----------------------------------------------------------
-- neighborSet
-- returns all the neighbors of a vertex or a set
-----------------------------------------------------------

neighborSet = method();

------------------------------------------------------------
-- numConnectedComponents
-- the number of connected components of a (hyper)Graph
------------------------------------------------------------

numConnectedComponents = method();
numConnectedComponents HyperGraph:= H -> (rank HH_0 hyperGraphToSimplicialComplex H)+1

-----------------------------------------------------------
-- numTrianges
-- returns the number of triangles in a graph
-----------------------------------------------------------

numTriangles = method();
numTriangles Graph := G -> (
     number(ass (coverIdeal G)^2,i->codim i==3)
     )

-----------------------------------------------------------
-- randomGraph
-- returns a graph with a given vertex set and randomly chosen
-- edges with the user determining the number of edges
-----------------------------------------------------------
randomGraph = method();
randomGraph (PolynomialRing,ZZ) := (R,num) -> (
     graph randomUniformHyperGraph(R,2,num)
     )

-----------------------------------------------------------
-- randomHyperGraph
-- returns a hypergraph on a given vertex set and randomly
-- chosen edges of given cardinality
-- NOTE: currently conflicts with inclusion error 
-----------------------------------------------------------

randomHyperGraph = method();
randomHyperGraph (PolynomialRing,List) := (R,li) -> (
     if not all(li,i->instance(i,ZZ) and i > 0) then error "cardinalities of hyperedges must be positive integers";
     verts:=flatten entries vars R;
     if any(li,i->i>#verts) then error "cardinality of at least one hyperedge is too large";
     cards:=sort li;
     uniques:=unique cards;
     numCards:=#uniques;
     edgeList:={};
     count:=0;
     while count < numCards do (
	  subs:=subsets(verts,uniques#count);
	  edgeList=append(edgeList,take(random subs,number(cards,i->i==uniques#count)));
     	  count=count+1;
	  );
     hyperGraph(R,flatten edgeList)
     )	  

-----------------------------------------------------------
-- randomUniformHyperGraph
-- returns a random hypergraph on a given vertex set
-- user chooses cardinality of edges and the number of edges
-----------------------------------------------------------

randomUniformHyperGraph = method();
randomUniformHyperGraph (PolynomialRing,ZZ,ZZ) := (R,card,num) -> (
     randomHyperGraph(R,toList(num:card))
     )



--------------------------------------------------
-- simplicialComplexToHyperGraph
-- change the type of a simplicial complex to a (hyper)graph
---------------------------------------------------

simplicialComplexToHyperGraph = method()

simplicialComplexToHyperGraph SimplicialComplex := D -> (
	  hyperGraph flatten entries facets D
	  )




------------------------------------------------------
-- smallestCycleSize
-- length of smallest induced cycle in a graph
-------------------------------------------------------
smallestCycleSize = method();

smallestCycleSize Graph := G -> (
     if numTriangles G =!= 0 then return(3);
     R :=  res edgeIdeal complementGraph G;
     smallestCycle:=0;
     i := 1;
     -- this loop determines if there is a non-linear syzygy
     -- the first non-linear syzygy tells us the smallest induced
     -- cycle has lenght >= 4.  This is based upon 
     -- the paper of Eisenbud-Green-Hulek-Popescu,
     -- "Restricting linear syzygyies: algebra and geometry"
     while  ((smallestCycle == 0) and (i <= pdim betti R)) do (
	  A := R_i;
          B := flatten degrees A     ;
	  t := tally B;
	  if (t #? (i+1)) then (
               d := rank A;
	       if d == t#(i+1) then i = i+1 else smallestCycle = i+2;
               )	   
       	  else smallestCycle = i+2;     
       );
     -- If the resolution is linear, smallestCycle still has the value of 0
     -- Because the resolution is linear, the graph is chordal, by
     -- a result of Froberg.  Since we have taken care of the case
     -- that G has a triangle, the graph will be a tree.
     return (smallestCycle);
     );	 



------------------------------------------------------------
-- spanningTree
-- returna a spanning tree of a graph
-----------------------------------------------------------

spanningTree = method();
spanningTree Graph:= G-> (
     if (not isConnected G) then error "The graph must be connected";
     eG := G#"edges";
     numVert:=#G#"vertices";
     eT := {eG_0};
     count:=1;
     while #eT < numVert-1 do (
	  eTemp := append(eT,eG_count);
	  while (smallestCycleSize (graph eTemp) > 0) do (
	       count =count+1;
	       eTemp = append(eT,eG_count);
	       );
	  count = count+1;
	  eT = eTemp;
	  );
     spanTree = graph eT;
     return (spanTree);
     );


----------------------------------------------------
-- vertexCoverNumber
-- return the vertex cover number of a (hyper)graph
---------------------------------------------------

vertexCoverNumber = method();
vertexCoverNumber HyperGraph := H -> (
     min apply(flatten entries gens coverIdeal H,i->first degree i)
     )

----------------------------------------
-- vertexCovers
-- return all minimal vertex covers 
-- (these are the generators of the Alexander dual of the edge ideal)
----------------------------------------

vertexCovers  = method();
vertexCovers HyperGraph := H -> (
     flatten entries gens coverIdeal H
     )

-----------------------------------------
-- vertices
-- returns the vertices of the (hyper)graph
--------------------------------------------

vertices = method();
vertices HyperGraph := H -> H#"vertices";


---------------------------------------------------------
---------------------------------------------------------
-- Simple Doc information
---------------------------------------------------------
---------------------------------------------------------

--*******************************************************
-- DOCUMENTATION FOR TYPES
--*******************************************************

---------------------------------------------------------
-- DOCUMENTATION HyperGraph
---------------------------------------------------------


doc ///
	Key
		HyperGraph
	Headline 
		a class for hypergraphs.
///

doc ///
	Key
		Graph
	Headline 
		a class for graphs.
	Description
		Text
			This class represents simple graphs. This class extends @TO HyperGraph@ and hence
			inherits all HyperGraph methods.
	SeeAlso
		HyperGraph
///


---------------------------------------------------------
-- DOCUMENTATION hyperGraph
---------------------------------------------------------

doc ///
	Key
		hyperGraph
		(hyperGraph, PolynomialRing, List)
		(hyperGraph, MonomialIdeal)
		(hyperGraph, Ideal)
		(hyperGraph, List)
		(hyperGraph, Graph)
	Headline 
		constructor for HyperGraph.
	Usage
		H = hyperGraph(R,E) \n H = hyperGraph(I) \n H = hyperGraph(E) \n H = hyperGraph(G)
	Inputs
		R:PolynomialRing
			whose variables correspond to vertices of the hypergraph.
		E:List
			contain a list of edges, which themselves are lists of vertices.
		I:MonomialIdeal
			which must be square-free and whose generators become the edges of the hypergraph.
		J:Ideal
			which must be square-free monomial and whose generators become the edges of the hypergraph.
		G:Graph
			which is to be converted to a HyperGraph.
	Outputs 
		H:HyperGraph
///


---------------------------------------------------------
-- DOCUMENTATION graph
---------------------------------------------------------

doc ///
	Key
		graph
		(graph, PolynomialRing, List)
		(graph, MonomialIdeal)
		(graph, Ideal)
		(graph, List)
		(graph, HyperGraph)
	Headline 
		constructor for Graph.
	Usage
		G = graph(R,E) \n G = graph(I) \n G = graph(E) \\ G = graph(H)
	Inputs
		R:PolynomialRing
			whose variables correspond to vertices of the hypergraph.
		E:List
			contain a list of edges, which themselves are lists of vertices.
		I:MonomialIdeal
			which must be square-free and whose generators become the edges of the hypergraph.
		J:Ideal
			which must be square-free monomial and whose generators become the edges of the hypergraph.
		H:HyperGraph
			which is to be converted to a graph. The edges in {\tt H} must be of size two.
	Outputs 
		G:Graph
///



---------------------------------------------------------------------------------------------

--**********************************************************
-- DOCUMENTATION FOR FUNCTIONS
--**********************************************************

	      
------------------------------------------------------------
-- DOCUMENTATION equality  ==
------------------------------------------------------------

doc ///
        Key
		(symbol ==, HyperGraph, HyperGraph)
	Headline
	        equality 
	Usage
	        g == h
	Inputs
	        g:HyperGraph
	        h:HyperGraph
	Outputs
	        b:Boolean
		       true if g and h are equal
        Description
	        Text
		       This function determines if two HyperGraphs are mathematically equal.
		       Two HyperGraphs are equal if they are defined over the same ring, have 
                       the same variables and have the same set of edges. In particular, 
                       the order of the edges and the order of variables within each edges 
                       does not matter.
		Example
                       R = QQ[a..f];
		       g = hyperGraph {{a,b,c},{b,c,d},{d,e,f}};
		       h = hyperGraph {{b,c,d},{a,b,c},{f,e,d}};
		       k = hyperGraph {{a,b},{b,c,d},{d,e,f}};
		       g == h
		       g == k
///

--document {
--     Key => symbol ==,
--     Headline => "equality",
--     Usage => "g==h",
--     Inputs => {
--                "g" => HyperGraph, 
--                "h" => HyperGraph
--          },
--     Outputs => {
--                Boolean => { "true if ", TT, "g", " and ", TT, "h", " are equal."}
--          },
--		       "This function determines if two HyperGraphs are mathematically equal.
--		       Two HyperGraphs are equal if they are defined over the same ring, have 
--                       the same variables and have the same set of edges. In particular, 
--                       the order of the edges and the order of variables within each edges 
--                       does not matter.",
--     EXAMPLE ///       R = QQ[a..f]
--		       g = hyperGraph {a*b*c,b*c*d,d*e*f}
--		       h = hyperGraph {b*c*d,a*b*c,f*e*d}
--		       k = hyperGraph {a*b,b*c*d,d*e*f}
--		       g == h
--		       g == k
--          ///
--     }
	      
------------------------------------------------------------
-- DOCUMENTATION adjacencyMatrix
------------------------------------------------------------

doc ///
        Key
	        adjacencyMatrix
		(adjacencyMatrix, Graph)
	Headline
	        returns the adjacency Matrix of a graph
	Usage
	        m = adjacencyMatrix g
	Inputs
	        g:Graph
	Outputs
	        m:Matrix
		       the adjacency matrix of the graph
        Description
	        Text
		       This function returns the adjacency matrix of the inputed graph.  The (i,j)^{th} position
		       of the matrix is 1 if there is an edge between the i^{th} vertex and j^{th} vertex,
		       and 0 otherwises.  The rows and columns are indexed by the variables of the ring and uses the 
		       ordering of the variables for determining the order of the rows and columns.
		Example
                       S = QQ[a..f]
		       g = graph {a*b,a*c,b*c,c*d,d*e,e*f,f*a,a*d}
		       t = adjacencyMatrix g	  
		       T = QQ[f,e,d,c,b,a]
		       g = graph {a*b,a*c,b*c,c*d,d*e,e*f,f*a,a*d}
		       t = adjacencyMatrix g -- although the same graph, matrix is different since variables have different ordering
		
///		      

------------------------------------------------------------
-- DOCUMENTATION allOddHoles
------------------------------------------------------------

doc ///
	Key
		allOddHoles
		(allOddHoles, Graph)
	Headline 
		returns all odd holes in a graph
	Usage
		L = hasOddHole G
	Inputs
		G:Graph
	Outputs 
		L:List
			returns all odd holes contained in {\tt G}.
	Description
	     Text
	     	  The method is based on work of Francisco-Ha-Van Tuyl, looking at the associated primes
		  of the square of the Alexander dual of the edge ideal. An odd hole is an odd induced
		  cycle of length at least 5.
	     Example
	     	  R=QQ[x_1..x_6]
		  G=graph({x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_1*x_5,x_1*x_6,x_5*x_6}) --5-cycle and a triangle
		  allOddHoles G --only the 5-cycle should appear
		  H=graph({x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_1*x_5,x_1*x_6,x_5*x_6,x_1*x_4}) --no odd holes
		  allOddHoles H
	SeeAlso
	     hasOddHole
///
	      
	      
------------------------------------------------------------
-- DOCUMENTATION chromaticNumber
------------------------------------------------------------

doc ///
        Key
	        chromaticNumber
		(chromaticNumber, HyperGraph)
	Headline
	        computes the chromatic number of a hypergraph
	Usage
	        c = chromaticNumber H
	Inputs
	        H:HyperGraph
	Outputs
	        i:ZZ
		       the chromatic number of {\tt H}
        Description
	        Text
		 Returns the chromatic number.
///		      

------------------------------------------------------------
-- DOCUMENTATION cliqueNumber
------------------------------------------------------------

doc ///
        Key
	        cliqueNumber
		(cliqueNumber, Graph)
	Headline
	        computes the clique number of a graph
	Usage
	        c = chromaticNumber G
	Inputs
	        G:Graph
	Outputs
	        i:ZZ
		       the clique number of {\tt G}
        Description
	        Text
		     cliqueNumber returns the clique number of a graph, the size of the largest clique
		     contained in the graph.
		Example
		     R=QQ[a..d]
		     cliqueNumber completeGraph R
		     G = graph({a*b,b*c,a*c,a*d})
		     cliqueNumber G
		 
	SeeAlso
	     getCliques
	     getMaxCliques
///		      


	      
------------------------------------------------------------
-- DOCUMENTATION complementGraph
------------------------------------------------------------

doc ///
        Key
	        complementGraph
		(complementGraph, Graph)
		(complementGraph, HyperGraph)
	Headline
	        returns the complement of a graph or hypergraph 
	Usage
	        g = complementGraph G \n h = complementGraph H
	Inputs
	        G:Graph
		H:HyperGraph
	Outputs
	        g:Graph
		       the complement of G, whose edges are the set of edges not in G
		h:HyperGraph
		       the complement of H, whose edge set is found by taking the complement of each
		       edge of H in the vertex set
        Description
	        Text
		       complementGraph behaves differently on graphs and hypergraphs
		Example
		       R = QQ[a,b,c,d,e]	   
		       c5 = graph {a*b,b*c,c*d,d*e,e*a} -- graph of the 5-cycle
		       complementGraph c5 -- the graph complement of the 5-cycle
		       c5hypergraph = hyperGraph c5 -- the 5-cycle, but viewed as a hypergraph
		       complementGraph c5hypergraph
	Caveat
	        Notice that {\tt complementGraph} works differently on graphs versus hypergraphs.
///	
	      
------------------------------------------------------------
-- DOCUMENTATION completeGraph
------------------------------------------------------------

doc ///
	Key
		completeGraph
		(completeGraph, Ring)
		(completeGraph, Ring, ZZ)
		(completeGraph, List)
	Headline
		returns a complete graph.
	Usage
		K = cycle R \n K = cycle(R,N) \n K = cycle L
	Inputs
		R:Ring
		N:ZZ
			number of variables to use
		L:List
			of vertices to make into a complete graph
	Outputs
		K:Graph
			which is a complete graph on the vertices in {\tt L} or on the variables of {\tt R}
	Description
		Example
			R = QQ[a,b,c,d,e]	   
			completeGraph R
			completeGraph(R,3)
			completeGraph {a,c,e}
///	

 
	      
------------------------------------------------------------
-- DOCUMENTATION coverIdeal
------------------------------------------------------------

doc ///
        Key
	        coverIdeal
		(coverIdeal, HyperGraph)
	Headline
	        creates the cover ideal of the hypergraph
	Usage
	        i = coverIdeal H
	Inputs
	        H:HyperGraph
	Outputs
	        i:MonomialIdeal
		       the cover ideal of H
        Description
	        Text
		 Returns the monomial ideal generated by the minimal vertex covers.  This is also the Alexander Dual 
		 of the edge ideal of the hypergraph {\tt H}.
///		      

------------------------------------------------------------
-- DOCUMENTATION cycle
------------------------------------------------------------

doc ///
	Key
		cycle
		(cycle, Ring)
		(cycle, Ring, ZZ)
		(cycle, List)
	Headline
		returns a graph cycle.
	Usage
		C = cycle R \n C = cycle(R,N) \n C = cycle L
	Inputs
		R:Ring
		N:ZZ
			length of cycle
		L:List
			of vertices to make into a cycle in the order provided
	Outputs
		C:Graph
			which is a cycle on the vertices in {\tt L} or on the variables of {\tt R}.
	Description
		Example
			R = QQ[a,b,c,d,e]	   
			cycle R
			cycle(R,3)
			cycle {e,c,d,b}
///	


------------------------------------------------------------
-- DOCUMENTATION degreeVertex
------------------------------------------------------------
doc ///
	Key
		degreeVertex
		(degreeVertex, HyperGraph, ZZ)
		(degreeVertex, HyperGraph, RingElement)
	Headline 
		gives degree of a vertex.
	Usage
		D = degreeVertex(H,N) \n D = degreeVertex(H,V)
	Inputs
		H:HyperGraph
		N:ZZ
			the index of a vertex
		V:RingElement
			a vertex/variable of the HyperGraph
	Outputs 
		D:ZZ
			which is the degree of vertex {\tt V} (or vertex number {\tt N})
	Description
		Text
			The degree of a vertex in a hypergraph is the number of edges that contain the vertex.
	SeeAlso
		vertices
///



------------------------------------------------------------
-- DOCUMENTATION deleteEdges
------------------------------------------------------------
 
doc ///
        Key
	        deleteEdges 
		(deleteEdges, Graph, List)
		(deleteEdges, HyperGraph, List)
	Headline
	        returns the graph or hypergraph with specified edges removed
	Usage
	        h = deleteEdges (H,S) \n g = deleteEdges (E,S)
	Inputs
		H:HyperGraph
		G:Graph
		S:List
		     which is a subset of the edges of the graph or hypergraph
	Outputs
		h:HyperGraph
		       the hypergraph with edges in S removed
		g:Graph
		       the graph with edges in S removed
        Description
	        Text
		       Stuff
///	



------------------------------------------------------------
-- DOCUMENTATION edgeIdeal
------------------------------------------------------------


doc ///
        Key
	        edgeIdeal
		(edgeIdeal, HyperGraph)
	Headline
	        creates the edge ideal of the hypergraph
	Usage
	        i = edgeIdeal H
	Inputs
	        H:HyperGraph
	Outputs
	        i:MonomialIdeal
		        the edge ideal of H
///		      



------------------------------------------------------------
-- DOCUMENTATION edges
------------------------------------------------------------


doc ///
	Key
		edges
		(edges, HyperGraph)
	Headline 
		gets the edges of a HyperGraph.
	Usage
		E = edges(H)
	Inputs
		H:HyperGraph
	Outputs 
		E:List
			of the edges of {\tt H}.
///


------------------------------------------------------------
-- DOCUMENTATION getCliques
------------------------------------------------------------

doc ///
	Key
		getCliques
		(getCliques, Graph, ZZ)
		(getCliques, Graph)
	Headline 
		returns cliques in a graph
	Usage
		c = getCliques(G,d) or c = getCliques G
	Inputs
		G:Graph
		d:ZZ
			representing the size of the cliques desired
	Outputs 
		c:List
			of cliques of size {\tt d} or, if no {\tt d} is entered, all cliques.
	SeeAlso
	        cliqueNumber
	Description
		Example
		     	R = QQ[a..d]
			G = completeGraph R 
     	       	    	getCliques(G,3)
			getCliques(G,4)
			getCliques G
	       
///


------------------------------------------------------------
-- DOCUMENTATION getEdge
------------------------------------------------------------

doc ///
	Key
		getEdge
		(getEdge, HyperGraph, ZZ)
	Headline 
		gets the n-th edge in a HyperGraph
	Usage
		E = edges(H,N)
	Inputs
		H:HyperGraph
		N:ZZ
			an index of an edge in {\tt H}
	Outputs 
		E:List
			which is the {\tt N}-th edge of {\tt H}
///

------------------------------------------------------------
-- DOCUMENTATION getEdgeIndex
------------------------------------------------------------

doc ///
	Key
		getEdgeIndex
		(getEdgeIndex, HyperGraph, List)
	Headline 
		finds the index of an edge in a HyperGraph
	Usage
		N = getEdgeIndex(H,E)
	Inputs
		H:HyperGraph
		E:List
			of vertices (or monomials)
	Outputs 
		N:ZZ
			which is the index of {\tt E} as an edge of {\tt H}. If {\tt E} is not in {\tt H}
			then -1 is returned
	SeeAlso
		isEdge
///

------------------------------------------------------------
-- DOCUMENTATION getMaxCliques
------------------------------------------------------------

doc ///
	Key
		getMaxCliques
		(getMaxCliques, Graph)
	Headline 
		returns maximal cliques in a graph
	Usage
		c = getMaxCliques G
	Inputs
		G:Graph
	Outputs 
		c:List
			of cliques of maximal size contained in {\tt G}
	Description
	     	Text
		     The function returns all cliques of maximal size in a graph as a list of lists.
		Example
		     	R = QQ[a..d]
			G = completeGraph R 
     	       	    	getMaxCliques G
			H=graph({a*b,b*c,a*c,c*d,b*d})
			getMaxCliques H
	SeeAlso
	        cliqueNumber
		getCliques
///

------------------------------------------------------------
-- DOCUMENTATION hasOddHole
------------------------------------------------------------

doc ///
	Key
		hasOddHole
		(hasOddHole, Graph)
	Headline 
		tells whether a graph contains an odd hole.
	Usage
		B = hasOddHole G
	Inputs
		G:Graph
	Outputs 
		B:Boolean
			returns {\tt true} if {\tt G} has an odd hole and {\tt false} otherwise
	Description
	     Text
	     	  The method is based on work of Francisco-Ha-Van Tuyl, looking at the associated primes
		  of the square of the Alexander dual of the edge ideal. An odd hole is an odd induced
		  cycle of length at least 5.
	     Example
	     	  R=QQ[x_1..x_6]
		  G=graph({x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_1*x_5,x_1*x_6,x_5*x_6}) --5-cycle and a triangle
		  hasOddHole G
		  H=graph({x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_1*x_5,x_1*x_6,x_5*x_6,x_1*x_4}) --no odd holes
		  hasOddHole H
	SeeAlso
	     allOddHoles
///



------------------------------------------------------------
-- DOCUMENTATION hyperGraphToSimplicialComplex
------------------------------------------------------------

doc ///
	Key
		hyperGraphToSimplicialComplex
		(hyperGraphToSimplicialComplex, HyperGraph)
	Headline 
		turns a (hyper)graph into a simplicial complex
	Usage
		D = hyperGraphToSimplicialComplex H
	Inputs
		H:HyperGraph
	Outputs 
		D:SimplicialComplex
			whose facets are given by the edges of H
	Description
	     Text
	     	  This function chances the type of a (hyper)graph to a simplicial complex where
		  the facets of the simplicial complex are given by the edge set of the (hyper)graph.
		  This function is the reverse of @TO simplicialComplexToHyperGraph @.  This function enables the users
		  to make use of the functions in the package @TO SimplicialComplexes @
	     Example
	     	  R=QQ[x_1..x_6]
		  G=graph({x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_1*x_5,x_1*x_6,x_5*x_6}) --5-cycle and a triangle
		  DeltaG = hyperGraphToSimplicialComplex G
		  hyperGraphDeltaG = simplicialComplexToHyperGraph DeltaG
	          GPrime = graph(hyperGraphDeltaG)
		  G === GPrime
	SeeAlso
	     simplicialComplexToHyperGraph     
///


------------------------------------------------------------
-- DOCUMENTATION independenceNumber
------------------------------------------------------------


doc ///
        Key
	        independenceNumber
		(independenceNumber, Graph)
	Headline
	        determines the independence number of a graph 
	Usage
	        d = independenceNumber G
	Inputs
	        G:Graph
	Outputs
	        d:ZZ
		       the independence number (the number of independent vertices) in {\tt G}
        Description
	        Text
///	
	      

------------------------------------------------------------
-- DOCUMENTATION inducedGraph
------------------------------------------------------------


doc ///
	Key
		inducedGraph
		(inducedGraph, Graph, List)
		(inducedGraph, HyperGraph, List)
	Headline
		returns the induced subgraph of a graph or hypergraph.
	Usage
		h = inducedGraph H \n g = inducedGraph G
	Inputs
		H:HyperGraph
		G:Graph
		L:List
			of vertices (i.e. variables in the ring of {\tt H} or {\tt G})
	Outputs
		h:HyperGraph
			the induced subgraph of {\tt H} whose edges are contained in {\tt L}
		g:Graph
			the induced subgraph of {\tt G} whose edges are contained in {\tt L}
	Description
		Text
			The ring of the induced subgraph contains only variables in {\tt L}.
			The current ring must be changed before working with the induced subgraph.
		Example
			R = QQ[a,b,c,d,e]	   
			G = graph {a*b,b*c,c*d,d*e,e*a} -- graph of the 5-cycle
			H1 = inducedGraph(G,{b,c,d,e})
			H2 = inducedGraph(G,{a,b,d,e})
			use H1#"ring"
			inducedGraph(H1,{c,d,e})
///	



------------------------------------------------------------
-- DOCUMENTATION isBipartite
------------------------------------------------------------

doc ///
        Key
	        isBipartite
		(isBipartite, Graph)
	Headline
	        determines if a graph is bipartite
	Usage
	        B = isBipartite G
	Inputs
	        G:Graph
	Outputs
	        B:Boolean
		       returns {\tt true} if {\tt G} is bipartite, {\tt false} otherwise
        Description
	        Text
///		      




------------------------------------------------------------
-- DOCUMENTATION isConnected
------------------------------------------------------------

doc ///
        Key
	        isConnected
		(isConnected, HyperGraph)
	Headline
	        determines if a (hyper)graph is connected
	Usage
	        b = isConnected H
	Inputs
	        H:Graph
	Outputs
	        B:Boolean
		       returns {\tt true} if {\tt H} is connected, {\tt false} otherwise
        Description
	        Text
		       This function checks if the (hyper)graph is connected.  It relies on the @TO numConnectedComponents @.
		Example
		       S = QQ[a..e]
		       g = graph {a*b,b*c,c*d,d*e,a*e} -- the 5-cycle (connected)
		       h = graph {a*b,b*c,c*a,d*e} -- a 3-cycle and a disjoint edge (not connected)
		       isConnected g
		       isConnected h
	SeeAlso
	        numConnectedComponents
///		      






------------------------------------------------------------
-- DOCUMENTATION isEdge
------------------------------------------------------------

doc ///
	Key
		isEdge
		(isEdge, HyperGraph, List)
		(isEdge, HyperGraph, RingElement)
	Headline 
		determines if an edge is in a HyperGraph
	Usage
		B = isEdge(H,E) \n B = isEdge(H,M)
	Inputs
		H:HyperGraph
		E:List
			of vertices.
		M:RingElement
			a monomial representing an edge.
	Outputs 
		B:Boolean
			which is true iff {\tt E} (or {\tt support M}) is an edge of {\tt H}
	SeeAlso
		getEdgeIndex
///

------------------------------------------------------------
-- DOCUMENTATION isPerfect
------------------------------------------------------------

doc ///
	Key
		isPerfect
		(isPerfect, Graph)
	Headline 
		determines whether a graph is perfect
	Usage
		B = isPerfect G
	Inputs
		G:Graph
	Outputs 
		B:Boolean
			which is {\tt true} if {\tt G} is perfect and {\tt false} otherwise
        Description
	     Text
	     	  The algorithm uses the Strong Perfect Graph Theorem, which says that {\tt G} is
		  perfect if and only if neither {\tt G} nor its complement contains an odd hole.
		  @TO hasOddHole@ is used to determine whether these conditions hold.
	     Example
     	       	  R=QQ[x_1..x_7]
		  G=complementGraph cycle R; --odd antihole with 7 vertices
		  isPerfect G
		  H=cycle(R,4)
		  isPerfect H
		  	     	  
	SeeAlso
		hasOddHole
///



------------------------------------------------------------
-- DOCUMENTATION numConnectedComponents
------------------------------------------------------------

doc ///
	Key
		numConnectedComponents
		(numConnectedComponents, HyperGraph)
	Headline 
		returns the number of connected components in a (hyper)graph
	Usage
		d = numConnectedComponents H
	Inputs
		H:HyperGraph
	Outputs 
		d:ZZ
			the number of connected components of H
	Description
	     Text
	     	  The function returns the number of connected components of a (hyper)graph.  To count the number of components,
		  the algorithm turns H into a simplicial complex, and then computes the rank of the 0^{th} reduced
		  homology group.  This number plus 1 gives us the number of connected components.
	     Example
	     	   S = QQ[a..e]
		   g = graph {a*b,b*c,c*d,d*e,a*e} -- the 5-cycle (connected)
		   h = graph {a*b,b*c,c*a,d*e} -- a 3-cycle and a disjoint edge (not connected)
		   numConnectedComponents g
		   numConnectedComponents h
	SeeAlso
	     isConnected
///


------------------------------------------------------------
-- DOCUMENTATION numTriangles
------------------------------------------------------------

doc ///
	Key
		numTriangles
		(numTriangles, Graph)
	Headline 
		returns the number of triangles in a graph
	Usage
		d = numTriangles G
	Inputs
		G:Graph
	Outputs 
		d:ZZ
			the number of triangles contained in {\tt G}
	Description
	     Text
	     	  The method is based on work of Francisco-Ha-Van Tuyl, looking at the associated primes
		  of the square of the Alexander dual of the edge ideal. The function counts the number
		  of these associated primes of height 3.
	     Example
	     	  R=QQ[x_1..x_6]
		  G=graph({x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_1*x_5,x_1*x_6,x_5*x_6}) --5-cycle and a triangle
		  numTriangles G
		  H=completeGraph R;
		  numTriangles H == binomial(6,3)
	SeeAlso
	     allOddHoles
	     getCliques
///

------------------------------------------------------------
-- DOCUMENTATION randomGraph
------------------------------------------------------------

doc ///
	Key
		randomGraph
		(randomGraph,PolynomialRing, ZZ)
	Headline 
		returns a random graph
	Usage
		G = randomGraph(R,d)
	Inputs
		R:PolynomialRing
		     which gives the vertex set of {\tt G}
		d:ZZ
		     the number of edges in {\tt G}
	Outputs 
		G:Graph
			a graph with {\tt d} edges on vertex set determined by {\tt R}
	Description
	     Example
	     	  R=QQ[x_1..x_9]
		  randomGraph(R,4)
     	       	  randomGraph(R,4)  
	SeeAlso
	     randomHyperGraph
	     randomUniformHyperGraph
///


------------------------------------------------------------
-- DOCUMENTATION randomHyperGraph
------------------------------------------------------------


------------------------------------------------------------
-- DOCUMENTATION randomUniformHyperGraph
------------------------------------------------------------

doc ///
	Key
		randomUniformHyperGraph
		(randomUniformHyperGraph,PolynomialRing,ZZ,ZZ)
	Headline 
		returns a random uniform hypergraph
	Usage
		H = randomUniformHyperGraph(R,c,d)
	Inputs
		R:PolynomialRing
		     which gives the vertex set of {\tt H}
		c:ZZ
		     the cardinality of the edge sets
		d:ZZ
		     the number of edges in {\tt H}
	Outputs 
		H:HyperGraph
			a hypergraph with {\tt d} edges of cardinality {\tt c} on vertex set determined by {\tt R}
	Description
	     Example
	     	  R=QQ[x_1..x_9]
		  randomUniformHyperGraph(R,3,4)
     	       	  randomUniformHyperGraph(R,4,2)  
	SeeAlso
	     randomGraph
	     randomHyperGraph
///


---------------------------------------------------------
-- DOCUMENTATION simplicialComplexToHyperGraph
----------------------------------------------------------



doc ///
	Key
		simplicialComplexToHyperGraph
		(simplicialComplexToHyperGraph, SimplicialComplex)
	Headline 
		change the type of a simplicial complex to a (hyper)graph
	Usage
		h = simplicialComplexToHyperGraph(D) 
	Inputs
		D:SimplicialComplex
		        the input
	Outputs 		
	        h:HyperGraph
			whose edges are the facets of D
        Description
 	        Text
		        This function takes a simplicial complex and changes it type to a HyperGraph by
			returning a hypergraph whose edges are defined by the facets of the simplicial
			complex.  This is the reverse of the function @TO hyperGraphToSimplicialComplex @
		Example
	                S = QQ[a..f]
			Delta = simplicialComplex {a*b*c,b*c*d,c*d*e,d*e*f}
                        h = simplicialComplexToHyperGraph Delta
        SeeAlso
	        hyperGraphToSimplicialComplex
///
 

---------------------------------------------------------
-- DOCUMENTATION smallestCycleSize
----------------------------------------------------------
 
doc ///
        Key
	        smallestCycleSize 
		(smallestCycleSize, Graph)
	Headline
	        returns the size of the smallest induced cycle of a graph
	Usage
	        s = smallestCycleSize(G)
	Inputs
		G:Graph
		     the input
	Outputs
		s:ZZ
		     the size of the smallest induced cycle
        Description
	        Text
		     This function returns the size of the smallest induced cycle of a graph.
		     It is based upon Theorem 2.1 in the paper "Restricting linear syzygies:
		     algebra and geometry" by Eisenbud, Green, Hulek, and Popsecu.  This theorem
		     states that if G is graph, then the edge ideal of the complement of G satisfies
		     property N_{2,p}, that is, the resolution of I(G^c) is linear up to the p-th step,
		     if and only if, the smallest induced cycle of G has length p+3.  The algorithm
		     looks at the resolution of the edge ideal of the complement to determine the size
		     of the smallest cycle.    	  
		Example      
     	       	     T = QQ[x_1..x_9]
		     g = graph {x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_5*x_6,x_6*x_7,x_7*x_8,x_8*x_9,x_9*x_1} -- a 9-cycle
		     smallestCycleSize g
		     h = graph {x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_5*x_6,x_6*x_7,x_7*x_8,x_8*x_9} -- a tree (no cycles)
		     smallestCycleSize h
		     l =  graph {x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_5*x_6,x_6*x_7,x_7*x_8,x_8*x_9,x_9*x_1,x_1*x_4}
		     smallestCycleSize l
		Text
		     Note that if g is a tree if and only if {\tt smallestCycleSize g = 0}
///






------------------------------------------------------
-- DOCUMENTATION spanningTree
----------------------------------------------------------
 
doc ///
        Key
	        spanningTree 
		(spanningTree, Graph)
	Headline
	        returns a spanning tree of a connected graph
	Usage
	        t = spanningTree(G)
	Inputs
		G:Graph
		     the input
	Outputs
		t:Graph
		     the spanning tree of G
        Description
	        Text
		     This function returns the a spanning tree of a connected graph.  It will
		     not work on unconnected graphs.  The algorithm is very naive;  the first edge
		     of the tree is the first edge of the graph.  The algorithm then successively
		     adds the next edge in the graph, as long as no cycle is created.  The algorithm terminates once (n-1)
		     edges have been added, where n is the number of edges.
		Example      
     	       	     T = QQ[x_1..x_9]
		     g = graph {x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_5*x_6,x_6*x_7,x_7*x_8,x_8*x_9,x_9*x_1} -- a 9-cycle
		     spanningTree g
		     h = graph {x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_5*x_6,x_6*x_7,x_7*x_8,x_8*x_9} -- a tree (no cycles)
		     spanningTree h === h
///









---------------------------------------------------------
-- DOCUMENTATION vertexCoverNumber
---------------------------------------------------------

doc ///
	Key
		vertexCoverNumber
		(vertexCoverNumber, HyperGraph)
	Headline 
		find the vertex covering number of a (hyper)graph
	Usage
		c = vertexCoverNumber(H) 
	Inputs
		H:HyperGraph
		        the input
	Outputs 
		c:ZZ
			the vertex covering number
        Description
	        Text
		        This function takes a graph or hypergraph, and returns the vertex covering number, that is,
			the size of smallest vertex cover of the (hyper)graph.  This corresponds to the smallest
			degree of a generator of the cover ideal of the (hyper)graph.
		Example
	                S = QQ[a..d]
			g = graph {a*b,b*c,c*d,d*a} -- the four cycle
			vertexCoverNumber g
		        S = QQ[a..e]
			g = graph {a*b,a*c,a*d,a*e,b*c,b*d,b*e,c*d,c*e,d*e} -- the complete graph K_5
			vertexCoverNumber g
		      	h = hyperGraph {a*b*c,a*d,c*e,b*d*e}
			vertexCoverNumber(h)
///
 

---------------------------------------------------------
-- DOCUMENTATION vertexCovers
---------------------------------------------------------

doc ///
	Key
		vertexCovers
		(vertexCovers, HyperGraph)
	Headline 
		list the minimal vertex covers of a (hyper)graph
	Usage
		c = vertexCovers(H) 
	Inputs
		H:HyperGraph
		        the input
	Outputs 
		c:List
			of the minimal vertex covers of {\tt H}.  The vertex covers are represented as monomials.
        Description
	        Text
		        This function takes a graph or hypergraph, and returns the minimal vertex cover of the graph or
			hypergraph.   A vertex cover is a subset of the vertices such that every edge of the (hyper)graph has
			non-empty intersection with this set.  The minimal vertex covers are given by the minimal generators
			of the cover ideal of H.
		Example
	                S = QQ[a..d]
			g = graph {a*b,b*c,c*d,d*a} -- the four cycle
			vertexCovers g
		        coverIdeal g
			flatten entries gens coverIdeal g == vertexCovers g
			S = QQ[a..e]
			h = hyperGraph {a*b*c,a*d,c*e,b*d*e}
			vertexCovers(h)
///
 
 
---------------------------------------------------------
-- DOCUMENTATION vertices
---------------------------------------------------------

doc ///
	Key
		vertices
		(vertices, HyperGraph)
	Headline 
		gets the vertices of a (hyper)graph
	Usage
		V = vertices(H) 
	Inputs
		H:HyperGraph
		        the input
	Outputs 
		V:List
			of the vertices of {\tt H}
        Description
	        Text
		        This function takes a graph or hypergraph, and returns the vertex set of the graph.
		Example
	                S = QQ[a..d]
			g = graph {a*b,b*c,c*d,d*a} -- the four cycle
			vertices(g)
			h = hyperGraph{a*b*c}
			vertices(h) -- the vertex d is treated as an isolated vertex
///


-----------------------------
-- Constructor Tests --------
-- Test hyperGraph and Graph
-----------------------------

TEST///
R = QQ[a,b,c]
H = hyperGraph(R, {{a,b},{b,c}})
assert(#(edges H) == 2)
assert(#(vertices H) == 3)
///

TEST///
R = QQ[a,b,c]
H = hyperGraph(R, {{a,b,c}})
assert(#(edges H) == 1)
assert(#(vertices H) == 3)
///

TEST///
R = QQ[a,b,c]
H = hyperGraph(R, {a*b,b*c})
assert(#(edges H) == 2)
assert(#(vertices H) == 3)
///

TEST///
R = QQ[a,b,c]
H = hyperGraph({{a,b},{b,c}})
assert(#(edges H) == 2)
assert(#(vertices H) == 3)
///

TEST///
R = QQ[a,b,c]
H = hyperGraph({a*b,b*c})
assert(#(edges H) == 2)
assert(#(vertices H) == 3)
///

TEST///
R = QQ[a,b,c]
H = hyperGraph(ideal {a*b,b*c})
assert(#(edges H) == 2)
assert(#(vertices H) == 3)
///

TEST///
R = QQ[a,b,c]
H = hyperGraph(monomialIdeal {a*b,b*c})
assert(#(edges H) === 2)
assert(#(vertices H) === 3)
///

-----------------------------
-- Test Equality ==
-----------------------------

TEST///
R = QQ[a,b,c,d]
G1 = hyperGraph(R, {{a,b},{b,c}})
G2 = hyperGraph(R, {{a,b},{b,c}})
G3 = hyperGraph(R, {{a,b},{c,b}})
G4 = hyperGraph(R, {{b,c}, {b,a}})
G5 = hyperGraph(R, {{b,c}, {a,c}})

S = QQ[a,b,c]
G6 = hyperGraph(S, {{a,b}, {b,c}})

assert(G1 == G1) 
assert(G1 == G2)
assert(G1 == G3)
assert(G1 == G4)
assert(G1 != G5)
assert(G1 != G6)
///

-----------------------------
-- Test adjacencyMatrix
-----------------------------

TEST///
R = QQ[a..d]
c4 = graph {a*b,b*c,c*d,d*a} -- 4-cycle plus an isolated vertex!!!!
adjacencyMatrix c4
m = matrix {{0,1,0,1},{1,0,1,0},{0,1,0,1},{1,0,1,0}}
assert(adjacencyMatrix c4 == m)

///
------------------------
-- Test chromaticNumber
------------------------ 

TEST///
R = QQ[a..e]
c4 = graph {a*b,b*c,c*d,d*a} -- 4-cycle
c5 = graph {a*b,b*c,c*d,d*e,e*a} -- 5-cycle
assert(chromaticNumber c4 == 2)
assert(chromaticNumber c5 == 3)
///



-----------------------------
-- Test complementGraph
-----------------------------

TEST///
R = QQ[a,b,c,d,e]	   
c5 = graph {a*b,b*c,c*d,d*e,e*a} 
c5c = graph {a*c,a*d,b*d,b*e,c*e}
assert(complementGraph c5 === c5c)
///


-----------------------------
-- Test coverIdeal
-----------------------------

TEST///
R = QQ[a,b,c]
i = monomialIdeal {a*b,b*c}
j = monomialIdeal {b,a*c}
h = hyperGraph i
assert((coverIdeal h) == j) 
///


-----------------------------
-- Test degreeVertex Test 
-----------------------------

TEST///
R = QQ[a,b,c,d]
H = hyperGraph(monomialIdeal {a*b,b*c,c*d,c*a})
assert( degreeVertex(H,a) == 2)
assert( degreeVertex(H,0) == 2)
assert( degreeVertex(H,b) == 2)
assert( degreeVertex(H,1) == 2)
assert( degreeVertex(H,c) == 3)
assert( degreeVertex(H,2) == 3)
assert( degreeVertex(H,d) == 1)
assert( degreeVertex(H,3) == 1)
///

-----------------------------
-- Test edgeIdeal
-----------------------------


TEST///
R = QQ[a,b,c]
i = monomialIdeal {a*b,b*c}
h = hyperGraph i
assert((edgeIdeal h) == i) 
///


-----------------------------
-- Test getEdgeIndex 
-----------------------------
TEST///
R = QQ[a,b,c]
H = hyperGraph(monomialIdeal {a*b,b*c})
assert( getEdgeIndex(H,{a,b}) == 0)
assert( getEdgeIndex(H,a*b) == 0)
assert( getEdgeIndex(H,{c,b}) == 1)
assert( getEdgeIndex(H,c*b) == 1)
assert( getEdgeIndex(H,{a,c}) == -1)
assert( getEdgeIndex(H,a*c) == -1)
///



-----------------------------
-- Test hasOddHole
-- Test isPerfect
-----------------------------

TEST///
R = QQ[a..g]
G = graph {a*b,b*c,c*d,d*e,e*f,f*g,a*g} 
H = complementGraph G
assert hasOddHole G
assert not hasOddHole H
assert not isPerfect G
///

-----------------------------
-- Test hyperGraphToSimplicialComplex
----------------------------------

TEST///
R=QQ[x_1..x_6]
G=graph({x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_1*x_5,x_1*x_6,x_5*x_6}) --5-cycle and a triangle
DeltaG = hyperGraphToSimplicialComplex G
hyperGraphDeltaG = simplicialComplexToHyperGraph DeltaG
GPrime = graph(hyperGraphDeltaG)
assert(G === GPrime)
///
-----------------------------
-- Test independenceNumber
-----------------------------

TEST///
R = QQ[a..e]
c4 = graph {a*b,b*c,c*d,d*a} -- 4-cycle plus an isolated vertex!!!!
c5 = graph {a*b,b*c,c*d,d*e,e*a} -- 5-cycle
assert(independenceNumber c4 == 3)
assert(independenceNumber c5 == 2)
///


-----------------------------
-- Test isBipartite
-----------------------------

TEST///
R = QQ[a..e]
c4 = graph {a*b,b*c,c*d,d*a} -- 4-cycle
c5 = graph {a*b,b*c,c*d,d*e,e*a} -- 5-cycle
assert(isBipartite c4 == true)
assert(isBipartite c5 == false)
///




-----------------------------<
-- Test isConnected
-----------------------------
TEST///
S = QQ[a..e]
g = graph {a*b,b*c,c*d,d*e,a*e} -- the 5-cycle (connected)
h = graph {a*b,b*c,c*a,d*e} -- a 3-cycle and a disjoint edge (not connected)
assert(isConnected g) 
assert(not isConnected h)
///

-----------------------------
-- Test isEdge Test
-----------------------------
TEST///
R = QQ[a,b,c]
H = hyperGraph(monomialIdeal {a*b,b*c})
assert( isEdge(H,{a,b}) )
assert( isEdge(H,a*b) )
assert( isEdge(H,{c,b}) )
assert( isEdge(H,b*c) )
assert( not isEdge(H,{a,c}) )
assert( not isEdge(H,a*c) )
///
-----------------------------
-- Test isLeaf
-----------------------------

TEST///
R = QQ[a..e]
G = graph {a*b,b*c,c*d,d*a,a*e} 
H = hyperGraph {a*b*c,b*d,c*e} 
I = hyperGraph {a*b*c,b*c*d,c*e} 
assert(isLeaf(G,4))
assert(not isLeaf(G,1))
assert(not isLeaf(G,0))
assert(not isLeaf(G,a))
assert(isLeaf(G,e))
assert(not isLeaf(H,0))
assert(isLeaf(I,0))
///

-------------------------------------
-- Test randomGraph
-------------------------------------

-------------------------------------
-- Test randomHyperGraph
-------------------------------------

-------------------------------------
-- Test randomUniformHyperGraph
-------------------------------------

-----------------------------<
-- Test numConnectedComponents
-----------------------------
TEST///
S = QQ[a..e]
g = graph {a*b,b*c,c*d,d*e,a*e} -- the 5-cycle (connected)
h = graph {a*b,b*c,c*a,d*e} -- a 3-cycle and a disjoint edge (not connected)
assert(numConnectedComponents == 1) 
assert(numConnectedComponents == 2)
///


-------------------------------------
-- Test simplicialComplexToHyperGraph
-------------------------------------

TEST///
S = QQ[a..f]
Delta = simplicialComplex {a*b*c,b*c*d,c*d*e,d*e*f}
h = simplicialComplexToHyperGraph Delta
assert(class h === HyperGraph)
///

-----------------------------
-- Test smallestCycleSize
-----------------------------

TEST///
T = QQ[x_1..x_9]
g = graph {x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_5*x_6,x_6*x_7,x_7*x_8,x_8*x_9,x_9*x_1} -- a 9-cycle
assert(smallestCycleSize g == 9)
///

--------------------------------
-- Test spanningTree
------------------------------
TEST///
T = QQ[x_1..x_9]
h = graph {x_1*x_2,x_2*x_3,x_3*x_4,x_4*x_5,x_5*x_6,x_6*x_7,x_7*x_8,x_8*x_9} -- a tree (no cycles)
assert(spanningTree h === h)
///

-----------------------------
-- Test vertexCoverNumber
-----------------------------
TEST///
S = QQ[a..d]
g = graph {a*b,b*c,c*d,d*a} -- the four cycle
assert(vertexCoverNumber g == 2)
///

-----------------------------
-- Test vertexCovers
-----------------------------
TEST///
S = QQ[a..d]
g = graph {a*b,b*c,c*d,d*a} -- the four cycle
vertexCovers g
coverIdeal g
assert(flatten entries gens coverIdeal g == vertexCovers g)
///

-----------------------------
-- Test vertices
-----------------------------

TEST///
R = QQ[a..f]
G = graph {a*b,b*c,c*d,d*e,e*f} 
V = vertices(G)
assert(vertices(G) == {a,b,c,d,e,f})
///

end

restart
installPackage ("EdgeIdeals", UserMode=>true)
loadPackage "EdgeIdeals"
viewHelp

