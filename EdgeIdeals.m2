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

export {HyperGraph, 
        hyperGraph, 
	Graph,
	graph,
	isGraph,
        vertices, 
        edges,   
        getEdge,
	isEdge,
	getEdgeIndex,
	complementGraph,
	inducedGraph,
	deleteEdges,
	stanleyReisnerComplex,
	independenceComplex,
	cliqueComplex,
	edgeIdeal,
	coverIdeal,
	isBipartite,
	isCMHyperGraph,
	isSCMHyperGraph,
	isPerfect,
	isChordal,
	isLeaf,
	hasOddHole,
	isTree,
	isConnected,
	cliqueNumber,
	chromaticNumber,
	vertexCoverNumber,
	independenceNumber,
	numTriangles,
	degreeVertex,
	numConnectedComponents,
	smallestCycleSize,
	allOddHoles,
	allEvenHoles,
	connectedComponents,
	vertexCovers,
	neighborSet,
	getCliques,
	getMaxCliques,
	adjacencyMatrix,
	incidenceMatrix,
	cycle,
	completeGraph,
	completeMultiPartite,
	antiHole,
	spanningTree,
	lineGraph
        };

needsPackage "SimpleDoc"

HyperGraph = new Type of HashTable;

hyperGraph = method(TypicalValue => HyperGraph);
hyperGraph (Ring, List) := HyperGraph => (R, E) -> 
( 
	V := gens R;
	if all(E, e-> class class e === PolynomialRing) then E = apply(E, support);
  E = apply(E, unique); --- Enforces square-free
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
( hyperGraph monomialIdeal I
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

isGraph = method();
isGraph HyperGraph := Boolean => (H) -> (
		all(H#"edges", e-> #e === 2 )
	)

Graph = new Type of HyperGraph;

graph = method(TypicalValue => Graph);
graph (Ring, List) := Graph => (R, E) -> (
		H := hyperGraph(R, E);
		if not isGraph(H) then error "Edges must be of size two.";
		new Graph from H
	)	

graph (MonomialIdeal) := Graph => (I) -> (
		H := hyperGraph(I);
		if not isGraph(H) then error "Ideal must have quadratic generators.";
		new Graph from H
	)	

graph (Ideal) := Graph => (I) -> (
		H := hyperGraph(I);
		if not isGraph(H) then error "Ideal must have quadratic generators.";
		new Graph from H
	)	

graph List := Graph => E -> (
		H := hyperGraph(E);
		if not isGraph(H) then error "Edges must be of size two.";
		new Graph from H
	)	

graph (HyperGraph) := Graph => (H) -> (
		if not isGraph(H) then error "Edges must be of size two.";
		new Graph from H
	)	

hyperGraph (Graph) := HyperGraph => (G) -> (
		new HyperGraph from G
	)	

vertices = method();
vertices HyperGraph := H -> H#"vertices";

edges = method();
edges HyperGraph := H -> H#"edges";

getEdge = method();
getEdge (HyperGraph, ZZ) := (H,N) -> H#"edges"#N;

isEdge = method();
isEdge (HyperGraph, List) := (H,E) -> (
		if class class E === PolynomialRing then E = support E;
		any(H#"edges", G->set G === set E)
	)
isEdge (HyperGraph, RingElement) := (H,E) -> (
		isEdge(H, support E)
	)

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

-- Graph Constructions

-- find the complement of G
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

-- given a set of vertices, return induced graph on those vertices
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


-- remove edges from G
deleteEdges = method();
deleteEdges (HyperGraph,List) := (H,E) -> (
     if (isSubset(set E,set H#"edges") =!= true) then error "Second argument must be a subset of the edges";
     newedges:=set(H#"edges")-set(E);
     return (hyperGraph toList newedges)
     )

deleteEdges (Graph,List) := (H,E) -> (graph deleteEdges (hyperGraph(H),E))

-- change type

 -- turn G from a graph to simplicial complex
stanleyReisnerComplex = method();

-- find independenceComplex
independenceComplex =method();
--independenceComplex HyperGraph := H -> (simplicialComplex edgeIdeal H)
--independenceComplex Graph := G -> independenceComplex (hyperGraph(G))

 -- clique complex of G
cliqueComplex =method();
--cliqueComplex Graph := G -> independenceComplex complementGraph G

-- return ideals


 -- edge ideal of G
edgeIdeal = method();
edgeIdeal HyperGraph := H -> (monomialIdeal apply(H#"edges",product)) 

 -- Alexander dual of edge ideal
coverIdeal = method();
coverIdeal HyperGraph := H -> dual edgeIdeal H


-- Boolean Functions

isBipartite = method();
isBipartite Graph := G -> (
     m := product G#"vertices";
     return m % (coverIdeal G)^2 == 0;
     );

 -- Boolean function (True of False if graph is CM)
isCMhyperGraph = method();

 -- Boolean function (True of False if graph is SCM)
isSCMhyperGraph = method();

 -- Boolean function (True or False if graph is perfect)
isPerfect = method();
isPerfect Graph := G -> (
     if hasOddHole G then return false;
     if hasOddHole complementGraph G then return false;
     return true;
     )

 -- Boolean  function (True of False if graph is chordal)
isChordal = method();

 -- (True or False if edge of hyperGraph/Graph is leaf)
isLeaf = method();
isLeaf (HyperGraph, ZZ) := (H,N) ->
( intersectEdges := (A,B) -> set H#"edges"#A * set H#"edges"#B;
	overlaps := apply(select(0..(#(H#"edges")-1), M -> M =!= N), M -> intersectEdges(M,N));
	overlapUnion := sum toList overlaps;
  any(overlaps, branch -> isSubset(overlapUnion,branch))
);
isLeaf (Graph, ZZ) := (G,N) ->
( any(G#"edges"#N, V -> degreeVertex(G,V) === 1)
  ---Note N refers to an edge index
);
isLeaf (Graph, RingElement) := (G,V) ->
( isLeaf(G,index V)
	---Note V refers to a vertex
);
isGoodLeaf = method();
isGoodLeaf (HyperGraph, ZZ) := (H,N) ->
( intersectEdges := (A,B) -> set H#"edges"#A * set H#"edges"#B;
	overlaps := apply(select(0..#(H#"edges")-1, M -> M =!= N), M -> intersectEdges(M,N));
	overlaps = sort(overlaps);
	--Check if the overlaps are totally ordered
	all(1..(#overlaps -1), I -> overlaps#(I-1) <= overlaps#I)
);
hasGoodLeaf = method();
hasGoodLeaf HyperGraph := H -> any(0..#(H#"edges")-1, N -> isGoodLeaf(H,N));

getGoodLeafIndex = method();
getGoodLeafIndex HyperGraph := H ->
(  GL := select(0..#(H#"edges")-1, N -> isGoodLeaf(H,N));
   if #GL == 0 then return -1;
   return first GL;
);

getGoodLeaf = method();
getGoodLeaf HyperGraph := H ->
( return H#"edges"#(getGoodLeafIndex H);
);


 -- (True or False if exists odd hole (not triangle) )
hasOddHole = method();
hasOddHole Graph := G -> (
     coverI:=coverIdeal G;
     any(ass coverI^2,i->codim i > 3)
     )     

 -- (True or False if graph is a tree)
isTree = method();

 -- (True or False if graph is connected)
isConnected = method();



-- Numerical Values

 -- return clique number
cliqueNumber = method();
cliqueNumber Graph := G -> (
     #(last getCliques G)
     )

 -- return chromatic number
chromaticNumber = method();
chromaticNumber HyperGraph := H -> (
     Chi := 2; 
     m := product H#"vertices";
     j := coverIdeal H;
     while ((m^(Chi-1) % j^Chi) != 0) do (
	  Chi = Chi + 1;
	  );
     return (Chi); 
     )


 -- return vertex cover number
vertexCoverNumber = method();
vertexCovers HyperGraph := H -> (
     min apply(flatten entries gens coverIdeal H,i->first degree i)
     )

 -- return independence number
independenceNumber = method();
independenceNumber Graph:= G -> (
     return (dim edgeIdeal G);
     )

 -- return number of triangles
numTriangles = method();
numTriangles Graph := G -> (
     number(ass (coverIdeal G)^2,i->codim i==3)
     )

 -- return degree of vertex
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

 -- number of connected components
numConnectedComponents = method();

 -- length of smallest induced cycle
smallestCycleSize = method();



-- Return Lists


-- return all odd holes
allOddHoles = method();
allOddHoles Graph := G -> (
     coverI:=coverIdeal G;
     select(ass coverI^2,i->codim i > 3)
     )

 -- return all even holes (this would be SLOWWW!)
allEvenHoles = method();

 -- return the connected components
connectedComponents = method();

 -- return all minimal vertex covers
vertexCovers  = method();
vertexCovers HyperGraph := H -> (
     flatten entries gens coverIdeal H
     )

 -- return neighbors of a vertex of a set
neighborSet = method();

 -- return all cliques of the graph
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

 -- return all cliques of maximal size
getMaxCliques = method();
getMaxCliques Graph := G -> (
     cliqueList:=getCliques G;
     clNum:=#(last cliqueList);
     select(cliqueList,i->#i == clNum)
     )


-- Return Matrices

 -- return the adjacency matrix
adjacencyMatrix = method();

 -- return the incidence matrix
incidenceMatrix = method();



-- special graphs (i.e. define functions to create special families)

 -- return graph of cycle on n vertices
cycle = method(TypicalValue=>Graph);
cycle (Ring) := Graph =>(R) -> cycle(generators R)
cycle (Ring, ZZ) := Graph =>(R, N) -> cycle(apply(N, i->R_i))
cycle (List) := Graph =>(L)-> (
  if #L < 3 then error "Cannot construct cycles of length less than three";
	graph(ring L#0,append(apply(#L-1, i-> L#i*L#(i+1)), (last L)*(first L)))
)

 -- return graph of complete n-graph
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
 -- return the complete multi-partite graph
completeMultiPartite = method();

 -- return graph of anti-n-hole
antiHole = method();

 -- return spanning tree of a graph G
spanningTree = method();

 -- return the graph with E(G) as its vertices where two
 --         vertices are adjacent when their associated edges are adjacent in G.
lineGraph = method();


---------------------------------------------------------
---------------------------------------------------------
---------------------------------------------------------
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

doc ///
	Key
		hyperGraph
		(hyperGraph, Ring, List)
		(hyperGraph, MonomialIdeal)
		(hyperGraph, Ideal)
		(hyperGraph, List)
		(hyperGraph, Graph)
	Headline 
		constructor for HyperGraph.
	Usage
		H = hyperGraph(R,E) \n H = hyperGraph(I) \n H = hyperGraph(E) \n H = hyperGraph(G)
	Inputs
		R:Ring
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

doc ///
	Key
		graph
		(graph, Ring, List)
		(graph, MonomialIdeal)
		(graph, Ideal)
		(graph, List)
		(graph, HyperGraph)
	Headline 
		constructor for Graph.
	Usage
		G = graph(R,E) \n G = graph(I) \n G = graph(E) \\ G = graph(H)
	Inputs
		R:Ring
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

doc ///
	Key
		vertices
		(vertices, HyperGraph)
	Headline 
		gets the vertices of a HyperGraph.
	Usage
		V = vertices(H)
	Inputs
		H:HyperGraph
		        the input
	Outputs 
		V:List
			of the vertices of {\tt H}.
///

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

doc ///
	Key
		getEdge
		(getEdge, HyperGraph, ZZ)
	Headline 
		gets the n-th edge in a HyperGraph.
	Usage
		E = edges(H,N)
	Inputs
		H:HyperGraph
		N:ZZ
			an index of an edge in {\tt H}
	Outputs 
		E:List
			which is the {\tt N}-th edge of {\tt H}.
///

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
			which is true iff {\tt E} (or {\tt support M}) is an edge of {\tt H}.
	SeeAlso
		getEdgeIndex
///

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
			the index of a vertex.
		V:RingElement
			a vertex/variable of the HyperGraph.
	Outputs 
		D:ZZ
			which is the degree of vertex {\tt V} (or vertex number {\tt N}). 
	Description
		Text
			The degree of a vertex in a hypergraph is the number of edges that contain the vertex.
	SeeAlso
		vertices
///

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
			of vertices (or monomials).
	Outputs 
		N:ZZ
			which is the index of {\tt E} as an edge of {\tt H}. If {\tt E} is not in {\tt H}
			then -1 is returned.
	SeeAlso
		isEdge
///



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
		       the chromatic number of {\tt H}.
        Description
	        Text
		 Returns the chromatic number.
///		      


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
		       returns {\tt true} if {\tt G} is bipartite, {\tt false} otherwise.
        Description
	        Text
///		      


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
			which is a complete graph on the vertices in {\tt L} or on the variables of {\tt R}.
	Description
		Example
			R = QQ[a,b,c,d,e]	   
			completeGraph R
			completeGraph(R,3)
			completeGraph {a,c,e}
///	

 
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
 
-----------------------------
-- Constructor Tests --------
------------------------- 0 to 6

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

----------------------------------
-- isEdge Test -------------------
-------------------------------- 7
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

----------------------------------
-- getEdgeIndex Test -------------
-------------------------------- 8
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

----------------------------------
-- degreeVertex Test -------------
-------------------------------- 9
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

--------------------------------------
-- Test edgeIdeal and coverIdeal 
---------------------------------- 10 to 11


TEST///
R = QQ[a,b,c]
i = monomialIdeal {a*b,b*c}
h = hyperGraph i
assert((edgeIdeal h) == i) 
///

TEST///
R = QQ[a,b,c]
i = monomialIdeal {a*b,b*c}
j = monomialIdeal {b,a*c}
h = hyperGraph i
assert((coverIdeal h) == j) 
///

----------------------------------------
-- Test Numerical Invariants
----------------------------------------

-- Chromatic Number
---------------------- 12

TEST///
R = QQ[a..e]
c4 = graph {a*b,b*c,c*d,d*a} -- 4-cycle
c5 = graph {a*b,b*c,c*d,d*e,e*a} -- 5-cycle
assert(chromaticNumber c4 == 2)
assert(chromaticNumber c5 == 3)
///

-----------------------------------------
-- Test isBipartite
------------------------------------- 13

TEST///
R = QQ[a..e]
c4 = graph {a*b,b*c,c*d,d*a} -- 4-cycle
c5 = graph {a*b,b*c,c*d,d*e,e*a} -- 5-cycle
assert(isBipartite c4 == true)
assert(isBipartite c5 == false)
///


-----------------------------------------
-- Test independenceNumber
-------------------------------------- 14

TEST///
R = QQ[a..e]
c4 = graph {a*b,b*c,c*d,d*a} -- 4-cycle plus an isolated vertex!!!!
c5 = graph {a*b,b*c,c*d,d*e,e*a} -- 5-cycle
assert(independenceNumber c4 == 3)
assert(independenceNumber c5 == 2)
///

-----------------------------------------
-- Test isLeaf
-------------------------------------- 15

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

---------------------------------------
-- Test complementGraph
--------------------------------------- 16

TEST///
R = QQ[a,b,c,d,e]	   
c5 = graph {a*b,b*c,c*d,d*e,e*a} 
c5c = graph {a*c,a*d,b*d,b*e,c*e}
assert(complementGraph c5 === c5c)
///

-----------------------------------------
-- Test isPerfect
-------------------------------------- 17

TEST///
R = QQ[a..g]
G = graph {a*b,b*c,c*d,d*e,e*f,f*g,a*g} 
H = complementGraph G
assert hasOddHole G
assert not hasOddHole H
assert not isPerfect G
///
----------------------------------------------
end


restart
installPackage ("EdgeIdeals", UserMode=>true)
loadPackage "EdgeIdeals"
viewHelp
