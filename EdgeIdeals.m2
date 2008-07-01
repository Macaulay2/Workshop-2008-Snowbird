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
        vertices, 
        edges,   
        getEdge,
				isEdge,
				getEdgeIndex
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

vertices = method();
vertices HyperGraph := H -> H#"vertices";

edges = method();
edges HyperGraph := H -> H#"edges";

getEdge = method();
getEdge (HyperGraph, ZZ) := (H,N) -> H#"edges"#N;

isEdge = method();
isEdge (HyperGraph, List) := (H,E) -> any(H#"edges", G->G==E);

getEdgeIndex = method();
getEdgeIndex (HyperGraph, List) := (H,E) -> 
( N :=  select(0..#(H#"edges")-1, N -> H#"edges"#N == E);
  if #N == 0 then return -1; 
  return first N;
)


doc ///
	Key
		HyperGraph
	Headline 
		a class for hypergraphs.
///

doc ///
	Key
		hyperGraph
		(hyperGraph, Ring, List)
		(hyperGraph, MonomialIdeal)
		(hyperGraph, Ideal)
		(hyperGraph, List)
	Headline 
		constructor for HyperGraph.
	Usage
		H = hyperGraph(R,E) or H = hyperGraph(I) or H = hyperGraph(E)
	Inputs
		R:Ring
			whose variables correspond to vertices of the hypergraph.
		E:List
			contain a list of edges, which themselves are lists of vertices.
		I:MonomialIdeal
			which must be square-free and whose generators become the edges of the hypergraph.
		I:Ideal
			which must be square-free monomial and whose generators become the edges of the hypergraph.
	Outputs 
		H:HyperGraph
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

-----------------------------
-- Constructor Tests --------
-----------------------------

TEST///
R = QQ[a,b,c]
H = hyperGraph(R, {{a,b},{b,c}})
assert(#(edges H) == 2)
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
assert(#(edges H) == 2)
assert(#(vertices H) == 3)
///


