-- Copyright 1996 Michael E. Stillman

PushforwardComputation = new SelfInitializingType of BasicList
PushforwardComputation.synonym = "push-forward computation"

-- valid values are (a) {J,cleanup code}   -- J is the aux matrix and the code to derive
-- 						the answer is the 2nd element.
--               or (b) {answer}           -- answer is a matrix

--subringOptions := mergeOptions(options gb, Strategy => , UseHilbertFunction => true

protect NonLinear					    -- no longer exported

pushOptions := new OptionTable from {
	  Strategy => NonLinear,            -- use the best choice
	  UseHilbertFunction => true,  -- if possible
	  MonomialOrder => EliminationOrder,
	  StopWithMinimalGenerators => false,            -- determine the minimal generators of the subring
	  BasisElementLimit => infinity,  -- number of generators of GB in the subring
	  StopBeforeComputation => false,
	  DegreeLimit => {},
	  PairLimit => infinity
	  }

pushNonLinear := opts -> (f,M) -> (				    -- this returns the presentation matrix of the pushforward module
    comp := PushforwardComputation{M,NonLinear};
    if not f.cache#?comp then (
	-- create the computation
	S := source f;
	n1 := numgens target f;
        order := if opts.MonomialOrder === EliminationOrder then 
                     Eliminate n1
                 else if opts.MonomialOrder === ProductOrder then 
		     ProductOrder{n1, numgens S}
		 else
		     Lex;
	JJ := generators graphIdeal(f,MonomialOrder => order, VariableBaseName => local X);
	m := presentation M;
	-- now map M to the new ring.
	xvars := map(ring JJ, ring M, submatrix(vars ring JJ, toList(0..n1-1)));
	m1 := xvars m;
	m1 = presentation ((cokernel m1) ** (cokernel JJ));
	mapback := map(S, ring JJ, map(S^1, S^n1, 0) | vars S);

	if opts.UseHilbertFunction === true 
           and isHomogeneous m1 and isHomogeneous f and isHomogeneous m then (
	    hf := poincare cokernel m;
	    T := (ring hf)_0;
	    hf = hf * product(numgens source JJ, i -> (d := (degrees source JJ)#i#0; 1 - T^d));
	    (cokernel m1).cache.poincare = hf;
	    );

	cleanupcode := g -> mapback selectInSubring(1,generators g);

	f.cache#comp = {m1, cleanupcode};
	);

    if #( f.cache#comp ) === 1 then
	f.cache#comp#0
    else (
	gboptions := new OptionTable from {
			StopBeforeComputation => opts.StopBeforeComputation,
			DegreeLimit => opts.DegreeLimit,
			PairLimit => opts.PairLimit};
	m1 = f.cache#comp#0;
	g := gb(m1,gboptions);
	result := f.cache#comp#1 g;
	--if isdone g then f.cache#comp = {result};  -- MES: There is NO way to check this yet!!

	-- MES: check if the monomial order restricts to S. S If so, then do
        -- forceGB result;
	result
	)
    )

{*
pushLinear := opts -> (f,M) -> (
    -- assumptions here:
    -- (a) f is homogeneous linear, and the linear forms are independent
    -- 
    -- First bring M over to a ring with an elimination order, which eliminates
    -- the variables 'not in' f.
    m := presentation M;    
    R := target f;
    S := source f;
    Rbase := ring m;
    fmat := lift(f.matrix,Rbase);
    n := numgens source f.matrix;
    n1 := numgens R - n;
    k := coefficientRing Rbase;
    X := local X;
    N := monoid [VariableBaseName => X, Variables => numgens R, MonomialOrder => Eliminate n1];
    R1 := k N;
    (Fto,Ffrom) := newCoordinateSystem(R1, fmat);
    m1 := Fto m;
    m1 = presentation (cokernel m1 ** cokernel Fto presentation R);
    if isHomogeneous f and isHomogeneous m then (
        hf := poincare cokernel m;
        T := (ring hf)_0;
        (cokernel m1).cache.poincare = hf;
        );
    gbopts := applyPairs(gbDefaults, (k,v) -> if opts#?k and k =!= Strategy then (k,opts#k) else (k,v));
    g := selectInSubring(1, generators gb(m1,gbopts));
    -- now map the answer back to S = source f.
    mapback := map(S, R1, map(S^1, S^n1, 0) | submatrix(vars S, {0..n-1}));
    mapback g
    )
*}

kernel Matrix := Module => opts -> (cacheValue symbol kernel) ((m) -> (
	  N := source m;
	  P := target m;
	  if m.?RingMap then (
	       f := m.RingMap;
	       n := map(target m,f source m,raw m);
	       p := (pushNonLinear pushOptions)(f,image n);
	       image p)
	  else (
	       m = matrix m;
	       if P.?generators then m = P.generators * m;
	       h := modulo(m, if P.?relations then P.relations);
	       if N.?generators then h = N.generators * h;
	       subquotient( h, if N.?relations then N.relations))))
kernel RingElement := Module => options -> (m) -> kernel (matrix {{m}},options)

pushForward = method (Options => pushOptions)
pushForward(RingMap, Module) := Module => opts -> (f,M) -> (
     if isHomogeneous f and isHomogeneous M then (
	  -- given f:R-->S, and M an S-module, finite over R, find R-presentation for M
	  S := target f;
	  M = cokernel presentation M;
	  M1 := M / ideal f.matrix;
	  M2 := subquotient(matrix basis M1, relations M);
	  cokernel (pushNonLinear opts)(f,M2)
	  )
     else error "not implemented yet for inhomogeneous modules or maps"
     )

-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/m2 "
-- End:
