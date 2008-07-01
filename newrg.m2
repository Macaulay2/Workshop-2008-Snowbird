nothing = first values options newRing

mergeOptions = (x,y) -> merge(x, y, (a,b) -> if b === nothing then a else b)

newRing Ring := Ring => opts -> (R) -> (
     -- First check the type of ring of R
     -- The following is for the case when R is a polynomial ring,
     -- or a quotient of a polynomial ring

     if    (instance(opts.Variables,List) 
              and #( opts.Variables ) =!= numgens R)
        or (instance(opts.Variables,ZZ) 
              and opts.Variables =!= numgens R)
     then
         error "cannot change the number of variables using 'newRing'";

     if opts.DegreeRank =!= nothing and opts.Degrees === nothing then opts = first override(opts, Degrees => null);
     --if opts.DegreeRank =!= nothing or opts.Degrees =!= nothing then opts = first override(opts, Heft => null);
     if opts.DegreeRank === nothing and opts.Degrees =!= nothing then opts = first override(opts, DegreeRank => null);
     opts = mergeOptions((monoid R).Options,opts);
     opts = select(opts, v -> v =!= nothing); -- this applies especially to the MonomialSize option, no longer present in (monoid R).Options
     f := presentation R;
     A := ring f;
     k := coefficientRing A;
     S := k(monoid [opts]);
     f = substitute(f,vars S);
     S/image f
     )

end
restart
debug Core
load "newrg.m2"
--newRing R
--
--resets the Heft vector and won't take the Heft option seriously.

R=ZZ[x,y, Degrees => {{0,1},{0,1}}, Heft=>{0,1}]	 
S=newRing(R, Heft=>{0,1})	 
monoid S
S=newRing(R, Heft=>{1,0})	 
monoid S
S=newRing(R, Degrees=> {{0,0,1}, {0,0,1}}, Heft=>{0,0,1})	 
monoid S

-- This is allowed:
S = newRing(R, DegreeRank=>3)
degree y
describe S

S = newRing(R, Degrees=>{1,2})
degree y
describe S

-- this should (and does) give an error:
S = newRing(R, DegreeRank=>3, Degrees=>{1,2})


S = QQ[a..d, DegreeRank=>3, Degrees=>null]
describe S
