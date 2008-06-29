;; This buffer is for notes you don't want to save, and for Lisp evaluation.
;; If you want to create a file, visit that file with C-x C-f,
;; then enter the text in that file's own buffer.

loadPackage "SchurFunctors"
help schur
debug SchurFunctors

L={{1,0}}
normalize L
---examples
kk=QQ
M=kk^2
S4M=schurModule({2},M)
(f,finv,AT,ST)=toSequence(S4M.cache.Schur)

AT
ST
keys(AT)

new Filling {{2,0}}

---Simple examples: 
-----Symmetric powers:
kk=QQ
M=kk^3
S1M=schurModule({1},M)
S2M=schurModule({2},M)
S3M=schurModule({3},M)

R=QQ[x_1,x_2,x_3]
F=map(R^1,R^3,vars R)
L=schur({3},F)
------------------n-th veronese embedding

-----Exterior powers:
kk=QQ
M=kk^3
E0M=schurModule({},M)---
E1M=schurModule({1},M)
E2M=schurModule({1,1},M)
E3M=schurModule({1,1,1},M)
-------Koszul Complex
kk=QQ
d=4
R=kk[x_1..x_d]
Partitions=apply(d,j->apply(j+1,s->1))
Koszul=apply(d,j->schurModule(Partitions_j,R^d))

SEQ=toSequence((Koszul_2).cache.Schur)
SEQ_3
(Koszul_3).cache.Schur

---- Functoriality
kk=QQ
M1=kk^3
M2=kk^3
M=matrix{{1,2,4},{3,9,27},{4,16,64}}
F=map(M2,M1,substitute(M,kk))
det(M)

schur({1,1},F)
minors(2,M)
schur({1,1,1},F)
-----------



res coker syz L
S=kk^1

F=map(M,N,substitute(matrix{{1,1,1},{1,1,1},{1,1,1}},kk))
G=map(S,M,substitute(matrix{{1,1,-2}},kk))
G*F

--------
restart
kk=QQ
R=kk[x_1,x_2,x_3,x_4]
I=ideal(x_1,x_2,x_3,x_4)
J=I^2
res coker gens J


 
 
toSequence(F2.cache.Schur)

F1=schurModule({1,1,1},R^4) 
F2=schurModule({1,1},R^4)

new Filling from {{3,2,1}}
