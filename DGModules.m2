debug needsPackage "DGAlgebras"
needsPackage "Complexes" -- minimize issue?
needsPackage "PushForward"

DGModule = new Type of MutableHashTable
DGModuleMap = new Type of MutableHashTable

net DGModule := U -> (
   myOutput := {net "DGAlgebra => " | net U.dgAlgebra};
   myOutput = myOutput | {net "Underlying module => " | net U.natural};
   diffMat := differentialMatrix U;
   myOutput = myOutput | {net "Differential => " | net diffMat };
   horizontalJoin flatten ("{", stack myOutput, "}")
)

dgAlgebra = method()
dgAlgebra DGModule := U -> U.dgAlgebra

dgModule = method()
dgModule (DGAlgebra, Module, List) := (A,M,L) -> (
   dgModule(A,M,hashTable apply(#L, i -> (i,L#i)))
)

dgModule (DGAlgebra, Module, HashTable) := (A,M,diffHash) -> (
   if not isHomogeneous M then error "Expected a graded module over input DG algebra.";
   if not all(values diffHash, v -> instance(v,Matrix) and isFreeModule source v and rank source v == 1) then
      error "Expected a list of matrices with one column as differentials.";
   U := new DGModule from { (symbol dgAlgebra) => A,
                            (symbol natural) => M,
       	                    (symbol diff) => diffHash,
			    (symbol cache) => new CacheTable from {}};
   U
)

map (DGModule, DGModule, Matrix) := opts -> (U,V,f) -> (
   if source f =!= V.natural or target f =!= U.natural then
      error "Expected map between underlying modules.";
   dgF := new DGModuleMap from { (symbol dgAlgebra) => dgAlgebra U,
       	                         (symbol source) => V,
				 (symbol target) => U,
       	                         (symbol natural) => f };
   dgF
)
map (DGModule, DGModule, List) := opts -> (U,V,ents) -> map(U,V,map(U.natural,V.natural,ents,opts),opts)

net DGModuleMap := f -> net f.natural
source DGModuleMap := f -> f.source
target DGModuleMap := f -> f.target

moduleDiff = method()
moduleDiff (DGModule, Matrix) := (U,v) -> (
   if not isFreeModule source v or rank source v != 1 then
      error "Expected a matrix with source R^1.";
   A := U.dgAlgebra;
   entV := flatten entries v;
   termList := for i from 0 to #entV - 1 list (
      polyDiff := polyDifferential(A,entV#i);
      result = polyDiff*(U.natural)_{i} + (-1)^(first degree entV#i)*(entV#i)*(U.diff#i);
      result
   );
   result = map(U.natural,,sum termList);
   result
)

moduleDiff (DGModule, ZZ) := (U, n) -> (
   if U.cache#?"diffs" and U.cache#"diffs"#?n then return U.cache#"diffs"#n;
   
   A := (dgAlgebra U).natural;
   R := coefficientRing A;

   basisUn := basis({n},U.natural);
   basisUnm1 := basis({n-1},U.natural);
   
   degsUnm1 := apply(degrees source basisUnm1, d -> -drop(d,1));
   degsUn := apply(degrees source basisUn, d -> -drop(d,1));

   if (basisUn == 0) then return map(part({n-1},U.natural),R^0,0);
    
   myDiffs := apply(numcols basisUn, i -> moduleDiff(U,basisUn_{i})); 
   modDiffs := matrix {myDiffs};

   psi := map(R,A, DegreeMap => degA -> take(degA, - degreeLength R));
   -- diffMat := psi last coefficients(modDiffs, Monomials => basisUnm1);
   diffMat := modDiffs // basisUnm1;
   if (basisUnm1 * diffMat != modDiffs) then error "Error in computing differential of DGModule.";
   diffMat = psi diffMat;   
   
   Unm1 := part({n-1},U.natural);
   Un := part({n},U.natural);

   result := map(Unm1, Un, diffMat);
   if not isHomogeneous result then error "Not homogeneous.";

   if not U.cache#?"diffs" then U.cache#"diffs" = new CacheTable from {};
   U.cache#"diffs"#n = result;
   
   result 
)

-- builds a matrix that represents the differentials
-- of the generators of U over A
differentialMatrix = method()
differentialMatrix DGModule := U -> matrix {apply(sort keys U.diff, k -> U.diff#k)}

moduleAsDGModule = method()
moduleAsDGModule (DGAlgebra, Module) := (A,M) -> (
   if (ring M =!= A.ring) then error "Expected a module over the base ring of the DGAlgebra.";
   presM := presentation M;
   varsA := id_(target presM) ** (vars A.natural);
   presOverA := varsA | sub(presM, A.natural);
   MoverA := coker presOverA;
   zeroMoverA := map(MoverA,(A.natural)^1,0);
   dgModule(A,MoverA,toList((numrows presOverA):zeroMoverA))
)

max DGModule := U -> (
   num := value numerator reduceHilbert hilbertSeries U.natural;
   den := value denominator reduceHilbert hilbertSeries U.natural;
   degRing := ring num;
   if den != 1 and member(degRing_0,support den) then return infinity;
   maxDeg := (exponents num) / first // max;
   maxDeg
)

min DGModule := U -> (
   -- this method assumes that the DGAlgebra is nonnegatively graded
   min (degrees source gens U.natural / first)
)

betti DGModule := opts -> U -> (
   if not isFreeModule U.natural then error "Expected a semifree DG module.";
   A := dgAlgebra U;
   R := ring A;
   if degreeLength R > 1 then error "Expected at most singly graded base ring.";
   v := getSymbol "v";
   mono := monoid [v_1..v_(degreeLength A.natural)];
   S := frac(QQ mono);
   phi := map(S,degreesRing A.natural,gens S);
   psi := map(S,degreesRing R, {S_1});
   hsUNum := numerator reduceHilbert hilbertSeries U.natural;
   hsUDen := denominator reduceHilbert hilbertSeries U.natural;
   hsRNum := numerator reduceHilbert hilbertSeries R;
   hsRDen := denominator reduceHilbert hilbertSeries R;
   hsU := numerator((phi(value hsUNum)*psi(value hsRDen)) / (phi(value hsUDen)*psi(value hsRNum)));
   coeffExp := apply(terms hsU, t -> (leadCoefficient t, first exponents t));
   bettiInput := if degreeLength A.natural == 2
                 then apply(coeffExp, p -> (p#1#0,{p#1#1},p#1#1) => p#0)
                 else apply(coeffExp, p -> (p#1#0,{0},0) => p#0);
   t := new BettiTally from bettiInput;
   t
)

-- this method assumes that A is nonnegatively graded
complex (DGModule,Nothing,Nothing) := 
complex (DGModule,Nothing,ZZ) :=
complex (DGModule,ZZ,Nothing) := 
complex (DGModule,ZZ,ZZ) := opts -> (U,minDeg,maxDeg) -> (
   startDeg := if minDeg === null then min U else minDeg;
   endDeg := if maxDeg === null then max U else maxDeg;
   if (endDeg < startDeg) then error "Expected an integer >= lowest degree.";
   if (startDeg == endDeg) then return complex(part({startDeg},U.natural),Base => startDeg);
   complex(apply(toList((startDeg+1)..endDeg), i -> moduleDiff(U,i)), Base => startDeg)
)

complex DGModule := opts -> U -> (
   maxDeg := max U;
   if maxDeg < infinity then return complex(U,,maxDeg,opts);
   -- if here, there is not a maximum degree
   error "Maximal degree is infinite, so must provide an integer.";
)

-- for now, assume that f is degree 0
complexMap = method()
complexMap DGModuleMap := f -> (
   U := source f;
   V := target f;
   maxDegU := max U;
   maxDegV := max V;
   minDegU := min U;
   minDegV := min V;
   if maxDegU == infinity and maxDegV == infinity then
      error "Must provide an integer since both source and target are infinite modules over the base.";
   if maxDegU < infinity and maxDegV == infinity then return complexMap(f,minDegU,maxDegU);
   if maxDegU == infinity and maxDegV < infinity then return complexMap(f,minDegV,maxDegV);
   return complexMap(f,min(minDegU,minDegV), max(maxDegU,maxDegV));
)

complexMap (DGModuleMap, ZZ, ZZ) := (f, minf, maxf) -> (
   -- create hashTable for parts of f between minf and maxf
   -- each element should be the map from (source f)_i -> (target f)_(i + d)
   -- where d = homological degree of f
   homDegf := first degree f.natural;
   U := source f;
   V := target f;
   Ucx := complex(U,minf,maxf);
   Vcx := complex(V,minf,maxf);
   fHash := hashTable apply(toList(minf..maxf), i -> (i,map(part({i},f.natural))));
   map(Vcx,Ucx,fHash)
)

DGModule Array := (U,ar) -> (
   -- new action is a.u = (-1)^|a|(au).  So how do
   -- we incorporate the sign?
   A := dgAlgebra U;
   R := ring A;
   zeroDegR := if isHomogeneous R then degree (1_R) else {};
   if #ar != 1 then error "Expected an array of length one.";
   shift := ar#0;
   if instance(shift,ZZ) then return U[{-shift} | zeroDegR];
   shift = first (ar#0);
   dgModule(dgAlgebra U,
            (U.natural) ** (A.natural)^(-{ar#0}),
            applyValues(U.diff,v -> (-1)^shift*v))
)

killCycles (DGModule, List) := opts -> (U,myCycles) -> (
   A := dgAlgebra U;
   R := ring A;
   zeroDegInR := degree 1_R;
   degCycles := apply(myCycles, z -> -(first degrees source z + degree z + ({1} | zeroDegInR)));
   -- create the new extension
   if U.natural.cache.?components then (
      newUnat := directSum( U.natural.cache.components | {(A.natural)^degCycles});
      injIndices := new Array from drop(indices newUnat,-1);
   )
   else (       
      newUnat = (U.natural) ++ (A.natural)^degCycles;
      injIndices = [0];
   );
   inj = newUnat_injIndices;
  
   newU := dgModule(A,newUnat,merge(applyValues(U.diff, v -> inj * v),
                              hashTable apply(#myCycles, i -> (i+numgens U.natural,inj * myCycles#i)),
        	              identity));
   newU
)

killCyclesInDegree = method()
killCyclesInDegree (DGModule,ZZ) := (U,d) -> (
   -- input: A DG module U and an integer d
   -- output: Adjoins variables in degree d+1 to kill all the cycles in
   --         homological degree d.
   A := dgAlgebra U;
   R := ring A;
   zeroDegInR := degree 1_R;
   Ucx := complex(U,d-1,d+1);
   -- compute homology in homDeg spot
   pruneHH := prune HH_d Ucx;
   if pruneHH == 0 then return U;  -- do nothing if homology is already zero in that degree
   hhUcx := image pruneHH.cache.pruningMap;
   -- get a generating set of the cycles
   myCycles = apply(numgens hhUcx, i -> basis({d},U.natural) * liftGenerator(hhUcx,i));
   killCycles(U,myCycles)
)

killCyclesInDegree (DGModuleMap, ZZ) := (eps,d) -> (
   F := source eps;
   U := target eps;
   A := dgAlgebra F;
   R := ring A;
   zeroDegInR := degree 1_R;
   epsCxMap := complexMap eps;  -- make this a range...
   coneEps := cone epsCxMap;
   hhConeEps := prune HH_d coneEps;
   hhGens := map(coneEps_d,,gens image hhConeEps.cache.pruningMap);
   hhGensUpstairs := -basis({d-1},F.natural) * hhGens^[0];
   newF := killCycles(F,apply(numcols hhGensUpstairs, i -> hhGensUpstairs_{i}));
   newDegs := apply(degrees source hhGens, deg -> -({0} | deg) + ({d+1} | zeroDegInR));
   newDownstairsMap := (basis({d},U.natural) * hhGens^[1]);
   newEps := map(U,newF,map(Unat,newF.natural,eps.natural | newDownstairsMap));
   newEps
)

semiFreeResolution = method()
semiFreeResolution (DGAlgebra,Module,ZZ) := (A,M,d) -> (
   -- input: a DG R-algebra A, an R-module M, and an integer d
   -- output: a semifree resolution U of M over A such that the
   --         rank of the R-module underlying U is correct out to
   --         homological degree d
   if d < 0 then error "Expected a nonnegative integer.";
   R := ring A;
   zeroDegInR := degree 1_R;
   presM := presentation M;
   tarMDeg := apply(degrees target presM, deg -> -({0} | deg));
   srcMDeg := apply(degrees source presM, deg -> -({1} | deg));
   homDeg := 0;
   -- if input is a free module or d = 0, then just return the semifree module
   -- with trivial module differential
   if isFreeModule M or d == homDeg then return A^tarMDeg;
      
   -- the first step is a little different than all the others,
   -- since we just add in basis elements corresponding to generators and
   -- relations of M
   Fnat := (A.natural)^tarMDeg ++ (A.natural)^srcMDeg;
   relsMatrix := basis({0},Fnat)*presM;
   newCycles := apply(numcols presM, i -> relsMatrix_{i});
   zeroUnat := map(Fnat,(A.natural)^1,0);
   F := dgModule(A,Fnat,toList(numrows presM : zeroUnat) | newCycles);
   DGM := moduleAsDGModule(A,M);
   homDeg = homDeg + 1;

   -- at this point, we want to loop until homDeg == d
   while (homDeg != d) do (
      F = killCyclesInDegree(F,homDeg);
      homDeg = homDeg + 1;
   );
   eps := map(DGM,F,map(DGM.natural,F.natural,(F.natural)^[0]));
   F.cache#"augmentation" = eps;
   
   F
)

semiFreeResolution (DGModule,ZZ) := (U,d) -> (
   Ucx := complex(U,min U,d+1);
   minU := minHomology Ucx;
   -- do nothing if max homological degree is less than
   -- location of earliest homology
   if d < minU then return map(U,K^0,map(U.natural,(K.natural)^0,0));

   -- this code is to build the first surjection onto the
   -- generators of the lowest degree homology
   curDeg := minU;
   hhMinU := prune HH_curDeg Ucx;
   hhMinGens := map(Ucx_curDeg,,gens image hhMinU.cache.pruningMap);
   hhMinDegs := apply(degrees source hhMinGens, d -> -({curDeg} | d));
   Fnat := (K.natural)^hhMinDegs;
   gensMap := hhMinGens ** (K.natural);
   F := dgModule(K,Fnat,apply(numcols gensMap, i -> gensMap_{i}));
   downstairsMap = map(Unat,Fnat,Unat_{0});
   eps := map(U,F,downstairsMap);
   curDeg = curDeg + 1;
   
   while (curDeg <= d) do (
      eps = killCyclesInDegree(eps,curDeg);
      curDeg = curDeg + 1;
   ); 
   F = source eps;
   F.cache#"augmentation" = eps;
   F
)

minHomology = method()
minHomology Complex := C -> (
   first select(1,toList(min C, max C), i -> prune HH_i C != 0)
)

---- DGAlgebra QoL
DGAlgebra ^ ZZ := (A,n) -> (
    M := (A.natural)^n;
    zeroM := map(M,(A.natural)^1,0);
    dgModule(A,M,toList(n:zeroM))
)
DGAlgebra ^ List := (A,l) -> (
    M := (A.natural)^l;
    zeroM := map(M,(A.natural)^1,0);
    dgModule(A,M,toList((#l):zeroM))
)

ring DGAlgebra := A -> A.ring
koszulComplexDGA RingElement := opts -> f -> koszulComplexDGA {f}
ZZ _ DGAlgebra := 
QQ _ DGAlgebra :=
RingElement _ DGAlgebra := (f,A) -> f_(A.natural)

liftGenerator = method()
liftGenerator (Module, ZZ) := (H, n) -> (
   -- H is a subquotient, and we are lifting the nth generator
   -- to the generating submodule
   f := H_{n};
   g := map(H,(image generators H), 1);
   h := f // g;
   --myLift := basis({1},F1.natural) * (gens image h1)
   gens image h
)

part (List,Module) := (deg,M) -> (
   -- input: a graded module M and a degree of length
   --        equal to the degrees added from R to A
   -- output: The component of M in degree deg as an R-module
   --         where A = ring M and R = coefficientRing A
   if not isHomogeneous M then error "Expected a homogeneous module.";
   A := ring M;
   R := coefficientRing A;
   bas := basis(deg,M,SourceRing=>R);
   transBas := transpose entries bas;
   kerBas := ker bas;
   tarDegs := degrees target bas;
   colPos := apply(transBas, c -> position(c, e -> e != 0));
   srcDegs := apply(#transBas, i -> (degree transBas#i#(colPos#i)) + tarDegs#(colPos#i));
   srcDegs = apply(srcDegs, d -> -drop(d,#deg));
   sourceMod := R^srcDegs;
   gensKerMap := map(sourceMod,,gens ker bas);
   modComp := prune coker gensKerMap;
   modComp
)

part (List,Matrix) := (deg,f) -> (
   -- input: a map of graded modules f and a degree of length
   --        equal to the degrees added from R to A
   -- output: The component of f as a map of R-modules
   if not isHomogeneous f then error "Expected a homogeneous map.";
   A := ring f;
   R := coefficientRing A;
   psi := map(R,A, DegreeMap => degA -> take(degA, - degreeLength R));
   newf := psi matrix basis(deg, f);
   sourcePart := part(deg,target f);
   targetPart := part(deg,source f);
   result := map(sourcePart,targetPart,newf);
   result
)

end

restart
load "./DGModules.m2"
S = QQ[x,y,z]
I = ideal (x^3,y^3)
R = S/I
K = koszulComplexDGA R
complex(K^{{0,0},{1,0}},Base=>-1)
complex(K^{{0,0},{1,0}})
Unat = K^{{0,0},{-1,-1}}
U = dgModule(K,Unat,{0_Unat,0_Unat})
Ucx = complex U
randomComplexMap(Ucx,Ucx[-1],Degree=>-1,Cycle=>true)
complex(U,,4)
complex U
complex(U,2,4)
dds = apply(6, i -> moduleDiff(U,i))
Ucx = complex(dds,Base => -1)
isHomogeneous Ucx
prune HH Ucx
max U

Unat = (K.natural)^{{0,0},{-1,0}}
U = dgModule(K,Unat,{0_Unat,Unat_0})
dds = apply(6, i -> moduleDiff(U,i))
Ucx = complex(dds,Base => -1)
isHomogeneous Ucx
prune HH Ucx

-- what do we need to check in isWellDefined DGModule:
-- homological degree -1 map
-- square zero
-- lift differential to ambient M, make sure V goes to V

-- another attempt and understanding graded module components
restart
load "DGModules.m2"
S = QQ[x,y]
R = S[z]
M1 = coker matrix {{y^2,z^2,x*z}}
part({1},M1)
M2 = coker matrix {{z^2}}
part({1},M2)
part({1},id_M2)
part({1},id_M1)

-- semifree resolution examples
restart
load "DGModules.m2"
R = QQ[x]/ideal(x^3)
K = koszulComplexDGA x^2
psi = map(K.natural,R)
M = (coker matrix {{x}})
F = semiFreeResolution(K,M,3)
diffMat = differentialMatrix F
F = semiFreeResolution(K,M,7)
Fcx = complex F
Fcx.dd
isHomogeneous Fcx
prune HH Ucx

restart
load "DGModules.m2"
R = QQ[x]/ideal(x^3)
K = koszulComplexDGA {x,x^2}
M = coker matrix {{x}}
U = semiFreeResolution(K,M,15);
U
Ucx = complex U
prune HH Ucx

restart
load "DGModules.m2"
R = QQ[x,y,z]/ideal(x^3,y^3)
K = koszulComplexDGA(z^3)
M = coker vars R
U = semiFreeResolution(K,M,3);
diffMat = differentialMatrix U
degrees source diffMat

restart
load "DGModules.m2"
R = QQ[x,y]
K = koszulComplexDGA {x^2,x*y}
M = coker vars R
U = semiFreeResolution(K,M,4);
diffMat = differentialMatrix U
Ucx = complex U

restart
load "DGModules.m2"
R = QQ[x,y]/ideal(x^2,x*y)
K = koszulComplexDGA {x,y^2}
M = coker vars R
U = semiFreeResolution(K,M,6);
Ucx = complex U
isHomogeneous Ucx
isWellDefined Ucx

-- part of a complex bug?
restart
needsPackage "Complexes"
S = QQ[a]
R = S[x]
K = koszulComplex {1_R,1_R,1_R}
C = K ** (coker matrix {{a,x}})
part({0},C) -- not right

restart
load "./DGModules.m2"
S = QQ[x,y,z]
I = ideal (x^3,y^3)
R = S/I
K = koszulComplexDGA R
kMod = coker vars K.ring
kDGMod = moduleAsDGModule (K,kMod)
Hom(kDGMod.natural,kDGMod.natural)
complex kDGMod
complex (kDGMod[-1])
complex (kDGMod[1])

-- todo: turn a finite complex over the ambient ring of a CI R whose homologies
--         are R-modules into a DG module over the koszul complex of the
--         relations of R (makeHomotopies in CompleteIntersectionResolutions)
--       isWellDefined of DGModule and DGModuleMap

--       Hom of DG modules
--          homomorphism and homomorphism'
--       Tensor product of DG modules
--       cone of a ComplexMap as a DG Module

--       ComplexMap corresponding to mult by an element
--       lifting along surjective quisms
--       Theorem 3.1.1 in Lucho's Notes
--       ComplexMap of a DGModuleMap
--       semifree resolution in internal degree order

--       speed up creation of differentials using tensor products
--       given a DGAlgebraMap A --> B, view B as a DG module over A.

-- strange behavior
R = QQ[x]
degree (0_R)
N = image matrix {{x}}
f = N_0
g = 0_N
degree f
degree g
isHomogeneous f
isHomogeneous g
isHomogeneous (f + g)
f + g == f

-- works
R = QQ[x]
N = image matrix {{x}}
f = N_{0}
f * (gens N)
g = matrix 0_N
degree f
degree g
isHomogeneous f
isHomogeneous g
isHomogeneous (f + g)
f + g == f

restart
R = QQ[x]
m = map(R^{-1},R^{-1},matrix {{x}},Degree => {1})
isHomogeneous (m_{0})

isHomogeneous m
m_0
m0mat = m_0#0
isHomogeneous target m0mat
isHomogeneous source m0mat
rawIsHomogenous m0mat.RawMatrix
source m0mat

m = map(R^{0},R^{-1},matrix {{x}})
isHomogeneous m
m_0
isHomogeneous (m_0)

M = target m
h = m_{0}
h = map(M, R^{degree m}, h, Degree => first degrees source h)
isHomogeneous h

restart
load "DGModules.m2"
R = QQ[x,y,z]/ideal(x^3,y^3)
K = koszulComplexDGA(z^3)
M = coker vars R
U = semiFreeResolution(K,M,8);
elapsedTime betti U
elapsedTime Ucx = complex U;
betti Ucx
degrees source Ucx.dd_1

restart
load "DGModules.m2"
R = QQ[x]/ideal(x^3)
K = koszulComplexDGA x^2
psi = map(K.natural,R)
M = (coker matrix {{x}})
F = semiFreeResolution(K,M,2)
Fcx = complex F

z \in A
\eta : U[-d] --> U
u |--> zu
eta(u) = zu
del(eta(u)) = del(zu) = \del(z)u + (-1)^d*z\del(u)
eta(del(u)) = (-1)^d*z\del(u)
so if z is a cycle, this is a chain map
and it is A-linear

-- in order for semifree res to work(?), the module must be a module
-- over R/I where I = image of 1st differential of A
restart
load "DGModules.m2"
S = ZZ/101[a,b,c,d]
I = ideal {5*a*c + b*c, a*d + b*d,c*d, a^2,b^2,c^2,d^2}
K = koszulComplexDGA I
R = S/I
-- the Gasharov-Peeva module as a module over S
M = pushForward(map(R,S),coker matrix {{a,c+d},{0,b}})
res M
res (prune (M ** R))
isHomogeneous M
dgM = moduleAsDGModule(K,M)
complex dgM
U = semiFreeResolution(K,M,2);
diffMat = differentialMatrix U
prune HH complex(U,0,3)

-- how to define differentials using tensor products rather than
-- computing differentials of individual objects
restart
load "DGModules.m2"
R = QQ[x,y]/ideal(x^2,x*y)
K = koszulComplexDGA {x,y^2}
M = coker vars R
U = semiFreeResolution(K,M,3);
Ucx = complex(U,0,3)
Kcx = toComplex K
Unatdegs = degrees U.natural
UdiffIndices = (sort pairs partition(p -> first last p,apply(numgens U.natural, i -> (i,Unatdegs#i)))) / last / (l -> apply(l,first))
tempUdiffs = apply(toList(1..#UdiffIndices-1), i -> (U.natural)^(splice [(0..(i-1))]) * matrix {apply(UdiffIndices#i, j -> U.diff#j)})

--        K2X0  K1X1   K0X2
-- K1X0 ( A11  -A12    A23  )
-- K0X1 ( 0     A22    A23  )
-- U_2 = K_2X_0 ++ K_1X_1 ++ K_0X_2
-- U_1 = K_1X_0 ++ K_0X_1
-- K_2X_0 -> K_1X_0 -- alg diff
diff20a = part({0},part({1},(U.natural^[0,1]*U.natural_[0]))*(polyDifferential(2,K) ** U.natural.cache.components#0))
A11 = polyDifferential(2,K) ** part({0},U.natural.cache.components#0)
temp = A11
A12 = Kcx_1**part({0},map(target tempUdiffs#0,,tempUdiffs#0))
A22 = polyDifferential(1,K) ** part({1},U.natural.cache.components#1)
temp = matrix {{temp,-A12},{0,A22}}
A23 = part({1},map(target tempUdiffs#1,,tempUdiffs#1))
temp = temp | A23
Ucx.dd_2

--             0    2      8       4
--           K3X0  K2X1   K1X2    K0X3
-- 1  K2X0 ( A11   A12    -A23    A34    )
-- 4  K1X1 ( 0     A22    -A23    A34    )
-- 4  K0X2 ( 0      0     A33     A34    )
A11 = polyDifferential(3,K) ** part({0},U.natural.cache.components#0)
temp = A11
A12 = Kcx_2**part({0},map(target tempUdiffs#0,,tempUdiffs#0))
A22 = polyDifferential(2,K) ** part({1},U.natural.cache.components#1)
temp = matrix {{temp,A12},{0,A22}}
A23 = part({2},map(target tempUdiffs#1,,tempUdiffs#1))
A33 = polyDifferential(1,K) ** part({2},U.natural.cache.components#2)
temp = matrix {{temp,-A23},{map(target A33,source temp,0),A33}}
A34 = part({2},map(target tempUdiffs#2,,tempUdiffs#2))
temp | A34
Ucx.dd_3

restart
load "DGModules.m2"
R = QQ[x,y]
K = koszulComplexDGA {x^4,y^4}
k = coker vars R
F = semiFreeResolution(K,k,4)
(complex F).dd^2
prune HH complex F
diffMat = differentialMatrix F
S = QQ[x,y]/ideal(x^4,y^4)
phi = map(S,K.natural)
diffMatS = phi diffMat
diffMatS^2
kResOverS = res(coker vars S, LengthLimit => 4)
kResOverS.dd

restart
load "DGModules.m2"
S = QQ[x,y]
K = koszulComplexDGA {x^4,y^4}
k = coker vars S
F = semiFreeResolution(K,k,4)
diffMat = differentialMatrix F
R = QQ[x,y]/ideal(x^4,y^4)
phi = map(R,K.natural)
diffMatR = phi diffMat
diffMatR^2
psi = map(S,K.natural)
diffMatS = psi diffMat
diffMatS^2

kResOverS = res(coker vars S, LengthLimit => 4)
kResOverS.dd

-- codim 2 mf example
restart
load "DGModules.m2"
S = QQ[x,y,a,b]
I = ideal {x*a,y*b}
K = koszulComplexDGA I
M = coker matrix {{x,y}}
R = S/I
MR = M ** R
resMOverR = res (MR,LengthLimit => 4)
N = ker resMOverR.dd_2
NR = prune pushForward(map(R,S),N)
F = semiFreeResolution(K,NR,3)
diffMat = differentialMatrix F
diffMatR = sub(diffMat,R)
Fnatdegs = degrees F.natural
FdiffIndices = (sort pairs partition(p -> first last p,apply(numgens F.natural, i -> (i,Fnatdegs#i)))) / last / (l -> apply(l,first))
temp1 = diffMatR_(FdiffIndices#1)^(FdiffIndices#0)
temp1_{2,3,0,4,1,5,6}^{3,1,0,2}
temp2 = diffMatR_(FdiffIndices#2)^(FdiffIndices#1)
temp2_{5,1,0,2,4,3}^{2,1,0,3,4}
diffMatR_(FdiffIndices#3)^(FdiffIndices#2)

restart
load "DGModules.m2"
S = QQ[x,y,a,b]
I1 = ideal {x*a,y*a}
I2 = ideal {x*a,y*b}
--phi = map(S,S,{random(1,S),random(1,S),random(1,S),random(1,S)})
--I2 = phi I1
K1 = koszulComplexDGA I1
K2 = koszulComplexDGA I2
M = coker matrix {{x,y}}
R1 = S/I1
R2 = S/I2
MR1 = M ** R1
MR2 = M ** R2
resMOverR1 = res (MR1,LengthLimit => 4)
resMOverR2 = res (MR2,LengthLimit => 4)
N1 = prune pushForward(map(R1,S),MR1)
N2 = prune pushForward(map(R2,S),MR2)
F1 = semiFreeResolution(K1,N1,3)
F2 = semiFreeResolution(K2,N2,3)
diffMat1 = differentialMatrix F1
diffMat2 = differentialMatrix F2
(net diffMat1) | (net diffMat2)

-- Blurb

The DGAlgebras group worked on creating additional functionality to
the DGAlgebras package.  We first worked on adding support for DG
modules.  As a result of our work, one may construct a DG module $U$
over a given DG $R$-algebra $A$, convert it to a complex over $R$,
which is graded if $R$ and $U$ carry an additional internal grading.
One may also compute a semifree resolution of an $R$-module $M$ over
$A$, provided $M$ is a module over $H_0(A)$ (i.e. the annihilator of
$M$ contains the degree zero boundaries of $A$).  Other features
include shifts of DG modules, DG module maps, and computing the Betti
diagram of a semifree DG module.  After adding this functionality, we
investigated the parallel between resolutions over complete
intersections and semifree resolutions over the Koszul complex given
by the defining equations.


restart
load "DGModules.m2"
S = QQ[x,y,a,b]
I1 = ideal {x*a,y*x}
I2 = ideal {x*a,y*b}
--phi = map(S,S,{random(1,S),random(1,S),random(1,S),random(1,S)})
--I2 = phi I1
K1 = koszulComplexDGA I1
K2 = koszulComplexDGA I2
M = coker matrix {{x*a,y*b,x*y}}
R1 = S/I1
R2 = S/I2
MR1 = prune (M ** R1)
MR2 = prune (M ** R2)
resMOverR1 = res (MR1,LengthLimit => 4)
resMOverR2 = res (MR2,LengthLimit => 4)
N1 = prune pushForward(map(R1,S),MR1)
N2 = prune pushForward(map(R2,S),MR2)
F1 = semiFreeResolution(K1,N1,3)
F2 = semiFreeResolution(K2,N2,3)
diffMat1 = differentialMatrix F1
diffMat2 = differentialMatrix F2
(net diffMat1) | (net diffMat2)

restart
load "DGModules.m2"
R = QQ[x,y]/ideal(x^5,y^5)
K = koszulComplexDGA({x^4,x^3*y},Variable => "S")
K2 = koszulComplexDGA({x,y},Variable => "T")
phi = dgAlgebraMap(K2,K,matrix{{x^3*T_1,x^3*T_2}})
isWellDefined phi
-- would like to just do:
--pushForward(phi,K2^1)
-- but it needs pushForward(phi.natural,(K2.natural)^1) to work
pushForward(phi.natural,(K2.natural)^1)  -- fails
gensSet = basis K2.natural
UnatAmb = (K.natural)^(apply(degrees source gensSet, d -> -d))
gensSetList = flatten entries gensSet
e1Map = sub(last coefficients (x^3*T_1*gensSet, Monomials => gensSet),R)
e2Map = sub(last coefficients (x^3*T_2*gensSet, Monomials => gensSet),R)
s1Map = map(UnatAmb,,matrix {apply(numcols e1Map, c -> (S_1*id_(UnatAmb))_{c} - e1Map_{c})})
s2Map = map(UnatAmb,,matrix {apply(numcols e2Map, c -> (S_2*id_(UnatAmb))_{c} - e2Map_{c})})
Unat = coker (s1Map | s2Map)
U = dgModule(K,Unat,{map(Unat,K.natural^1,0),x*Unat_{0},x*Unat_{3} - y*Unat_{1},y*Unat_{0}})
F = semiFreeResolution(U,5)
eps = F.cache#"augmentation"
isHomogeneous complex F
isHomogeneous cone complexMap eps
prune HH cone complexMap eps

-- DEMO
restart
load "DGModules.m2"
R = QQ[x,y]
K = koszulComplexDGA {x^2,x*y}
M = coker vars R
U = semiFreeResolution(K,M,4)
eps = U.cache#"augmentation"
prune HH cone complexMap eps
diffMat = differentialMatrix U
Ucx = complex U
U.natural.cache.components
degrees U.natural

restart
load "DGModules.m2"
R = QQ[x,y,z]/ideal(x^3,y^3)
K = koszulComplexDGA(z^3)
M = coker vars R
U = semiFreeResolution(K,M,4);
diffMat = differentialMatrix U
Ucx = complex U
betti U
betti Ucx
U[-1]
Ucx' = complex U[-1]
myMap = map(U,U,map(U.natural,U.natural,x))
complexMap myMap

-- parts
restart
load "DGModules.m2"
S = QQ[x,y]
R = S[z]
M1 = coker matrix {{y^2,z^2,x*z}}
part({1},M1)
-- basis({1},M1,SourceRing=>S)
M2 = coker matrix {{z^2}}
part({1},M2)
part({1},id_M2)
part({1},id_M1)

-- module as a DG module
restart
load "DGModules.m2"
R = QQ[x,y,z]/ideal(x^3,y^3)
K = koszulComplexDGA(z^3)
M = coker vars R
U = moduleAsDGModule(K,M)
complex U

-- suppose A is a graded commutative DG algebra
-- phi : A -> A defined by phi(a) = (-1)^|a|a for homogeneous a.
-- Is phi a DGAlgebra homomorphism?
-- alg hom... yes
-- phi(ab) = (-1)^{|a||b|}ab = (-1)^|a|a(-1)^|b|b = phi(a)phi(b)
-- comm with diff... no
-- phi(del(a)) = (-1)^{|a|-1}del(a)
-- del(phi(a)) = del((-1)^|a|a) = (-1)^|a|del(a)

-- suppose U has presentation given by a matrix P over a DGA
-- let phi be as above.  Then phi(P) is a presentation for the shift of U.

