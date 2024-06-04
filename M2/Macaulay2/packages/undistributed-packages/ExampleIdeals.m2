-- -*- coding: utf-8 -*-
newPackage(
	"ExampleIdeals",
	AuxiliaryFiles => true,
    	Version => "0.1", 
    	Date => "February 8, 2007",
    	Authors => {{Name => "Mike Stillman", 
		  Email => "mike@math.cornell.edu", 
		  HomePage => "http://www.math.cornell.edu/~mike/"}},
    	Headline => "examples of ideals",
     	PackageImports => { 
            "GraphicalModels" 
            },
    	DebuggingMode => false
    	)

export {
     "readExampleFile",
     "getExampleFile",
     "ExampleTable",
     "box",
     "example",
     "findExamples",

     "toSingular",
     "singularGB",
     "singularGBString",
     "singularIntegralClosure",
     "runSingularGB",     

     "toMagma",
     "magmaGBString",
     "runMagmaGB",
     "runMagmaIntegralClosure",
     
     "examplesStdSingular",
     "examplesDGP",
     "examplesSIN",
     "examplesBayes",
     "egPermanents",
     "egHaas",
     "katsura",
     "cyclicRoots",
     "cyclicRootsHomogeneous",
     "commuting4by4",
     "commuting4by4grevlex",
     "mayr",
     "PellikaanJaworski",
     "bayes"
     }

needs "./ExampleIdeals/mayr-meyer.m2"

ExampleTable = new Type of HashTable

box = method()
example = method(Options=>{CoefficientRing => ZZ/32003,
	                   Ring => null})

findExamples  = method()
findExamples(ExampleTable, String) := (E,regex) -> (
     K := keys E;
     select(K, k -> match(regex, K#k#0))
     )

show(ExampleTable, ZZ) := (H,x) -> print ("-------------------" || ("-- "|H#x#0) || H#x#1)
show(ExampleTable, List) := (H,x) -> scan(x, x1 -> show(H,x1))
show(ExampleTable, String) := (H,re) -> show(H,findExamples(H,re))
show(ExampleTable) := (H) -> show(H, sort keys H)

box(ExampleTable, ZZ) := (H,x) -> box(H,{x})
box(ExampleTable, List) := (H,x) -> netList apply(x, x1 -> {x1, ("-- "|H#x1#0) || H#x1#1})
box(ExampleTable, String) := (H,re) -> box(H,findExamples(H,re))
box(ExampleTable) := (H) -> box(H, sort keys H)

example(ExampleTable, ZZ) :=
example(ExampleTable, String) := opts -> (H,x) -> (
     R1 := if opts#?Ring then opts#Ring else null;
     kk := if R1 === null 
             then opts.CoefficientRing 
	     else coefficientRing R1; 
     I := value replace("kk", toString kk, H#x#1);
     if R1 =!= null then (
     	  nvars := numgens ring I;
	  if numgens R1 < nvars then 
	    error ("expected ring with at least "|nvars|" variables");
	  substitute(I, (vars R1)_{0..nvars-1})
	  )
     else I)

readExampleFile = method()
-* -- remove this code
readExampleFile(String,Ring) := (filename, coeffring) -> (
     G := separateRegexp("---+", get (ExampleIdeals#"source directory"|filename));
     G = apply(G, s -> select(lines s, t -> #t > 0));
     -- now for each example, find its name/number and make the string
     G = select(G, s -> #s > 0);
     new ExampleTable from apply(#G, i -> (
	       s := substring(2,G#i#0); -- remove the first two -- characters
	       i+1 => s => replace("kk", toString coeffring, demark("\n",drop(G#i,1)))))
     )
readExampleFile(String) := (filename) -> (
     G := separateRegexp("---+", get (ExampleIdeals#"source directory"|filename));
     G = apply(G, s -> select(lines s, t -> #t > 0));
     -- now for each example, find its name/number and make the string
     G = select(G, s -> #s > 0);
     new ExampleTable from apply(#G, i -> (
	       s := substring(2,G#i#0); -- remove the first two -- characters
	       i+1 => s => demark("\n",drop(G#i,1))))
     )
*-
getExampleFile = method()

-* -- remove this code
getExampleFile(String,String) := (filename,kkstring) -> (
     G := separateRegexp("---+", get filename);
     G = apply(G, s -> select(lines s, t -> #t > 0));
     -- now for each example, find its name/number and make the string
     G = select(G, s -> #s > 0);
     new ExampleTable from apply(#G, i -> (
	       s := substring(2,G#i#0); -- remove the first two -- characters
	       i+1 => s => replace("kk", kkstring, demark("\n",drop(G#i,1)))))
     )
getExampleFile(String) := (filename) -> getExampleFile(filename,"")
*-

-- New code
getExampleFile(String) := (filename) -> (
     G := separateRegexp("---+", get filename);
     G = apply(G, s -> select(lines s, t -> #t > 0));
     -- now for each example, find its name/number and make the string
     G = select(G, s -> #s > 0);
     new ExampleTable from apply(#G, i -> (
	       s := substring(2,G#i#0); -- remove the first two -- characters
	       i+1 => s => demark("\n",drop(G#i,1))))
     )
readExampleFile(String) := (filename) -> 
     getExampleFile(ExampleIdeals#"source directory"|"ExampleIdeals/"|filename)
     
replaceStrings = (L, str) -> (scan(L, v -> str = replace(v#0,v#1,str)); str)
substitute(ExampleTable, List) := (E, L) -> (
     -- L is a list of options: str => newstr, (or regex => newstr).
     -- return a new ExampleTable where each final string has the given strings in L
     -- replaced (in order).
     new ExampleTable from apply(pairs E, (k,v) -> (
	       k => (v#0 => replaceStrings(L, v#1))
	       ))
     )
substitute(ExampleTable, Option) := (E,subs) -> substitute(E, {subs})


examplesDGP = method()
examplesDGP Ring := (kk) -> substitute(readExampleFile "DGP.m2", {"kk" => toString kk})

examplesSIN = method()
examplesSIN Ring := (kk) -> substitute(readExampleFile "SIN.m2", {"kk" => toString kk})

examplesStdSingular = method()
examplesStdSingular Ring := (kk) -> substitute(readExampleFile "SIN.m2", {"kk" => toString kk})

examplesBayes = () -> readExampleFile "bayes5.m2"

-- This is a list of examples from several sources

egPermanents = (kk,m,n,size) -> (
     R := kk[vars(0..m*n-1)];
     I := permanents(size,genericMatrix(R,m,n))
     )

egHaas = (kk) -> (
     -- From Hashemi, Efficient algorithms for computing Noether normalization
     (t,x,y,z) := ("t","x","y","z")/getSymbol;
     R := kk[t,x,y,z];
     (t,x,y,z) = (t,x,y,z)/value;
     I := ideal"x8+zy4-y,y8+tx4-x,64x7y7-16x3y3zt+4y3z+4x3t-1"
     )

--katsura = method()
--katsura(ZZ,Ring) := (n,R) -> (
--     )
katsura = (n,kk) -> (
     -- This is written to match the Singular version, which seems to differ
     -- from the POSSO version
     n = n-1;
     R := kk[vars(0..n)];
     L := gens R;
     u := (i) -> (
	  if i < 0 then i = -i;
	  if i <= n then L_i else 0_R);
     f1 := -1 + sum for i from -n to n list u i;
     I := ideal prepend(f1,
	  apply(0..n-1, i -> (
	       - u i + sum(-n..n, j -> (u j) * (u (i-j)))
	       )))
     )

cyclicRoots = (n,kk) -> (
     R := kk[vars(0..n-1)];
     ideal apply(1..n-1, d-> sum(0..n-1, i -> product(d, k -> R_((i+k)%n)))) 
       + ideal(product gens R - 1))

cyclicRootsHomogeneous = (n,kk) -> (
     R := kk[vars(0..n)];
     ideal apply(1..n-1, d-> sum(0..n-1, i -> product(d, k -> R_((i+k)%n)))) 
       + ideal(product(n, i -> R_i) - R_n^n))

commuting4by4 = (kk) -> (
  R := kk[vars(0..31),
         MonomialOrder=>{8, 12, 12}, 
	 MonomialSize=>8];
  I := ideal"
          -jo+ip-vA+uB-xC+wD, 
	  -ap+bo+cp-do+kB-lA+mD-nC, 
	  -aB+bA+eB-fA+pq-or-zC+yD, 
	  -aD+bC+gD-hC+ps-ot+BE-AF, 
	  aj-bi-cj+di-qv+ru-sx+tw, 
	  jo-ip-lq+kr-ns+mt, 
	  -cr+dq+er-fq-iB+jA-sz+ty, 
	  -ct+ds+gt-hs-iD+jC-qF+rE, 
	  av-bu-ev+fu-jk+il-xE+wF, 
	  cl-dk-el+fk+mF-nE+ov-pu, 
	  lq-kr+vA-uB-zE+yF, 
	  -eF+fE+gF-hE+ls-kt+vC-uD, 
	  ax-bw-gx+hw-jm+in-vy+uz, 
	  cn-dm-gn+hm+kz-ly+ox-pw, 
	  ez-fy-gz+hy+nq-mr+xA-wB, 
	  ns-mt+xC-wD+zE-yF")

commuting4by4grevlex = (kk) -> (
  R := kk[vars(0..31),
	 MonomialSize=>8];
  I := ideal"
          -jo+ip-vA+uB-xC+wD, 
	  -ap+bo+cp-do+kB-lA+mD-nC, 
	  -aB+bA+eB-fA+pq-or-zC+yD, 
	  -aD+bC+gD-hC+ps-ot+BE-AF, 
	  aj-bi-cj+di-qv+ru-sx+tw, 
	  jo-ip-lq+kr-ns+mt, 
	  -cr+dq+er-fq-iB+jA-sz+ty, 
	  -ct+ds+gt-hs-iD+jC-qF+rE, 
	  av-bu-ev+fu-jk+il-xE+wF, 
	  cl-dk-el+fk+mF-nE+ov-pu, 
	  lq-kr+vA-uB-zE+yF, 
	  -eF+fE+gF-hE+ls-kt+vC-uD, 
	  ax-bw-gx+hw-jm+in-vy+uz, 
	  cn-dm-gn+hm+kz-ly+ox-pw, 
	  ez-fy-gz+hy+nq-mr+xA-wB, 
	  ns-mt+xC-wD+zE-yF")


-- The following contain the resolution tests for
-- homogeneous ideals/modules contained in the
-- paper "Standard bases, syzygies, and their 
-- implementation in SINGULAR", by Grassmann, Greuel,
-- Martin, Neumann, Pfister, Pohl, Schoenemann,
-- Siebert.
--

-- these functions aren't used or exported
-- singF = (a,b,c,t) -> x^a + y^b + z^(3*c) + x^(c+2) * y^(c-1) + 
--    x^(c-1) * y^(c-1) * z^3 + x^(c-2) * y^c * (y^2 + t * x)^2
-- singH = (a) -> x^a + y^a + z^a + x * y * z * (x + y + z)^2 + (x+y+z)^3
-- singG = (a,b,c,d,e,t) -> x^a + y^b + z^c + x^d * y^(e-5) + 
--    x^(d-2) * y^(e-3) + x^(d-3) * y^(e-4) * z^2 + 
--    x^(d-4) * y^(e-4) * (y^2 + t * x)^2

PJ = (R,m) -> (
    PJf := (a,b) -> R_(a-1) * R_(b-1) - R_(a-2) * R_(b+1);
    if m < 4 then trim ideal(0_R)
    else if m == 4 then 
	ideal(R_3 * R_0 - R_1^2, R_3 * R_1 - R_2^2)
    else if m == 5 then 
	PJ(R,4) + ideal(PJf(5,1), PJf(5,2), R_4 * R_2 - R_3^2 + R_1 * R_0)
    else if m == 6 then
	PJ(R,5) + ideal(PJf(6,1), PJf(6,2), PJf(6,3), R_5 * R_3 - R_4^2 - R_1^2)
    else if m%2 == 1 then
        PJ(R,m-1) + ideal apply(m-3, i -> PJf(m,i+1)) + ideal(R_(m-1) * R_(m-3) - R_(m-2)^2 - R_(m-4) * R_(m-6))
    else if m%2 == 0 then
        PJ(R,m-1) + ideal apply(m-3, i -> PJf(m,i+1)) + ideal(R_(m-1) * R_(m-3) - R_(m-2)^2 - 
                                                                R_(m-2)^2 - R_(m-3) * R_(m-5)))

PellikaanJaworski = (kk,m) -> (
    R := kk[vars(0..m-1)];
    PJ(R,m))

bayes = method()
bayes(List, Sequence) := Ideal => (Glist, d) -> (
    -- Note: this now uses GraphicalModels, not Markov.
    -- example: Glist is {{}, {}, {1}, {3}, {1,4}}
    --   represents a directed graph on 1..5
    -- example: d is (2,2,2,2,2) (length is #vertices in digraph of Glist
    R := markovRing d;
    Glist = for i from 0 to #Glist-1 list {i+1, Glist#i};
    G := digraph Glist;
    S := globalMarkov G;
    J := conditionalIndependenceIdeal(R,S);
    F := marginMap(1,R);
    J = F J;
    ideal mingens J
    )

Fabrice24 = (kk) -> (
  (x1, x2, x3, y1, y2, y3, z1, z2, z3) := ("x1", "x2", "x3", "y1", "y2", "y3", "z1", "z2", "z3")/getSymbol;
  R := kk[x1, x2, x3, y1, y2, y3, z1, z2, z3];
  (x1, x2, x3, y1, y2, y3, z1, z2, z3) = (x1, x2, x3, y1, y2, y3, z1, z2, z3)/value;
  ideal(62500*x1^2 + 62500*y1^2 + 62500*z1^2 -74529,
       625*x2^2 + 625*y2^2 + 625*z2^2 -1250*x2 -2624,
       12500*x3^2 + 12500*y3^2 + 12500*z3^2 + 2500*x3 -44975*y3 -10982,
       400000*x1*x2 + 400000*y1*y2 + 400000*z1*z2 -400000*x2 + 178837,
       1000000*x1*x3 + 1000000*y1*y3 + 1000000*z1*z3 + 100000*x3 -1799000*y3 -805427,
       2000000*x2*x3 + 2000000*y2*y3 + 2000000*z2*z3 -2000000*x2 + 200000*x3 -3598000*y3 -1403,
       113800000000000*x3*y2*z1 -113800000000000*x2*y3*z1 -113800000000000*x3*y1*z2 + 113800000000000*x1*y3*z2 + 113800000000000*x2*y1*z3 -113800000000000*x1*y2*z3 -206888400000000*x2*y1 + 206888400000000*x3*y1 + 206888400000000*x1*y2 -206888400000000*x3*y2 -206888400000000*x1*y3 + 206888400000000*x2*y3 -2014260000000*x2*z1 + 2014260000000*x3*z1 -61907200000000*y2*z1 + 61907200000000*y3*z1 + 2014260000000*x1*z2 -2014260000000*x3*z2 + 61907200000000*y1*z2 -61907200000000*y3*z2 -2014260000000*x1*z3 + 2014260000000*x2*z3 -61907200000000*y1*z3 + 61907200000000*y2*z3 -362960716800000*x1 + 38025201600000*x2 + 292548849600000*x3 + 11809567440000*y1 + 1475978220000*y2 -825269402280000*y3 -1212982689600000*z1 -151600474800000*z2 + 825859951200000*z3 -19295432410527,
       -777600000000*x3*y2*z1 + 777600000000*x2*y3*z1 + 777600000000*x3*y1*z2 -777600000000*x1*y3*z2 -777600000000*x2*y1*z3 + 777600000000*x1*y2*z3 -1409011200000*x2*y1 + 1409011200000*x3*y1 + 1409011200000*x1*y2 -1409011200000*x3*y2 -1409011200000*x1*y3 + 1409011200000*x2*y3 -1065312000000*x2*z1 + 1065312000000*x3*z1 -805593600000*y2*z1 + 805593600000*y3*z1 + 1065312000000*x1*z2 -1065312000000*x3*z2 + 805593600000*y1*z2 -805593600000*y3*z2 -1065312000000*x1*z3 + 1065312000000*x2*z3 -805593600000*y1*z3 + 805593600000*y2*z3 + 235685027200*x1 + 398417510400*x2 + 158626915200*x3 -311668424000*y1 -268090368000*y2 + 72704002800*y3 + 412221302400*z1 + 354583756800*z2 + 307085438400*z3 + 282499646407,
       3200*x2 + 1271)
  )

Lichtblau = (kk) -> (
     (t,x,y) := (t,x,y)/getSymbol;
     R := kk[t,x,y,MonomialOrder=>Eliminate 1];
     (t,x,y) = (t,x,y)/value;
     ideal"x-110t2+495t3-1320t4+2772t5-5082t6+7590t7-8085t8+5555t9-2189t10+374t11,
           y-22t+110t2-330t3+1848t5-3696t6+3300t7-1650t8+550t9-88t10-22t11"
     )

-- Examples from Grassmann et al, 2002, pg. 6.

examplesSingular1 = new MutableHashTable;
examplesSingular1#1 = (R) -> (
     if R === null then R = QQ{"t","x","y","z"};
     use R;
     ideal"5t3x2z+2t2y3x5,7y+4x2y+y2x+2zt,3tz+3yz2+2yz4"
     )

toClassic = method()
toClassic Ideal := (I) -> (
     g := concatenate between(",\n   ", apply(numgens I, i -> replace(///[\*\^]///,"",toString I_i)));
     "ideal\"" | g | "\""
     )

-----------------------------------------------
-- Translation to Singular --------------------
-----------------------------------------------
-- ring variable name translation
--   ring variable with no subscript, and no 's:  same
--   ring variable with complicated subscripts need to be mapped
--   I think that even doubly indexed variables can't be done?
--   
toSingular = method()
toSingular Ideal := (I) -> (
     g := concatenate between(",\n   ", apply(numgens I, i -> replace(///[\*\^]///,"",toString I_i)));
     "ideal i = " | g | ";\n"
     )
toSingular Ring := (R) -> (
     -- note: R is assumed to be a polynomial ring.  Variables allowed: single letters, 
     -- letters indexed by a single non-negative integer.
     kk := coefficientRing R;
     p := char kk;
     a := "ring R1 = "|p|",(";
     b := concatenate between(",", (gens R)/toString);
     c := "),dp;\n";
     a | b | c
     )
toSingular Ideal := (I) -> (
     a := "ideal I1 = \n";
     g := concatenate between(",\n   ", apply(numgens I, i -> toString I_i));
     a | g | ";\n"
     )
toSingular (Ideal, String) := (I,str) -> (
     a := "ideal " | str | " = \n";
     g := concatenate between(",\n   ", apply(numgens I, i -> toString I_i));
     a | g | ";\n"
     )

timerWrap = (str) -> (
     "rtimer = 1;\nint ti=rtimer;\n"
     |str|
     ///int ti2=rtimer-ti;
print("time used"); print(ti2);
///
     )
-- computing a GB in Singular
-- string with name of ideal @I@
singGBstring = 
  ///ideal J1=groebner(@I@);
print(size(J1));
///

-- computing an integral closure of a ring in Singular
-- this is the integral closure of R/I...!
-- string with name of ideal: @I@
singICstring = "list nor=normal(@I@);\n"

singularGB = method()
singularGB String := (idealName) -> 
     timerWrap replace("@I@",idealName,singGBstring)
          
singularIntegralClosure = method()
singularIntegralClosure String := (idealName) -> 
     timerWrap replace("@I@",idealName,singICstring)

runSingularGB = method()
runSingularGB Ideal := (I) -> (
     "foo"
     << toSingular ring I 
     << toSingular I
     << singularGB "I"
     << "exit(0);\n" << close;
     run "/sw/bin/Singular <foo"
     )
runSingularGB Ideal := (I) -> (
     str := toSingular ring I | toSingular I | singularGB "I1" | "\nexit(0);\n";
     runSingular str
     )

--------------------------
singGBtemplate = 
///proc nummonoms (ideal L1)
{
  int i;
  int result=0;
  for (i=1; i<=size(L1); i++) {
    result = result + size(L1[i]);
  }
  return(result);
}

$ring
$ideal
timer = 1;
int ti=timer;
ideal J1=groebner(I1);
int ti2=timer-ti;
printf("time=%s sec, #gb=%s #monoms=%s", ti2, size(J1), nummonoms(J1));
exit;
///
--------------------------

singularGBString = method()
singularGBString Ideal := (I) -> (
     replace("\\$ring", toSingular ring I,
	  replace("\\$ideal", toSingular I, singGBtemplate))
     )

runSingular = method()
runSingular String := (str) -> (
     "foo" << str << endl << close;
     get "!/sw/bin/Singular <foo"
     )

-----------------------------------------------
-- Translation to Magma -----------------------
-----------------------------------------------

toMagma = method()
toMagma Ring := (R) -> (
     -- note: R is assumed to be a polynomial ring.  Variables allowed: single letters, 
     -- letters indexed by a single non-negative integer.
     -- For now the base ring needs to be ZZ/p or QQ.
     kk := coefficientRing R;
     p := char kk;
     basering := if p === 0 then "RationalField()" else "GF("|p|")";
     "R1<" | concatenate between(",", (gens R)/toString) | "> := PolynomialRing(" 
       | basering | "," | toString numgens R | ",\"grevlex\");"
     )
toMagma Ideal := (I) -> (
     a := "I1 := ideal< R1 | \n   ";
     g := concatenate between(",\n   ", apply(numgens I, i -> toString I_i));
     a | g | ">;\n" 
     )

magmaICstring = "time Js := Normalization(@I@);\n"

magmaIntegralClosure = method()
magmaIntegralClosure String := (idealName) -> 
     replace("@I@",idealName,magmaICstring)

runMagmaGB = method()
runMagmaGB Ideal := (I) -> (
     "foo" 
     << toMagma ring I << endl
     << toMagma I
     << "time J1 := GroebnerBasis(I1);\n"
     << "#J1;\n"
     << "quit;\n" << close;
     run "magma <foo"
     )

runMagmaIntegralClosure = method()
runMagmaIntegralClosure Ideal := (I) -> (
     "foo" 
     << toMagma ring I << endl
     << toMagma I
     << "time Js := Normalization(I1);\n"
     << "#Js;\n"
     << "quit;\n" << close;
     run "magma <foo"
     )

magmaGBtemplate = 
///
$ring
$ideal
time J1 := GroebnerBasis(I1);
#J1;
quit;
///
--------------------------

magmaGBString = method()
magmaGBString Ideal := (I) -> (
     replace("\\$ring", toMagma ring I,
	  replace("\\$ideal", toMagma I, magmaGBtemplate))
     )

beginDocumentation()

doc ///
  Key
    ExampleIdeals
  Headline
    a package containing examples for basic computations
  Description
   Text
      This package allows one to collect examples into a single file, 
      and conveniently run these examples, or computations based on these examples.

      For example, an @TO ExampleTable@ can be read into Macaulay2, and/or computations
      based on them can be executed.
   -- comment out non-working example:
   -- Example
   --    E = getM2ExampleFile("bayes", CoefficientRing => ZZ/32003);
   --    keys E
   --    E
///

doc ///
  Key
    ExampleTable
  Headline
    hash table containing example ideals, computations, or other M2 constructions
  Description
   Text
      The format of an {\tt ExampleTable}, E: the keys should be integers, starting at 1, 
      and the value E#i is a pair (strname => str), where strname is a very short description
      of the example, and {\tt str} is M2 code which generates the example.
   Example
     E = new ExampleTable from {
	  1 => "eg1" => "R = QQ[a..d];\nI = ideal(a^2,b*c,c*d,b^3-c^2*d)"
	  }
   Example
     E#1#1
     example(E,1)   
     box(E)
   Text
      Normally, one does not create such a table directly, one reads one from a file, using
      @TO getExampleFile@ or @TO readExampleFile@.
  SeeAlso
     getExampleFile
     readExampleFile
     example
     box
///

doc ///
  Key
    readExampleFile
  Headline
    read an example file which is packaged with ExampleIdeals
  Usage
    readExampleFile(filename)
  Inputs
    filename:String
  Outputs
    :ExampleTable
  Description
   Text
     read in a predefined example file.  Possible names include:
     DGP, SIN, bayes5, gb-examples, local, pd-run-examples, stdSingular, and symbolicdata.
     (DGP stands for Decker-Greuel-Pfister, SIN for Singular, and symbolicdata 
     for some of the examples at
     symbolicdata.org, which doesn't appear to exist anymore)
   Example
     H = readExampleFile "bayes5.m2";
     keys H
     H#200#0
     H#200#1
     value H#200#1
     apply(10..20, i -> codim value H#i#1)
  SeeAlso
     getExampleFile
///

end--------------------------------------------------

restart

debug needsPackage "ExampleIdeals"
E = examplesBayes();
elapsedTime for k in keys E do (
    I = example(E, k);
    elapsedTime c := codim I;
    << E#k#0 << " has codim "  << c << endl;
    )

box E
example(E, 5)

fil = openOut "markovIdeals";
for k in keys E do (
    J = example(E, k);
    fil << show(E, k) << endl;
    for f in J_* do fil << f << endl;
    )
close fil

fil = openOut "graphModelsIdeals";
for k in keys E do (
    J = example(E, k);
    fil << show(E, k) << endl;
    for f in J_* do fil << f << endl;
    )
close fil

I2 = example(E, 5);
------------------------------------
-- examples for the singular code --
------------------------------------
restart
loadPackage "ExampleIdeals"
R = QQ[a..d,h,r,t]
assert(toSingular R == "ring R = 0,(a,b,c,d,h,r,t),dp;\n")
R = QQ[a..d,h,rt]
assert(toSingular R == "ring R = 0,(a,b,c,d,h,rt),dp;\n")
R = QQ[x_1..x_4]
assert(toSingular R == "ring R = 0,(x(1)-x(4)),dp;\n")

singularGB
loadPackage "ExampleIdeals"
debug ExampleIdeals
R = ZZ/101[a..d]
I = ideal random(R^1, R^{-2,-2})

s = concatenate between("\n",{toSingular ring I,
     toSingular I,
     replace(singularGB, "@I@", "I")})

"!/sw/bin/Singular" << s << close



print toSingular R
print toSingular I
print singularIntegralClosure "I"

runMagmaGB I
runSingularGB I
print toMagma R; print toMagma I

time H = examplesDGP QQ
time H = examplesSIN QQ

time H = examplesBayes();
time scan(keys H, x -> example(H,x))

I = example(H,138);
codim I
degree I
betti gens gb I

gbTrace=1
scan(keys H, x -> (
	  time G := gb example(H,x); 
	  M := monomialIdeal leadTerm G;
	  done := if M == radical M then "yes" else "no";
	  << "doing " << x << " radical? " << done << endl;
	  ))

time possibleNonradicals = select(keys H, x -> (
	  time G := gb example(H,x); 
	  M := monomialIdeal leadTerm G;
	  M != radical M))

possibleNonradicals = {10, 20, 23, 24, 25, 27, 37, 55, 58, 
     67, 71, 73, 74, 75, 76, 
     78, 81, 103, 118, 121, 122, 124, 125, 127, 134, 138, 139, 
     140, 145, 148, 150, 152, 154, 155, 157, 158, 159, 169, 
     202, 204, 206, 208, 209, 212, 213, 218, 228, 231, 
     233, 236, 239}

I = example(H,212)
Isat = saturate(I,p_(1,1,1,1,1))
Isat = trim Isat;
Irest = I : Isat;
intersect(Isat,Irest) == I -- true
m = first independentSets(Irest, Limit=>1)

debug PrimaryDecomposition
flatt(Irest,m)
flattener
example(H,71)
H#10
inI = monomialIdeal I;
inI == radical inI

numgens oo
time C = decompose I;
G
box H
box(H,4)
example(H,15)


-- I used the code here to create the file bayes5.m2
scan(#D5s, i -> (
	  print "------------------------------------------------"; 
	  print("--binary bayes "|i|" "|toString D5s#i);
	  print("bayes("|toString D5s#i|",(2,2,2,2,2))")))


apply(keys H, a -> example(H,a))
oo/class
H = examplesDGP
example(H,1,CoefficientRing=>QQ)
S = QQ[z_1..z_10]
example(H,1,Ring=>S)
show H
show(H,1)
box(H,1)
box H
box(H,{1,3})
box(H,{3,1})
show(H,{3,1})
kk = QQ; value H#"chemistry"#1()

print netList sort apply(pairs H, x -> {x#0, x#1#1()})
netList sort apply(pairs H, x -> {x#0, x#1#0})
kk = ZZ/32003; value H#"sy-j"#1()
pairs H

I = katsura(5,QQ)
x = symbol x
R = QQ[x_0..x_4]
I = substitute(I,vars R)
SIN#4 QQ
egPermanents(QQ,3,4,3)
egSYJ QQ
egSYSt QQ
egGerdt QQ
egHorrocks QQ

monomialIdeal leadTerm I
radical oo
codim I
dim I
I1 = substitute(I, u => u + 3*x + 5*y + 7*z)
radical monomialIdeal leadTerm I1

--
loadPackage "ExampleIdeals"
I = cyclicRootsHomogeneous(7,ZZ/23)
gbTrace=3
time gens gb I;
time gens gb(I, Algorithm=>LinearAlgebra, GBDegrees=>{1,1,1,1,1,1,1,1});

loadPackage "ExampleIdeals"
I = cyclicRootsHomogeneous(8,ZZ/23)
time gens gb(I, Algorithm=>LinearAlgebra, GBDegrees=>{1,1,1,1,1,1,1,1,1});

loadPackage "ExampleIdeals"
I = cyclicRootsHomogeneous(9,ZZ/23)
time gens gb(I, Algorithm=>LinearAlgebra, GBDegrees=>{1,1,1,1,1,1,1,1,1,1});

restart
cyclicRootsHomogeneous = (n,kk) -> (
     R = kk[vars(0..n)];
     ideal apply(1..n-1, d-> sum(0..n-1, i -> product(d, k ->
R_((i+k)%n))))
       + ideal(product(n, i -> R_i) - R_n^n))
I = cyclicRootsHomogeneous(7,ZZ/23)
time gens gb(I, Algorithm=>LinearAlgebra, GBDegrees=>toList(numgens ring I:1));

I = Fabrice24(ZZ/101)
gbTrace=3
gens gb I
codim I
numgens R
numgens I
eliminate({x1, x2, x3, y1, y2, y3, z1},I)
factor(o12_4)
factor oo
degree I

I = Lichtblau(QQ)
eliminate({t},I)

p = symbol p;
R = ZZ/32003[reverse(p_(1,1,1,1,1)..p_(2,2,2,2,2)), MonomialSize=>8];
J = ideal(
	      -p_(1,1,2,1,1)*p_(2,1,1,1,1)+p_(1,1,1,1,1)*p_(2,1,2,1,1),
	      -p_(1,1,2,1,2)*p_(2,1,1,1,2)+p_(1,1,1,1,2)*p_(2,1,2,1,2),
	      -p_(1,1,2,2,1)*p_(2,1,1,2,1)+p_(1,1,1,2,1)*p_(2,1,2,2,1),
	      -p_(1,1,2,2,2)*p_(2,1,1,2,2)+p_(1,1,1,2,2)*p_(2,1,2,2,2),
	      -p_(1,2,2,1,1)*p_(2,2,1,1,1)+p_(1,2,1,1,1)*p_(2,2,2,1,1),
	      -p_(1,2,2,1,2)*p_(2,2,1,1,2)+p_(1,2,1,1,2)*p_(2,2,2,1,2),
	      -p_(1,2,2,2,1)*p_(2,2,1,2,1)+p_(1,2,1,2,1)*p_(2,2,2,2,1),
	      -p_(1,2,2,2,2)*p_(2,2,1,2,2)+p_(1,2,1,2,2)*p_(2,2,2,2,2),
	      -p_(1,1,1,1,2)*p_(1,2,1,1,1)+p_(1,1,1,1,1)*p_(1,2,1,1,2),
	      -p_(1,1,1,2,1)*p_(1,2,1,1,1)+p_(1,1,1,1,1)*p_(1,2,1,2,1),
	      -p_(1,1,1,2,1)*p_(1,2,1,1,2)+p_(1,1,1,1,2)*p_(1,2,1,2,1),
	      -p_(1,1,1,2,2)*p_(1,2,1,1,1)+p_(1,1,1,1,1)*p_(1,2,1,2,2),
	      -p_(1,1,1,2,2)*p_(1,2,1,1,2)+p_(1,1,1,1,2)*p_(1,2,1,2,2),
	      -p_(1,1,1,2,2)*p_(1,2,1,2,1)+p_(1,1,1,2,1)*p_(1,2,1,2,2),
	      -p_(1,1,2,1,2)*p_(1,2,2,1,1)+p_(1,1,2,1,1)*p_(1,2,2,1,2),
	      -p_(1,1,2,2,1)*p_(1,2,2,1,1)+p_(1,1,2,1,1)*p_(1,2,2,2,1),
	      -p_(1,1,2,2,1)*p_(1,2,2,1,2)+p_(1,1,2,1,2)*p_(1,2,2,2,1),
	      -p_(1,1,2,2,2)*p_(1,2,2,1,1)+p_(1,1,2,1,1)*p_(1,2,2,2,2),
	      -p_(1,1,2,2,2)*p_(1,2,2,1,2)+p_(1,1,2,1,2)*p_(1,2,2,2,2),
	      -p_(1,1,2,2,2)*p_(1,2,2,2,1)+p_(1,1,2,2,1)*p_(1,2,2,2,2),
	      -p_(1,1,1,1,2)*p_(1,2,1,1,1)+p_(1,1,1,1,1)*p_(1,2,1,1,2),
	      -p_(1,1,1,2,2)*p_(1,2,1,2,1)+p_(1,1,1,2,1)*p_(1,2,1,2,2),
	      -p_(1,1,2,1,2)*p_(1,2,2,1,1)+p_(1,1,2,1,1)*p_(1,2,2,1,2),
	      -p_(1,1,2,2,2)*p_(1,2,2,2,1)+p_(1,1,2,2,1)*p_(1,2,2,2,2),
	      -p_(1,1,1,2,1)*p_(1,2,1,1,1)+p_(1,1,1,1,1)*p_(1,2,1,2,1),
	      -p_(1,1,1,2,2)*p_(1,2,1,1,2)+p_(1,1,1,1,2)*p_(1,2,1,2,2),
	      -p_(1,1,2,2,1)*p_(1,2,2,1,1)+p_(1,1,2,1,1)*p_(1,2,2,2,1),
	      -p_(1,1,2,2,2)*p_(1,2,2,1,2)+p_(1,1,2,1,2)*p_(1,2,2,2,2),
	      -p_(1,1,1,1,2)*p_(1,1,1,2,1)+p_(1,1,1,1,1)*p_(1,1,1,2,2)
		+p_(1,1,1,2,2)*p_(1,1,2,1,1)-p_(1,1,1,2,1)*p_(1,1,2,1,2)
		-p_(1,1,1,1,2)*p_(1,1,2,2,1)-p_(1,1,2,1,2)*p_(1,1,2,2,1)
		+p_(1,1,1,1,1)*p_(1,1,2,2,2)+p_(1,1,2,1,1)*p_(1,1,2,2,2)
		+p_(1,1,1,2,2)*p_(1,2,1,1,1)+p_(1,1,2,2,2)*p_(1,2,1,1,1)
		-p_(1,1,1,2,1)*p_(1,2,1,1,2)-p_(1,1,2,2,1)*p_(1,2,1,1,2)
		-p_(1,1,1,1,2)*p_(1,2,1,2,1)-p_(1,1,2,1,2)*p_(1,2,1,2,1)
		-p_(1,2,1,1,2)*p_(1,2,1,2,1)+p_(1,1,1,1,1)*p_(1,2,1,2,2)
		+p_(1,1,2,1,1)*p_(1,2,1,2,2)+p_(1,2,1,1,1)*p_(1,2,1,2,2)
		+p_(1,1,1,2,2)*p_(1,2,2,1,1)+p_(1,1,2,2,2)*p_(1,2,2,1,1)
		+p_(1,2,1,2,2)*p_(1,2,2,1,1)-p_(1,1,1,2,1)*p_(1,2,2,1,2)
		-p_(1,1,2,2,1)*p_(1,2,2,1,2)-p_(1,2,1,2,1)*p_(1,2,2,1,2)
		-p_(1,1,1,1,2)*p_(1,2,2,2,1)-p_(1,1,2,1,2)*p_(1,2,2,2,1)
		-p_(1,2,1,1,2)*p_(1,2,2,2,1)-p_(1,2,2,1,2)*p_(1,2,2,2,1)
		+p_(1,1,1,1,1)*p_(1,2,2,2,2)+p_(1,1,2,1,1)*p_(1,2,2,2,2)
		+p_(1,2,1,1,1)*p_(1,2,2,2,2)+p_(1,2,2,1,1)*p_(1,2,2,2,2));
R = (coefficientRing R)[x_1..x_(numgens R), MonomialSize=>8]
I = sub(J,vars R)
time gens gb(I, MaxReductionCount=>3000);
print toMagma R; print toMagma I
runMagmaGB I
runSingularGB I
-* -- magma
R<x_1,x_2,x_3,x_4,x_5,x_6,x_7,x_8,x_9,x_10,x_11,x_12,x_13,x_14,x_15,x_16,x_17,x_18,x_19,x_20,x_21,x_22,x_23,x_24,x_25,x_26,x_27,x_28,x_29,x_30,x_31,x_32> := PolynomialRing(GF(32003),32,"grevlex");
I := ideal< R | 
   -x_16*x_28+x_12*x_32,
   -x_15*x_27+x_11*x_31,
   -x_14*x_26+x_10*x_30,
   -x_13*x_25+x_9*x_29,
   -x_8*x_20+x_4*x_24,
   -x_7*x_19+x_3*x_23,
   -x_6*x_18+x_2*x_22,
   -x_5*x_17+x_1*x_21,
   -x_24*x_31+x_23*x_32,
   -x_24*x_30+x_22*x_32,
   -x_23*x_30+x_22*x_31,
   -x_24*x_29+x_21*x_32,
   -x_23*x_29+x_21*x_31,
   -x_22*x_29+x_21*x_30,
   -x_20*x_27+x_19*x_28,
   -x_20*x_26+x_18*x_28,
   -x_19*x_26+x_18*x_27,
   -x_20*x_25+x_17*x_28,
   -x_19*x_25+x_17*x_27,
   -x_18*x_25+x_17*x_26,
   -x_24*x_31+x_23*x_32,
   -x_22*x_29+x_21*x_30,
   -x_20*x_27+x_19*x_28,
   -x_18*x_25+x_17*x_26,
   -x_24*x_30+x_22*x_32,
   -x_23*x_29+x_21*x_31,
   -x_20*x_26+x_18*x_28,
   -x_19*x_25+x_17*x_27,
   -x_18*x_19+x_17*x_20+x_20*x_21-x_19*x_22-x_18*x_23-x_22*x_23+x_17*x_24+x_21*x_24+x_20*x_25+x_24*x_25-x_19*x_26-x_23*x_26-x_18*x_27-x_22*x_27-x_26*x_27+x_17*x_28+x_21*x_28+x_25*x_28+x_20*x_29+x_24*x_29+x_28*x_29-x_19*x_30-x_23*x_30-x_27*x_30-x_18*x_31-x_22*x_31-x_26*x_31-x_30*x_31+x_17*x_32+x_21*x_32+x_25*x_32+x_29*x_32>;
time J := GroebnerBasis(I);
*-



---------------------------------------------------------------
-- examples from packages/ExampleIdeals/2019PDexamples.m2
---------------------------------------------------------------

-- Mike Stillman contributed this example where the new code
-- for minimal primes runs much faster.
-- This file was added to the ExampleIdeals directory
-- at the IMA 2019 M2 workshop by Primary Decomposition group.
makeIdeal = (kk) -> (
    S = kk[x_1..x_5,y_1..y_5];
    I = ideal(y_1+y_3,
        -x_2*y_1-x_5*y_1+x_1*y_2+x_1*y_5-y_1,
        x_2*y_1-x_1*y_2-x_3*y_2+x_2*y_3,
        x_3*y_2-x_2*y_3-x_4*y_3+x_3*y_4-y_3,
        x_4*y_3-x_3*y_4-x_5*y_4+x_4*y_5,
        x_5*y_1+x_5*y_4-x_1*y_5-x_4*y_5,
        x_1^2+y_1^2-1,
        x_2^2+y_2^2-1,
        x_3^2+y_3^2-1,
        x_4^2+y_4^2-1,
        x_5^2+y_5^2-1
        )
    )
I = makeIdeal QQ
S = ring I

-- This example contains an ideal whose primary decomposition
-- runs for a long time in M2 (using the old default methods)
-- but can be decomposed quickly in Singular using GTZ.
-- It was communicated by Andrew Carroll and Jerzy Weyman to
-- Federico Galetto, and it comes from the orbit closure of
-- some quiver representation.
R=QQ[x_11,x_12,x_21,x_22,y_11,y_12,y_21,y_22,z_11,z_12,z_21,z_22]
g1 = x_11^2+x_21*x_12;
g2 = x_11*x_12+x_12*x_22;
g3 = x_11*x_21+x_21*x_22;
g4 = x_21*x_12+x_22^2;
g5 = z_11^2+z_21*z_12;
g6 = z_11*z_12+z_12*z_22;
g7 = z_11*z_21+z_21*z_22;
g8 = z_21*z_12+z_22^2;
g9 = x_11*y_11*z_11+x_12*y_21*z_11+x_11*y_12*z_21+x_12*y_22*z_21;
g10 = x_11*y_11*z_12+x_12*y_21*z_12+x_11*y_12*z_22+x_12*y_22*z_22;
g11 = x_21*y_11*z_11+x_22*y_21*z_11+x_21*y_12*z_21+x_22*y_22*z_21;
g12 = x_21*y_11*z_12+x_22*y_21*z_12+x_21*y_12*z_22+x_22*y_22*z_22;
I = ideal(g1,g2,g3,g4,g5,g6,g7,g8,g9,g10,g11,g12);

---------------------------------------------------------------
-- examples from packages/MinimalPrimes/radical.m2
---------------------------------------------------------------

load "../MinimalPrimes/radical.m2"

R = QQ[x,y,z]/(x^2+y^2+z^2)
I = ideal"x,y"
rad I

R = ZZ/32003[b,s,t,u,v,w,x,y,z]
I = ideal(
    b*v+s*u,
    b*w+t*u,
    s*w+t*v,
    b*y+s*x,
    b*z+t*x,
    s*z+t*y,
    u*y+v*x,
    u*z+w*x,
    v*z+w*y)
time rad I
time intersect decompose I

R = ZZ/32003[b,s,t,u,v,w,x,y,z]
I = ideal(
    s*u-b*v,
    t*v-s*w,
    v*x-u*y,
    w*y-v*z)
time rad I
time intersect decompose I
time decompose I

R = ZZ/32003[a,b,c,d,e,f,g,h]
I = ideal(
    h+f+e-d-a,
    2*f*b+2*e*c+2*d*a-2*a^2-a-1,
    3*f*b^2+3*e*c^2-3*d*a^2-d+3*a^3+3*a^2+4*a,
    6*g*e*b-6*d*a^2-3*d*a-d+6*a^3+6*a^2+4*a,
    4*f*b^3+4*e*c^3+4*d*a^3+4*d*a-4*a^4-6*a^3-10*a^2-a-1,
    8*g*e*c*b+8*d*a^3+4*d*a^2+4*d*a-8*a^4-12*a^3-14*a^2-3*a-1,
    12*g*e*b^2+12*d*a^3+12*d*a^2+8*d*a-12*a^4-18*a^3-14*a^2-a-1,
    -24*d*a^3-24*d*a^2-8*d*a+24*a^4+36*a^3+26*a^2+7*a+1)
time decompose I
time rad I -- not good yet

R = ZZ/32003[a,b,c,d,f,g,h,k,l,s,t,u,v,w,x,y,z, MonomialSize=>8]
I = ideal(
    -a*b-a*d+2*a*h,
    a*d-b*d-c*f-2*a*h+2*b*h+2*c*k,
    a*b-a*d-2*b*h+2*d*h-2*c*k+2*f*k+2*g*l,
    a*c-2*c*s-a*t+2*b*t,
    a*c-c*s-2*a*t+b*t,
    -d-3*s+4*u,
    -f-3*t+4*v,
    -g+4*w,
    -a+2*x,
    -b^2-c^2+2*b*x+2*c*y,
    -d^2-f^2-g^2+2*d*x+2*f*y+2*g*z)
time decompose I
time rad I -- not good yet

R0 = (ZZ/32003)[w_(0,0), w_(0,1), w_(0,2), v, u, z, Degrees => {6:1}, Heft => {1}, MonomialOrder => VerticalList{MonomialSize => 32, GRevLex => {3:1}, GRevLex => {1}, GRevLex => {2:1}, Position => Up}, DegreeRank => 1]
J0 = ideal(w_(0,0)*u-v^2-2*v*z-z^2,w_(0,2)^2+3378*w_(0,0)*v+3378*w_(0,0)*z+8595*w_(0,1)*v-9157*w_(0,1)*u+8595*w_(0,1)*z+8990*w_(0,2)*v+502*w_(0,2)*u+13486*w_(0,2)*z-14160*v^2-7666*v*u+6065*v*z+911*u^2+6866*u*z-14748*z^2,w_(0,1)*w_(0,2)-2296*w_(0,0)*v-2296*w_(0,0)*z+10183*w_(0,1)*v-10093*w_(0,1)*u+12431*w_(0,1)*z-15664*w_(0,2)*v+1481*w_(0,2)*u-15867*w_(0,2)*z+13406*v^2+2557*v*u-3813*v*z+13277*u^2+11829*u*z+6482*z^2,w_(0,0)*w_(0,2)+6955*w_(0,0)*v+9203*w_(0,0)*z+4020*w_(0,1)*v+8014*w_(0,1)*u+4020*w_(0,1)*z-2330*w_(0,2)*v-4665*w_(0,2)*u-2329*w_(0,2)*z+2106*v^2-15232*v*u+5834*v*z+5406*u^2+4443*u*z+5976*z^2,w_(0,1)^2+1511*w_(0,0)*v+1511*w_(0,0)*z-887*w_(0,1)*v-1020*w_(0,1)*u-1293*w_(0,1)*z-13362*w_(0,2)*v+5279*w_(0,2)*u-13362*w_(0,2)*z-2150*v^2+807*v*u-1705*v*z+8408*u^2-15068*u*z+9651*z^2,w_(0,0)*w_(0,1)+14147*w_(0,0)*v+13944*w_(0,0)*z+2558*w_(0,1)*v+5113*w_(0,1)*u+2559*w_(0,1)*z+213*w_(0,2)*v+426*w_(0,2)*u+213*w_(0,2)*z+14843*v^2+7373*v*u+3383*v*z+5350*u^2-11815*u*z-11663*z^2,w_(0,0)^2-214*w_(0,0)*v-212*w_(0,0)*z-12*w_(0,1)*v-24*w_(0,1)*u-12*w_(0,1)*z-w_(0,2)*v-2*w_(0,2)*u-w_(0,2)*z-518*v^2-184*v*u-1062*v*z-25*u^2-244*u*z-543*z^2,u^3-u*z^2,v*u^2-v*z^2+u^2*z-z^3,-w_(0,0)*z^2+v^2*u+2*v*u*z+u^2*z+u*z^2-z^3,-214*w_(0,0)*v*z^2-212*w_(0,0)*z^3-12*w_(0,1)*v*z^2-24*w_(0,1)*u*z^2-12*w_(0,1)*z^3-w_(0,2)*v*z^2-2*w_(0,2)*u*z^2-w_(0,2)*z^3+v^4+4*v^3*z-512*v^2*z^2-184*v*u*z^2-1058*v*z^3-26*u^2*z^2-244*u*z^3-541*z^4,12778*w_(0,0)*v*z^2+12517*w_(0,0)*z^3+708*w_(0,1)*v*z^2+1415*w_(0,1)*u*z^2+708*w_(0,1)*z^3+11078*w_(0,2)*v^2*u+15899*w_(0,2)*v*u^2-9847*w_(0,2)*v*u*z+59*w_(0,2)*v*z^2+8411*w_(0,2)*u^3-5026*w_(0,2)*u^2*z+11196*w_(0,2)*u*z^2+59*w_(0,2)*z^3-1277*v^4-11258*v^3*u-5108*v^3*z-9055*v^2*u^2+946*v^2*u*z-9103*v^2*z^2+11814*v*u^3-3556*v*u^2*z+14519*v*u*z^2-6512*v*z^3+8502*u^4+8105*u^3*z+10968*u^2*z^2+5855*u*z^3-1501*z^4,2393*w_(0,0)*v*z^2+2607*w_(0,0)*z^3+121*w_(0,1)*v*z^2+228*w_(0,1)*u*z^2+121*w_(0,1)*z^3-4923*w_(0,2)*v^2*u+1232*w_(0,2)*v*u^2-9846*w_(0,2)*v*u*z+10*w_(0,2)*v*z^2-4923*w_(0,2)*u^3-3691*w_(0,2)*u^2*z-4904*w_(0,2)*u*z^2+10*w_(0,2)*z^3+12274*v^4-1038*v^3*u-14910*v^3*z+6619*v^2*u^2-4649*v^2*u*z+14818*v^2*z^2-15939*v*u^3-2607*v*u^2*z-4344*v*u*z^2-4158*v*z^3-6315*u^4-3854*u^3*z+9218*u^2*z^2-133*u*z^3-13943*z^4,9597*w_(0,0)*v*z^2+12583*w_(0,0)*z^3-6552*w_(0,1)*v*z^2-13104*w_(0,1)*u*z^2-6552*w_(0,1)*z^3-546*w_(0,2)*v*z^2+w_(0,2)*u^3-1093*w_(0,2)*u*z^2-546*w_(0,2)*z^3+546*v^4+1571*v^3*u+2184*v^3*z+2819*v^2*u*z+8475*v^2*z^2-804*v*u^2*z-3530*v*u*z^2-810*v*z^3+15109*u^2*z^2-5535*u*z^3-4661*z^4)
time decompose J0 -- this time, this one is very bad
time rad J0 -- and this one is very good

R0 = (ZZ/32003)[w_(0,0), w_(0,1), w_(0,2), w_(0,3), w_(0,4), w_(0,5), v, u, z, Degrees => {9:1}, Heft => {1}, MonomialOrder => VerticalList{MonomialSize => 32, GRevLex => {6:1}, GRevLex => {1}, GRevLex => {2:1}, Position => Up}, DegreeRank => 1]
J0 = ideal(w_(0,2)*v+9428*w_(0,2)*z-6100*w_(0,3)*v+7354*w_(0,3)*u-6312*w_(0,3)*z+1840*w_(0,4)*v+8112*w_(0,4)*u+1840*w_(0,4)*z+6100*w_(0,5)*u-10532*w_(0,5)*z-3247*v*z+13997*u*z+14070*z^2,w_(0,1)*z-15633*w_(0,2)*z-498*w_(0,3)*v+9803*w_(0,3)*u+15078*w_(0,3)*z-3827*w_(0,4)*v-11798*w_(0,4)*u-3827*w_(0,4)*z+498*w_(0,5)*u+3646*w_(0,5)*z-563*v*z+334*u*z+9246*z^2,w_(0,1)*u+12802*w_(0,2)*u-11891*w_(0,2)*z-7319*w_(0,3)*v-8378*w_(0,3)*u+6728*w_(0,3)*z+1264*w_(0,4)*v-10334*w_(0,4)*u+1264*w_(0,4)*z-4756*w_(0,5)*v+4741*w_(0,5)*u-6147*w_(0,5)*z+623*v^2-11023*v*u+12718*v*z+9112*u^2-8759*u*z-13856*z^2,w_(0,1)*v-w_(0,2)*u+5868*w_(0,2)*z-12083*w_(0,3)*v+3765*w_(0,3)*u-1469*w_(0,3)*z+13219*w_(0,4)*v+9702*w_(0,4)*u+13219*w_(0,4)*z+12083*w_(0,5)*u+4653*w_(0,5)*z-2810*v*z+10445*u*z+13715*z^2,w_(0,0)*z+9765*w_(0,2)*z+12581*w_(0,3)*v-13568*w_(0,3)*u-13609*w_(0,3)*z-9392*w_(0,4)*v+2096*w_(0,4)*u-9392*w_(0,4)*z-12581*w_(0,5)*u-8299*w_(0,5)*z+3373*v*z-10779*u*z+9043*z^2,w_(0,0)*u-v^2-2*v*z-z^2,w_(0,0)*v+12802*w_(0,2)*u+10347*w_(0,2)*z+12103*w_(0,3)*v+5190*w_(0,3)*u-11666*w_(0,3)*z+10656*w_(0,4)*v-12430*w_(0,4)*u+10656*w_(0,4)*z-4756*w_(0,5)*v-14681*w_(0,5)*u+2152*w_(0,5)*z+623*v^2-11023*v*u+9346*v*z+9112*u^2+2020*u*z+9105*z^2,w_(0,5)^2+15447*w_(0,2)*u-15064*w_(0,2)*z-5900*w_(0,3)*v+7864*w_(0,3)*u+5296*w_(0,3)*z+2354*w_(0,4)*v-6631*w_(0,4)*u+8493*w_(0,4)*z+1559*w_(0,5)*v+4095*w_(0,5)*u-3080*w_(0,5)*z+8124*v^2+4156*v*u+15167*v*z+9462*u^2-4081*u*z+4687*z^2,w_(0,4)*w_(0,5)-4893*w_(0,2)*u-7303*w_(0,2)*z+4388*w_(0,3)*v-14001*w_(0,3)*u-15376*w_(0,3)*z+10434*w_(0,4)*v+6352*w_(0,4)*u-13392*w_(0,4)*z+1462*w_(0,5)*v+6691*w_(0,5)*u-320*w_(0,5)*z+10453*v^2+8164*v*u-7097*v*z+14362*u^2-3443*u*z+5824*z^2,w_(0,3)*w_(0,5)+4583*w_(0,2)*u+11704*w_(0,2)*z+15151*w_(0,3)*v+936*w_(0,3)*u-2505*w_(0,3)*z+13918*w_(0,4)*v-3035*w_(0,4)*u+1206*w_(0,4)*z+4703*w_(0,5)*v+954*w_(0,5)*u-6710*w_(0,5)*z-3364*v^2-15337*v*u-4273*v*z-9965*u^2-1583*u*z-9705*z^2,w_(0,2)*w_(0,5)-2871*w_(0,2)*u+98*w_(0,2)*z-4040*w_(0,3)*v-936*w_(0,3)*u+6560*w_(0,3)*z-8857*w_(0,4)*v+50*w_(0,4)*u-14930*w_(0,4)*z+10638*w_(0,5)*v-1035*w_(0,5)*u-10770*w_(0,5)*z+14782*v^2+2268*v*u-9743*v*z-9527*u^2+1701*u*z-7994*z^2,w_(0,1)*w_(0,5)+2493*w_(0,2)*u+7064*w_(0,2)*z+2756*w_(0,3)*v+4383*w_(0,3)*u+11875*w_(0,3)*z+9675*w_(0,4)*v+3006*w_(0,4)*u+10221*w_(0,4)*z-12286*w_(0,5)*v-15247*w_(0,5)*u-5803*w_(0,5)*z-15601*v^2-15612*v*u-9085*v*z+13580*u^2+2256*u*z+2869*z^2,w_(0,0)*w_(0,5)-6095*w_(0,2)*u+3886*w_(0,2)*z+9877*w_(0,3)*v+1498*w_(0,3)*u+7566*w_(0,3)*z+793*w_(0,4)*v-13128*w_(0,4)*u+793*w_(0,4)*z-609*w_(0,5)*v+13572*w_(0,5)*u-689*w_(0,5)*z-2500*v^2+13405*v*u-15*v*z-15575*u^2-3850*u*z+1503*z^2,w_(0,4)^2+2493*w_(0,2)*u+2237*w_(0,2)*z+8396*w_(0,3)*v+9175*w_(0,3)*u-2784*w_(0,3)*z-5847*w_(0,4)*v+15793*w_(0,4)*u-6449*w_(0,4)*z-12370*w_(0,5)*v+11116*w_(0,5)*u-10951*w_(0,5)*z-15601*v^2-15612*v*u-9127*v*z+13580*u^2-333*u*z-7059*z^2,w_(0,3)*w_(0,4)-4890*w_(0,2)*u-6730*w_(0,2)*z-9898*w_(0,3)*v+898*w_(0,3)*u+4322*w_(0,3)*z-49*w_(0,4)*v+7144*w_(0,4)*u-4564*w_(0,4)*z+3060*w_(0,5)*v-6580*w_(0,5)*u+13591*w_(0,5)*z+1606*v^2+12857*v*u+6897*v*z-2759*u^2+15411*u*z+11748*z^2,w_(0,2)*w_(0,4)-6095*w_(0,2)*u-7125*w_(0,2)*z+5427*w_(0,3)*v-7483*w_(0,3)*u+11208*w_(0,3)*z-832*w_(0,4)*v+13346*w_(0,4)*u-728*w_(0,4)*z-609*w_(0,5)*v-14065*w_(0,5)*u-2901*w_(0,5)*z-2500*v^2+13405*v*u+10619*v*z-15575*u^2-12972*u*z-7801*z^2,w_(0,1)*w_(0,4)-10213*w_(0,2)*z-4503*w_(0,3)*v-13981*w_(0,3)*u+8262*w_(0,3)*z+3927*w_(0,4)*v+1973*w_(0,4)*u+3915*w_(0,4)*z-w_(0,5)*v+4503*w_(0,5)*u+1397*w_(0,5)*z-15984*v*z+2266*u*z-8730*z^2,w_(0,0)*w_(0,4)+8104*w_(0,2)*z-9352*w_(0,3)*v+9787*w_(0,3)*u+10502*w_(0,3)*z+6428*w_(0,4)*v-4023*w_(0,4)*u+6429*w_(0,4)*z+9351*w_(0,5)*u+7523*w_(0,5)*z-2885*v*z+635*u*z+13251*z^2,w_(0,3)^2-15809*w_(0,2)*u+8153*w_(0,2)*z+1149*w_(0,3)*v-15556*w_(0,3)*u+7803*w_(0,3)*z+655*w_(0,4)*v-2143*w_(0,4)*u+1860*w_(0,4)*z-14976*w_(0,5)*v+11885*w_(0,5)*u+9441*w_(0,5)*z-7036*v^2+5335*v*u+6413*v*z-2573*u^2-4217*u*z-12654*z^2,w_(0,2)*w_(0,3)-6641*w_(0,2)*u-14611*w_(0,2)*z+14*w_(0,3)*v+1591*w_(0,3)*u-5001*w_(0,3)*z+15957*w_(0,4)*v-12599*w_(0,4)*u-15372*w_(0,4)*z+12325*w_(0,5)*v+11851*w_(0,5)*u+4957*w_(0,5)*z-13598*v^2-14767*v*u+6290*v*z-13305*u^2+143*u*z+1580*z^2,w_(0,1)*w_(0,3)-6095*w_(0,2)*u-2059*w_(0,2)*z-1342*w_(0,3)*v-7379*w_(0,3)*u+15137*w_(0,3)*z+15278*w_(0,4)*v+4640*w_(0,4)*u+15219*w_(0,4)*z-621*w_(0,5)*v-7296*w_(0,5)*u-595*w_(0,5)*z-2500*v^2+13405*v*u-11119*v*z-15575*u^2+5992*u*z-279*z^2,w_(0,0)*w_(0,3)+13692*w_(0,2)*z+12596*w_(0,3)*v-8944*w_(0,3)*u-8640*w_(0,3)*z-14280*w_(0,4)*v+8346*w_(0,4)*u-14280*w_(0,4)*z-w_(0,5)*v-12608*w_(0,5)*u+7702*w_(0,5)*z+1250*v*z-4992*u*z-5323*z^2,w_(0,2)^2-14163*w_(0,2)*z+158*w_(0,3)*v-8233*w_(0,3)*u+15729*w_(0,3)*z+6253*w_(0,4)*v-10485*w_(0,4)*u+6239*w_(0,4)*z-w_(0,5)*v-158*w_(0,5)*u-8843*w_(0,5)*z+1045*v*z-3690*u*z+5332*z^2,w_(0,1)*w_(0,2)-8191*w_(0,2)*z+12588*w_(0,3)*v-651*w_(0,3)*u-12564*w_(0,3)*z+9610*w_(0,4)*v+6435*w_(0,4)*u+9611*w_(0,4)*z-12589*w_(0,5)*u-6630*w_(0,5)*z-6870*v*z-15774*u*z-12316*z^2,w_(0,0)*w_(0,2)-4739*w_(0,2)*z-15164*w_(0,3)*v+4760*w_(0,3)*u-239*w_(0,3)*z-14811*w_(0,4)*v+542*w_(0,4)*u-14811*w_(0,4)*z+15164*w_(0,5)*u-13325*w_(0,5)*z+1455*v*z+13761*u*z+12173*z^2,w_(0,1)^2-4739*w_(0,2)*z-15164*w_(0,3)*v+4760*w_(0,3)*u-239*w_(0,3)*z-14811*w_(0,4)*v+542*w_(0,4)*u-14811*w_(0,4)*z+15164*w_(0,5)*u-13325*w_(0,5)*z+1455*v*z+13761*u*z+12173*z^2,w_(0,0)*w_(0,1)-6943*w_(0,2)*z-5602*w_(0,3)*v-2449*w_(0,3)*u+10613*w_(0,3)*z+5667*w_(0,4)*v-12093*w_(0,4)*u+5667*w_(0,4)*z+5602*w_(0,5)*u-14178*w_(0,5)*z-2684*v*z+13663*u*z+4824*z^2,w_(0,0)^2-w_(0,2)*u+12473*w_(0,2)*z+6841*w_(0,3)*v-4867*w_(0,3)*u-4785*w_(0,3)*z-13219*w_(0,4)*v-4192*w_(0,4)*u-13219*w_(0,4)*z-6841*w_(0,5)*u-15405*w_(0,5)*z-6746*v*z-10445*u*z+13918*z^2,u^3-u*z^2,v*u^2-v*z^2+u^2*z-z^3,6000*w_(0,3)*v*z+9917*w_(0,3)*u*z+6000*w_(0,3)*z^2+14765*w_(0,4)*v^2-14900*w_(0,4)*v*u-2473*w_(0,4)*v*z-655*w_(0,4)*u^2+3360*w_(0,4)*u*z+14765*w_(0,4)*z^2-9141*w_(0,5)*v^2-12538*w_(0,5)*v*u+5929*w_(0,5)*v*z+1645*w_(0,5)*u^2+3268*w_(0,5)*u*z+15070*w_(0,5)*z^2+3535*v^3-3543*v^2*u+6807*v^2*z-14272*v*u^2-3289*v*u*z-9652*v*z^2+5630*u^3+15772*u^2*z-7022*u*z^2-12924*z^3,-1940*w_(0,3)*v*z+10021*w_(0,3)*u*z-1940*w_(0,3)*z^2+1510*w_(0,4)*v^2-7484*w_(0,4)*v*u+3019*w_(0,4)*v*z+5072*w_(0,4)*u^2-1180*w_(0,4)*u*z+1509*w_(0,4)*z^2+7936*w_(0,5)*v^2+3897*w_(0,5)*v*u+4643*w_(0,5)*v*z-9145*w_(0,5)*u^2-1746*w_(0,5)*u*z-3293*w_(0,5)*z^2-15191*v^3+12068*v^2*u+2749*v^2*z-5858*v*u^2-13155*v*u*z+4612*v*z^2+8077*u^3+7426*u^2*z-2400*u*z^2-13328*z^3,-4194*w_(0,3)*v*z-7759*w_(0,3)*u*z-4194*w_(0,3)*z^2+424*w_(0,4)*v^2-9462*w_(0,4)*v*u+860*w_(0,4)*v*z-2108*w_(0,4)*u^2+15086*w_(0,4)*u*z+436*w_(0,4)*z^2+5371*w_(0,5)*v^2-1192*w_(0,5)*v*u+11051*w_(0,5)*v*z-7484*w_(0,5)*u^2+4012*w_(0,5)*u*z+5680*w_(0,5)*z^2+11583*v^3+15934*v^2*u-10306*v^2*z+556*v*u^2+3353*v*u*z-15662*v*z^2+10530*u^3+13222*u^2*z+7884*u*z^2+6227*z^3)
numgens J0
codim J0
numgens R0
time rad J0 -- very quick
time decompose J0

restart
load "../MinimalPrimes/radical.m2"
loadPackage "PrimaryDecomposition"
debug PrimaryDecomposition
kk = ZZ/32003 -- from Greuel-Laplagne-Seelisch arXiv:0904.3561v1
S = kk[x,y]
I = ideal"55x8+66y2x9+837x2y6-75y4x2-70y6-97y7x2"
J = ideal jacobian I
rad1 = time rad J
rad2 = time intersect decompose J
rad1 == rad2 -- NO!!  So probably rad has a bug?
rad J == intersect decompose J
(gens J) % rad2
-- I think that rad2 might not be correct?
Slex = kk[x,y,MonomialOrder=>{1,1}]
J1 = sub(J,Slex)
rad1 = sub(rad1,Slex)
rad2 = sub(rad2,Slex)
see ideal gens gb J1
see ideal gens gb rad1
see ideal gens gb rad2

F0 = (ideal selectInSubring(1,gens gb J1))_0
F1 = (ideal selectInSubring(1,gens gb rad1))_0
F2 = (ideal selectInSubring(1,gens gb rad2))_0
saturate(J1,rad1)
saturate(J1,rad2)
decompose rad1
netList (oo/(i -> gens gb i))
decompose rad2
netList (oo/(i -> gens gb i))

rad3 = J : det jacobian J
rad3 == intersect decompose rad3
rad3 == rad1
(gens rad1) % rad2
(gens rad2) % rad1
degree rad1
degree rad2
rad1 : rad2
rad2 : rad1
decompose J
netList oo

(decompose rad1)/(i -> ideal gens gb i)
netList oo
(decompose rad2)/(i -> ideal gens gb i)
netList oo
rad1 == intersect decompose rad1
rad2 == intersect decompose rad2

---------------------------------------------------
-- New tests as of 6/10/2010

restart
load "../MinimalPrimes/radical.m2"


R = ZZ/32003[b,s,t,u,v,w,x,y,z]
I = ideal(
    b*v+s*u,
    b*w+t*u,
    s*w+t*v,
    b*y+s*x,
    b*z+t*x,
    s*z+t*y,
    u*y+v*x,
    u*z+w*x,
    v*z+w*y)
codim I
U = first independentSets I
H = flatt2(I,U)
peek H
F = (intersect values H)_0
C1 = saturate(I,F)
I : C1
