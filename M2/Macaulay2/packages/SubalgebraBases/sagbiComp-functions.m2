-- initializesagbiComputation: produces a SAGBIComputation
--   a mutable version of a SAGBIBasis object, to be used for sagbi computation 
-- This function should be called at the beginning of sagbi computation
-- the options for the sagbiComputation are taken from SAGBIBasis except 
--   if RenewOptions is true then only the specified options are used
initializeSagbiComputation = method();
initializeSagbiComputation (SAGBIBasis, HashTable):= (S, opts) -> (
    rings := new MutableHashTable from S#SAGBIrings;
    maps := new MutableHashTable from S#SAGBImaps;
    ideals := new MutableHashTable from S#SAGBIideals;
    data := new MutableHashTable from S#SAGBIdata;
    pending := new MutableHashTable from applyValues(S#SAGBIpending, l -> new MutableList from l);
    optionTable := new MutableHashTable from (
	if opts.RenewOptions then opts else S#SAGBIoptions
	);
    
    data#"limit" = opts.Limit;
    optionTable#PrintLevel = opts.PrintLevel;
    optionTable#RenewOptions = false;
    optionTable#Recompute = false;
    --apply(keys pending, i -> pending#i = new MutableList from pending#i);

    new SAGBIComputation from {
        SAGBIrings => rings,
        SAGBImaps => maps,
        SAGBIideals => ideals,
        SAGBIdata => data,
        SAGBIpending => pending,
        SAGBIoptions => optionTable
    }
)

-- limitedSagbiComputation: construct a small sagbiComputation with enough data for use in autoSubduction
limitedSagbiComputation = method();
limitedSagbiComputation (SAGBIComputation, Matrix) := (sagbiComputation, M) -> (
    -- Construct the monoid of a ring with variables corresponding
    --    to generators of the ambient ring and the subalgebra.
    -- Has an elimination order that eliminates the generators of the ambient ring.
    -- The degrees of generators are set so that the SyzygyIdeal is homogeneous.
    numberVariables := numgens sagbiComputation#SAGBIrings#"liftedRing";
    numberGenerators := numColumns M;
    newMonomialOrder := append((monoid sagbiComputation#SAGBIrings#"liftedRing").Options.MonomialOrder,
    		     Eliminate numberVariables);
    tensorVariables := monoid[
        Variables => numberVariables + numberGenerators,
        Degrees => first entries (matrix{
		flatten degrees source vars sagbiComputation#SAGBIrings#"liftedRing"}|
		matrix{flatten degrees source M}),
        MonomialOrder => newMonomialOrder];
    tensorRing := (coefficientRing sagbiComputation#SAGBIrings#"liftedRing") tensorVariables;
    rings := new MutableHashTable from {
        quotientRing => sagbiComputation#SAGBIrings.quotientRing,
        "liftedRing" => sagbiComputation#SAGBIrings#"liftedRing",
        global tensorRing => tensorRing
    };

    -- Maps:
    inclusionLifted := map(rings.tensorRing,rings#"liftedRing",
    		    (vars rings.tensorRing)_{0..numberVariables-1});
    substitution := map(rings.tensorRing,rings.tensorRing,
    		    (vars rings.tensorRing)_{0..numberVariables-1} | inclusionLifted(M));
    projectionLifted := map(rings#"liftedRing",rings.tensorRing,
    		    vars rings#"liftedRing" | matrix {toList(numberGenerators:0_(rings#"liftedRing"))});
    sagbiInclusion := map(rings.tensorRing,rings.tensorRing,
    		    matrix {toList (numberVariables:0_(rings.tensorRing))} |
		    (vars rings.tensorRing)_{numberVariables .. numberVariables + numberGenerators - 1});

    maps := new MutableHashTable from {
        "inclusionLifted" => inclusionLifted,
        "projectionLifted" => projectionLifted,
        "sagbiInclusion" => sagbiInclusion,
        "substitution" => substitution,
        "fullSubstitution" => projectionLifted * substitution,
        "quotient" => sagbiComputation#SAGBImaps#"quotient"
    };
    
    -- Ideals:
    generatingVariables := (vars rings.tensorRing)_{numberVariables..numberVariables + numberGenerators - 1};
    SIdeal := ideal(generatingVariables - maps#"inclusionLifted"(leadTerm M));
    ideals := new MutableHashTable from {
        "I" => sagbiComputation#SAGBIideals#"I",
        "SIdeal" => SIdeal,
        "leadTermsI" => sagbiComputation#SAGBIideals#"leadTermsI",
        "reductionIdeal" => maps#"inclusionLifted" sagbiComputation#SAGBIideals#"leadTermsI" + SIdeal
    };
    optionTable := new MutableHashTable from sagbiComputation#SAGBIoptions;
    data := null;
    pending := null;
    new SAGBIComputation from {
        SAGBIrings => rings,
        SAGBImaps => maps,
        SAGBIideals => ideals,
        SAGBIdata => data,
        SAGBIpending => pending,
        SAGBIoptions => optionTable
    }
)


-- compSubduction is an internal (unexported) version of subduction for use in sagbi
-- the user-friendly version is subduction
-- compSubduction takes a sagbiComputation and 1-row matrix M
--     with entries in the quotientRing and subducts the elements of M against sagbiComputation

compSubduction = method( 
    TypicalValue => HashTable,
    Options => {
	AutoSubduce => true,
        ReduceNewGenerators => true,
	StorePending => true,
        Strategy => "Master", -- Master (default), DegreeByDegree, Incremental
        SubductionMethod => "Top", -- Top or Engine
    	Limit => 20,
	AutoSubduceOnPartialCompletion => false,
    	PrintLevel => 0,
	Recompute => false,
	RenewOptions => false
    	}
    );

compSubduction(SAGBIComputation, MutableMatrix) := opts -> (sagbiComputation, M) -> (
    new MutableMatrix from compSubduction(sagbiComputation, matrix M)
    )

compSubduction(SAGBIComputation, Matrix) := opts -> (sagbiComputation, M) -> (
    if sagbiComputation#SAGBIoptions#PrintLevel > 3 then (    
	print("-- subduction input:");
	print(M);
	);    
    if zero(M) then return M;
    result := matrix {toList(numcols(M):0_(sagbiComputation#SAGBIrings#"liftedRing"))};
    liftedM := matrix {
	for m in first entries M list sub(m, sagbiComputation#SAGBIrings#"liftedRing")
	};
    if sagbiComputation#SAGBIoptions#PrintLevel > 5 then (
	print("-- [compSubduction] elements to subduct:");
	print(transpose liftedM);
	);
    local subductedPart;
    local leadTermSubductedPart;
    while not (zero(liftedM)) do (
	if sagbiComputation#SAGBIoptions#SubductionMethod == "Top" then (
            subductedPart = subductionTopLevelLeadTerm(sagbiComputation, liftedM);
	    ) 
	else if sagbiComputation#SAGBIoptions#SubductionMethod == "Engine" then (
    	    subductedPart = subductionEngineLevelLeadTerm(sagbiComputation, liftedM);
	    ) 
	else (
	    error ("unknown SubductionMethod " | toString sagbiComputation#SAGBIoptions#SubductionMethod | ", expected \"Top\" or \"Engine\"\nThe next time 'sagbi' or 'subalgebraBases' is used on the same input, run it with the option: 'RenewOptions => true'"); 
	    );
	leadTermSubductedPart = leadTerm subductedPart;
	result = result + leadTermSubductedPart;
	liftedM = (subductedPart - leadTermSubductedPart) % sagbiComputation#SAGBIideals#"I";
	
	if sagbiComputation#SAGBIoptions#PrintLevel > 5 then (
	    print("-- [compSubduction] result so far:");
	    print(transpose result);
	    print("-- [compSubduction] remaining to subduct:");
	    print(transpose liftedM);
	    );
	);
    result = result % sagbiComputation#SAGBIideals#"I";
    
    if sagbiComputation#SAGBIoptions#PrintLevel > 3 then (    
	print("-- subduction result using "| sagbiComputation#SAGBIoptions#SubductionMethod |" strategy:");
	print(result);
	);
    result
    )


-- subductionTopLevelLeadTerm: expects the matrix M to have entries in liftedRing
-- performs subduction only until the lead term cannot be subducted further
-- NB this method assumes M is reduced mod I
subductionTopLevelLeadTerm = method();
subductionTopLevelLeadTerm (SAGBIComputation, Matrix) := (sagbiComputation, M) -> (
    liftg := M;
    while not (zero liftg) do ( 
        tensorRingLiftg := sagbiComputation#SAGBImaps#"inclusionLifted" liftg;
	tensorRingLeadTermg := leadTerm tensorRingLiftg;
	h := tensorRingLeadTermg % (sagbiComputation#SAGBIideals#"reductionIdeal"); -- do partial % based on sagbiComputation option
	projectionh := sagbiComputation#SAGBImaps#"fullSubstitution" sagbiComputation#SAGBImaps#"sagbiInclusion" h;

    	if sagbiComputation#SAGBIoptions#PrintLevel > 6 then (
	    print("-- [subductionTopLevelLeadTerm] --");
	    print("-- lift g:");
	    print(transpose liftg);
	    print("-- tensorRingLiftg:");
	    print(transpose tensorRingLiftg);
	    print("-- tensorRingLeadTermg:");
	    print(transpose tensorRingLeadTermg);
	    print("-- h:");
	    print(transpose h);
	    print("-- projectionh:");
	    print(transpose projectionh);
	    );
		
	-- exit the loop if h does not lie in K[p_1 .. p_r] <- the variables tagging the generators of S
	-- note that h is a monomial, if it is divisible by some x_i (from the lifted ring) then projectionh is zero
	--
	if zero(projectionh) then break;

	-- if I is nonzero then reduce projectionh modulo I:
	if not zero sagbiComputation#SAGBIideals#"I" then (projectionh = projectionh % sagbiComputation#SAGBIideals#"I"); 
 	
	--update g
	liftg = liftg - projectionh;
	);
    
    -- check if g is zero or has degree zero 
    matrix {apply(
	    first entries liftg,
	    i -> 
	    if (not (i == 0_(sagbiComputation#SAGBIrings#"liftedRing"))) and (degree(i))_0 == 0 then (
		0_(sagbiComputation#SAGBIrings#"liftedRing")
		) 
	    else (
		i
		)
	    )}
    );

-- Engine Subduction of the lead term
-- perform the same function as subductionTopLevelLeadTerm except
-- with engine-level code.
subductionEngineLevelLeadTerm = method();
subductionEngineLevelLeadTerm(SAGBIComputation, RingElement) := (sagbiComputation, g) -> (
    (subductionEngineLevelLeadTerm(sagbiComputation, matrix {{g}}))_(0,0) 
    );

subductionEngineLevelLeadTerm(SAGBIComputation, Matrix) := (sagbiComputation, M) -> (
    local result;
    tense := sagbiComputation#SAGBIrings.tensorRing;
    	    
    ambR := source sagbiComputation#SAGBImaps#"inclusionLifted";
    if ring M === tense then (
	M = (sagbiComputation#SAGBImaps#"fullSubstitution")(M);
	) 
    else if ring M =!= ambR then (
	error "M must be from ambR or tensorRing.";
	);
    -- It is possible for ring f === ambient to be true but f is still from a different ring
    -- than pres.tensorRing. In this case, it shouldn't try to prevent an error by using "sub"
    -- or something. Instead, the following line will deliberately throw an error:
    -- (This is done because otherwise there is potential for a segfault.)
    throwError := M_(0,0) - 1_(ambR);
    -- Use the same pres ring as much as possible.
    -- M2 will automatically cache the gb calculation
    -- as long as the pres ring is not reconstructed.
    gbI := gb sagbiComputation#SAGBIideals#"I";
    gbReductionIdeal := gb sagbiComputation#SAGBIideals#"reductionIdeal";
    F := sagbiComputation#SAGBImaps#"substitution";
    N := monoid ambR;
    numblocks := rawMonoidNumberOfBlocks raw N;
    result = rawSubduction1(numblocks, raw tense, raw ambR, raw M, raw sagbiComputation#SAGBImaps#"inclusionLifted", raw sagbiComputation#SAGBImaps#"fullSubstitution", raw (sagbiComputation#SAGBImaps#"substitution" * sagbiComputation#SAGBImaps#"sagbiInclusion"), raw gbI, raw gbReductionIdeal);
    result = matrix{apply(first entries result,i->promote(i,ambR))}
    );

---------------
-- AutoSubduce: (sagbiComputation)
---------------
-- for each subalgebraGenerator subduct it against the rest of the subalgebraGenerators
-- for each such generator we produce a temporary sagbiComputation object that contains
-- enough data to perform subduction with
--

autosubduce = method();
autosubduce SAGBIComputation := sagbiComputation -> (
    
    local tempSagbiComputation;
    local M;
    generatorMatrix := new MutableMatrix from sagbiComputation#SAGBIdata#"subalgebraGenerators";
    for i from 0 to (numColumns generatorMatrix) - 1 do (
            M = new Matrix from generatorMatrix_(toList join(0..(i-1),(i+1)..((numColumns generatorMatrix)-1)));
            tempSagbiComputation = limitedSagbiComputation(sagbiComputation,lift(M,sagbiComputation#SAGBIrings#"liftedRing"));
	    generatorMatrix_(0,i) = (compSubduction(tempSagbiComputation,generatorMatrix_{i}))_(0,0);
            if not generatorMatrix_(0,i) == 0 then
                generatorMatrix_(0,i) = generatorMatrix_(0,i)*(1/leadCoefficient(generatorMatrix_(0,i)));
    );
    compress new Matrix from generatorMatrix
)

---------------------------------
-- AutoSubduceSagbi: (sagbiComputation)
---------------------------------
-- for each sagbiGenerator subduct it against the rest of the sagbiGenerators
-- for each such generator we produce a temporary sagbiComputation object that contains
-- enough data to perform subduction with

autosubduceSagbi = method();
autosubduceSagbi SAGBIComputation := sagbiComputation -> (
    
    if sagbiComputation#SAGBIoptions#PrintLevel > 0 then (
	print("-- AutoSubducting Sagbi Generators ...");
	);	
    
    local tempsagbiComputation;
    local M;
    generatorMatrix := new MutableMatrix from sagbiComputation#SAGBImaps#"quotient" sagbiComputation#SAGBIdata#"sagbiGenerators";
    for i from 0 to (numColumns generatorMatrix) - 1 do (
            M = new Matrix from generatorMatrix_(toList join(0..(i-1),(i+1)..((numColumns generatorMatrix)-1)));
            tempsagbiComputation = limitedSagbiComputation(sagbiComputation,lift(M,sagbiComputation#SAGBIrings#"liftedRing"));
	    generatorMatrix_(0,i) = (compSubduction(tempsagbiComputation,generatorMatrix_{i}))_(0,0);
            if not generatorMatrix_(0,i) == 0 then
                generatorMatrix_(0,i) = generatorMatrix_(0,i)*(1/leadCoefficient(generatorMatrix_(0,i)));
    );
    compress new Matrix from generatorMatrix
)


-- updateComputation: checks the Strategy: DegreeByDegree or Incremental.
--   passes to a function that recomputed the rings, maps and ideals wrt new sagbiGenerators
-- NB if there are no new sagbiGenerators, then this function is not called

updateComputation = method();
updateComputation SAGBIComputation := sagbiComputation -> (
    if sagbiComputation#SAGBIoptions#Strategy == "Master" then (
	updateComputationMaster(sagbiComputation);
	) 
    else if sagbiComputation#SAGBIoptions#Strategy == "DegreeByDegree" then (
	updateComputationDegreeByDegree(sagbiComputation);
	) 
    else if sagbiComputation#SAGBIoptions#Strategy == "Incremental" then (
	updateComputationIncremental(sagbiComputation);
	) 
    else (
	error("unknown Strategy, expected \"Master\", \"DegreeByDegree\", or \"Incremental\"\nThe next time 'sagbi' or 'subalgebraBases' is used on the same input, run it with the option: 'RenewOptions => true'");
	);
    )


-- updateComputationMaster: Master Strategy for computation updates
-- We use the heuristic that sagbiGenerators are generally clumped together
-- at low degree and become sparser at higher degrees
--
-- So, we check the number of sagbiGenerators that were added last time
-- during the last loop of sagbi algorithm
-- if 0 or 1 sagbiGenerators were added and the degree of the last added generator > 5, then use Incremental
-- otherwise use DegreeByDegree

updateComputationMaster = method();
updateComputationMaster SAGBIComputation := sagbiComputation -> (
    
    if (sagbiComputation#SAGBIdata#?"numberOfNewGenerators") and (numColumns sagbiComputation#SAGBIdata#"sagbiGenerators" > 0) then (
	numNewGens := sagbiComputation#SAGBIdata#"numberOfNewGenerators";
	lastSagbiGenDegree := last first entries sagbiComputation#SAGBIdata#"sagbiDegrees";
	-- compare the number of new generators with the total number of generators
	-- e.g. if you're adding less than 2-3% of the total number of generators
	if (numNewGens == 0 or numNewGens == 1) and (lastSagbiGenDegree > 8) then (
	    if sagbiComputation#SAGBIoptions#PrintLevel > 4 then (
		print("-- [updateComputationMaster] Detected few new generators; using Incremental Strategy");
		);
	    updateComputationIncremental(sagbiComputation);
	    ) 
	else (
	    if sagbiComputation#SAGBIoptions#PrintLevel > 4 then (
		print("-- [updateComputationMaster] Detected many or low-degree new generators; using DegreeByDegree Strategy");
		);
	    updateComputationDegreeByDegree(sagbiComputation);
	    );
	 
	) 
    else (
	if sagbiComputation#SAGBIoptions#PrintLevel > 4 then (
	    print("-- [updateComputationMaster] Defaulting to DegreeByDegree Strategy");
	    );
	updateComputationDegreeByDegree(sagbiComputation);
	);
    );


-- updateComputation using DegreeByDegree strategy 
-- NB this does not compute a gb for the reductionIdeal 
-- The gb computation next occurs in collectSPairs or during subduction
-- The gb computation is only necessary up to a certain degree

updateComputationDegreeByDegree = method();
updateComputationDegreeByDegree SAGBIComputation := sagbiComputation -> (
        
    sagbiGens := sagbiComputation#SAGBIdata#"sagbiGenerators";
    
    -- Changes to the rings:
    -- quotientRing (unchanged)
    -- liftedRing   (unchanged)
    -- tensorRing   (modified)
    liftedRing := sagbiComputation#SAGBIrings#"liftedRing";
    
    numberVariables := numgens sagbiComputation#SAGBIrings#"liftedRing";
    numberGenerators := numColumns sagbiGens;
    newMonomialOrder := append((monoid liftedRing).Options.MonomialOrder, Eliminate numberVariables);    
    tensorVariables := monoid[
        Variables => numberVariables + numberGenerators,
        Degrees => degrees source vars liftedRing | degrees source sagbiGens,
        MonomialOrder => newMonomialOrder];
    tensorRing := (coefficientRing liftedRing) tensorVariables;
    sagbiComputation#SAGBIrings.tensorRing = tensorRing;
    
    -- Changes to the maps:
    -- inclusionLifted  (modified)
    -- substitution     (modified)
    -- projectionLifted (modified)
    -- sagbiInclusion   (modified)
    -- fullSubstitution (modified)
    -- quotient         (unchanged)
    
    inclusionLifted := map(tensorRing, liftedRing, (vars tensorRing)_{0..numberVariables-1});
    substitution := map(tensorRing, tensorRing , (vars tensorRing)_{0..numberVariables-1} | inclusionLifted(sub(sagbiGens, liftedRing)));
    projectionLifted := map(liftedRing, tensorRing, vars liftedRing | matrix {toList(numberGenerators:0_(liftedRing))});
    sagbiInclusion := map(tensorRing, tensorRing, matrix {toList (numberVariables:0_(tensorRing))} | (vars tensorRing)_{numberVariables .. numberVariables + numberGenerators - 1});
    
    sagbiComputation#SAGBImaps#"inclusionLifted"  = inclusionLifted;
    sagbiComputation#SAGBImaps#"substitution"     = substitution;
    sagbiComputation#SAGBImaps#"projectionLifted" = projectionLifted;
    sagbiComputation#SAGBImaps#"sagbiInclusion"   = sagbiInclusion;
    sagbiComputation#SAGBImaps#"fullSubstitution" = projectionLifted * substitution,
    
    -- Changes to the ideals:
    -- I              (unchanged)
    -- SIdeal         (modified)
    -- leadTermsI     (unchanged)
    -- reductionIdeal (modified)
    
    generatingVariables := (vars tensorRing)_{numberVariables..numberVariables + numberGenerators - 1};
    SIdeal := ideal(generatingVariables - inclusionLifted(sub(leadTerm sagbiGens, liftedRing)));
    sagbiComputation#SAGBIideals#"SIdeal" = SIdeal;
    sagbiComputation#SAGBIideals#"reductionIdeal" = inclusionLifted sagbiComputation#SAGBIideals#"leadTermsI" + SIdeal;    
    );

----------------------------------------------------------
-- updateComputation by using the incremental strategy
--
-- This method computes a full GB for the reductionIdeal by
-- using a (potentially previously computed) GB. This is done
-- by computing a GB in for the following ideal:
--   J = ideal (newTagVariables - newSagbiGenerators) 
-- which lives in the quotient ring:
--   oldTensorRing / oldReductionIdeal
-- Note this GB computation is faster than computing a GB for the new reductionIdeal
-- because we already have a GB for the oldReductionIdeal. 

updateComputationIncremental = method();
updateComputationIncremental SAGBIComputation := sagbiComputation -> (
    sagbiGens := sagbiComputation#SAGBIdata#"sagbiGenerators";
    
    -- Changes to the rings:
    -- quotientRing (unchanged)
    -- liftedRing   (unchanged)
    -- tensorRing   (modified)
    liftedRing := sagbiComputation#SAGBIrings#"liftedRing";
    
    numberVariables := numgens sagbiComputation#SAGBIrings#"liftedRing";
    numberGenerators := numColumns sagbiGens;
    newMonomialOrder := append((monoid liftedRing).Options.MonomialOrder, Eliminate numberVariables);    
    tensorVariables := monoid[
        Variables => numberVariables + numberGenerators,
        Degrees => degrees source vars liftedRing | degrees source sagbiGens,
        MonomialOrder => newMonomialOrder];
    tensorRing := (coefficientRing liftedRing) tensorVariables;
    oldTensorRing := sagbiComputation#SAGBIrings.tensorRing;
    
    -- Changes to the maps:
    -- inclusionLifted  (modified)
    -- substitution     (modified)
    -- projectionLifted (modified)
    -- sagbiInclusion   (modified)
    -- fullSubstitution (modified)
    -- quotient         (unchanged)
    
    inclusionLifted := map(tensorRing, liftedRing, (vars tensorRing)_{0..numberVariables-1});
    substitution := map(tensorRing, tensorRing , (vars tensorRing)_{0..numberVariables-1} | inclusionLifted(sub(sagbiGens, liftedRing)));
    projectionLifted := map(liftedRing, tensorRing, vars liftedRing | matrix {toList(numberGenerators:0_(liftedRing))});
    sagbiInclusion := map(tensorRing, tensorRing, matrix {toList (numberVariables:0_(tensorRing))} | (vars tensorRing)_{numberVariables .. numberVariables + numberGenerators - 1});
       
    -- Changes to the ideals:
    -- I              (unchanged)
    -- SIdeal         (modified)
    -- leadTermsI     (unchanged)
    -- reductionIdeal (modified)
    
    -- Incremental steps to form reductionIdeal and compute a GB:
    -- 1) Write down new sagbi gens, construct new tensor ring [done above] and inclusion map.
    -- 2) Map the old gb into new tensor ring and promise it’s a gb (forceGB)
    -- 3) Construct the ideal, quotient ring, and the quotient map
    -- 4) Apply the quotient map to the new generators, compute a gb, and lift
    -- 5) Concatenate the lifted elements with the old gb generators and promise that’s a gb (forceGB)
    
    -- (1)    
    numberOfNewGenerators := (numgens tensorRing) - (numgens oldTensorRing);
    generatingVariables := (vars tensorRing)_{numberVariables + numberGenerators - numberOfNewGenerators ..numberVariables + numberGenerators - 1};
    newSagbiGens := sagbiGens_{numberGenerators - numberOfNewGenerators .. numberGenerators - 1};
    newSIdealGens := generatingVariables - inclusionLifted(sub(leadTerm newSagbiGens, liftedRing));    
    tensorRingInclusion := map(tensorRing, oldTensorRing, (vars tensorRing)_{0 .. numberVariables + numberGenerators - numberOfNewGenerators - 1});
    
    -- (2)
    oldReductionIdealGB := tensorRingInclusion gens gb sagbiComputation#SAGBIideals#"reductionIdeal";
    forceGB oldReductionIdealGB;
    
    -- (3) 
    tensorRingQuotientOldReduction := tensorRing / (ideal oldReductionIdealGB);
    quotientMapOldReduction := map(tensorRingQuotientOldReduction, tensorRing, vars tensorRingQuotientOldReduction);
    
    -- (4)
    quotientReductionGB := lift(gens gb quotientMapOldReduction newSIdealGens, tensorRing);
    
    -- (5)
    newReductionGB := oldReductionIdealGB | quotientReductionGB;    
    forceGB newReductionGB;
    
    
    -- Update the sagbiComputation:
    sagbiComputation#SAGBIrings.tensorRing = tensorRing;            
    sagbiComputation#SAGBImaps#"inclusionLifted"  = inclusionLifted;
    sagbiComputation#SAGBImaps#"substitution"     = substitution;
    sagbiComputation#SAGBImaps#"projectionLifted" = projectionLifted;
    sagbiComputation#SAGBImaps#"sagbiInclusion"   = sagbiInclusion;
    sagbiComputation#SAGBImaps#"fullSubstitution" = projectionLifted * substitution,
    sagbiComputation#SAGBIideals#"SIdeal" = ideal newSIdealGens;
    sagbiComputation#SAGBIideals#"reductionIdeal" = ideal newReductionGB;    
    );


-- Finds the lowest list in Pending
lowestDegree = method()
lowestDegree SAGBIComputation := sagbiComputation -> (
    min keys sagbiComputation#SAGBIpending
)

-- Adds newGens to sagbiComputation#SAGBIdata#"sagbiGenerators" 
--   newGens is a 1-row matrix of generators to be added
-- updates the sagbiDegrees with the degrees of the generators added
-- saves the number of sagbiGenerators that were just added
--
appendToBasis = method()
appendToBasis (SAGBIComputation, Matrix) := (sagbiComputation, newGenerators) -> (
    sagbiComputation#SAGBIdata#"sagbiDegrees" = sagbiComputation#SAGBIdata#"sagbiDegrees" | matrix{flatten degrees source newGenerators};
    sagbiComputation#SAGBIdata#"sagbiGenerators" = sagbiComputation#SAGBIdata#"sagbiGenerators" | newGenerators;
    sagbiComputation#SAGBIdata#"numberOfNewGenerators" = numColumns newGenerators;
)

--------------------------------------------------
-- Process Pending: (sagbiComputation) -> currentDegree
--------------------------------------------------
-- 1) Reduces the elements of lowest degree in the pending list (triangularBasis)
-- 2) Adds these elements to the SAGBI basis (insertPending)
-- 3) Updates all the maps, rings, and ideals (updateComputation)
-- NB Assumes that the pending list has been subducted 
-- 
-- returns the lowest degree of a new sagbiGenerator added
--
          
processPending = method();
processPending SAGBIComputation := sagbiComputation -> (
    local reducedGenerators; 
    currentLowest := lowestDegree(sagbiComputation);
    if currentLowest < infinity then (
	if sagbiComputation#SAGBIoptions#PrintLevel > 4 then (
	    print("-- [processPending] generators before reduction:");
	    print(transpose matrix{toList sagbiComputation#SAGBIpending#currentLowest});
	    );
	if sagbiComputation#SAGBIoptions#ReduceNewGenerators then ( --perform gaussian elimination on the new generators
	    reducedGenerators = triangularBasis matrix{toList sagbiComputation#SAGBIpending#currentLowest};
	    reducedGenerators = matrix {select((entries reducedGenerators)_0, i->(degree i)_0>0)}; -- remove elements of degree zero
	    if sagbiComputation#SAGBIoptions#PrintLevel > 4 then (
	    	print("-- [process pending]: reduced generators:");
	    	print(transpose reducedGenerators);
	    	);
	    ) 
	else (
	    reducedGenerators = matrix{toList sagbiComputation#SAGBIpending#currentLowest};
	    );
	
	
	remove(sagbiComputation#SAGBIpending, currentLowest);
        insertPending(sagbiComputation, reducedGenerators);

        currentLowest = lowestDegree(sagbiComputation);
        if currentLowest < infinity then (
	    
	    if sagbiComputation#SAGBIoptions#PrintLevel > 4 then (
		print("-- [processPending]: new sagbi generators being added:");
		print(transpose matrix{toList sagbiComputation#SAGBIpending#currentLowest});
		);    
	    
            appendToBasis(sagbiComputation, matrix{toList sagbiComputation#SAGBIpending#currentLowest});
            updateComputation(sagbiComputation);
            remove(sagbiComputation#SAGBIpending, currentLowest);
            );
    	);
    currentLowest
    )


-- Gaussian Elimination:
--
-- Takes a 1xn matrix M
-- Finds all the monomials contained in polynomials of M
-- Substitutes each monomial with a variable
-- Computes a gb for the ideal generated by these linear polynomials
-- Substitutes back and forms a matrix from the gb generators

triangularBasis = method();
triangularBasis(Matrix) := M -> (
    R := ring M;
    mons := monomials M;
    A := last coefficients(M,Monomials=>mons);
    S := (coefficientRing R) (monoid[Variables => (numcols mons)]);
    I := ideal(vars S * sub(A, S));
    reduced := last coefficients(gens gb I);
    compress (mons * sub(reduced,R))
    );


insertPending = method();
insertPending (SAGBIComputation, Matrix) := (sagbiComputation, candidates) -> (
    for candidate in first entries candidates do(
        -- get the entry of the column and its degree
        level := (degree candidate)_0;
        if sagbiComputation#SAGBIpending#?level then(
            sagbiComputation#SAGBIpending#level = append(sagbiComputation#SAGBIpending#level, candidate)
        ) 
    else (
	        sagbiComputation#SAGBIpending#level = new MutableList from {candidate}
	    );
    );
)

processFirstStep = method();
processFirstStep SAGBIComputation := sagbiComputation -> (
    if sagbiComputation#SAGBIoptions#AutoSubduce then (
        if sagbiComputation#SAGBIoptions#PrintLevel > 0 then
            print("-- Performing initial autosubduction...");
	sagbiComputation#SAGBIdata#"subalgebraGenerators" = autosubduce sagbiComputation;
    	sagbiComputation#SAGBIoptions#AutoSubduce = false; -- autosubduction may now be skipped if the computation is resumed
    );
    
    if (numcols sagbiComputation#SAGBIdata#"sagbiGenerators" == 0) then (
        liftedGenerators := lift(sagbiComputation#SAGBIdata#"subalgebraGenerators",sagbiComputation#SAGBIrings#"liftedRing");
        insertPending(sagbiComputation, liftedGenerators);
        -- Remove elements of the underlying field
        remove(sagbiComputation#SAGBIpending, 0);
        sagbiComputation#SAGBIdata#degree = processPending(sagbiComputation) + 1;
    );
)

--Accepts a 1-row matrix inputMatrix and returns a matrix of columns 
-- of inputMatrix where the highest degree entry has total degree equal to selectedDegree
submatrixByDegree = method()
submatrixByDegree (Matrix,ZZ) := (inputMatrix, selectedDegree) -> (
    matrixDegrees := degrees source inputMatrix;
    selectedEntries := positions(matrixDegrees, d -> d === {selectedDegree});
    inputMatrix_selectedEntries
)

collectSPairs = method();
collectSPairs SAGBIComputation := sagbiComputation -> (
    
    if sagbiComputation#SAGBIoptions#PrintLevel > 0 then (
	    print("---------------------------------------");
	    print("-- Current degree:"|toString(sagbiComputation#SAGBIdata#degree));
	    print("---------------------------------------");
	    print("-- Computing the tete-a-tete's...");
    );
    sagbiGB := gb(sagbiComputation#SAGBIideals#"reductionIdeal", DegreeLimit => sagbiComputation#SAGBIdata#degree);
    k := rawMonoidNumberOfBlocks(raw monoid (sagbiComputation#SAGBIrings.tensorRing)) - 2;
    zeroGens := submatrixByDegree(selectInSubring(k, gens sagbiGB), sagbiComputation#SAGBIdata#degree);
    SPairs := sagbiComputation#SAGBImaps#"fullSubstitution"(zeroGens) % sagbiComputation#SAGBIideals#"I";
    
    if sagbiComputation#SAGBIpending#?(sagbiComputation#SAGBIdata#degree) then (
        SPairs = SPairs | matrix{toList sagbiComputation#SAGBIpending#(sagbiComputation#SAGBIdata#degree)};
	remove(sagbiComputation#SAGBIpending, sagbiComputation#SAGBIdata#degree);
    );
    
    if sagbiComputation#SAGBIoptions#PrintLevel > 2 then ( -- extra information
	print("-- GB for reductionIdeal:");
	print(sagbiGB);
	print(gens sagbiGB);
	print("-- zeroGens:");
	print(zeroGens);
	);
    if sagbiComputation#SAGBIoptions#PrintLevel > 0 then (
	print("-- Num. S-polys before subduction: "| toString(numcols SPairs));
	);
    if sagbiComputation#SAGBIoptions#PrintLevel > 1 then (
	print("-- S-polys:");
	print(SPairs);
	);
        
    SPairs
)

-- sagbi -> updatePending -> insertPending/processPending
-- updatePending(sagbiComputation, Spairs)
-- Takes the already subducted SPairs and removes any 0's from the matrix
-- Returns true if new generators are added
--
updatePending = method();
updatePending (SAGBIComputation, Matrix) := (sagbiComputation, SPairs) -> (
    
    local newGens;
    local currentLowestDegree;
    addedGenerators := false;
    
    if numcols SPairs != 0 then (
	newGens = compress (SPairs);
	) 
    else (
	newGens = SPairs;
	);
    
    if sagbiComputation#SAGBIoptions#PrintLevel > 0 then(
	print("-- Num. S-polys after subduction: " | toString(numcols newGens));
	);
    
    if sagbiComputation#SAGBIoptions#PrintLevel > 1 then(
	print("-- New generators:");
	if (numcols newGens == 0) then(
	    -- It has to treat this as a special case because zero matrices are special.
	    print("| 0 |");
	    )else(
	    print(newGens);
	    );
    	);
    
    -- add the newGens to the pending list
    if numcols newGens > 0 then (
	insertPending(sagbiComputation, newGens);
	currentLowestDegree = processPending(sagbiComputation);
	if not currentLowestDegree == infinity then ( 
	    sagbiComputation#SAGBIdata#degree = currentLowestDegree;
	    );
	addedGenerators = true;
	sagbiComputation#SAGBIdata#"autoSubductedSagbiGenerators" = false; -- need to autoSubduct new generators (see sagbiComputation option: AutoSubductOnPartialCompletion)
	);
    
    addedGenerators
    )


--------------------------------
-- Check Termination
--------------------------------
-- check whether the sagbi computation should terminate
-- criteria for termination:
-- 0) the pending list is empty
--   - if not: an element of the pending list may be a new sagbiGenerator
-- 1) fully computed the GB for the reductionIdeal (always true for the Incremental strategy)
--   - if not: new elements of GB of the reductionIdeal may give new SPairs and new sagbiGenerators
-- 2) the degree of the computation > the maximum degree of sagbiGenerators
--   - if not: there was a drop in computation degree, so the computation degree needs to catch up
-- 3) the degree of the computation > the maximum degree of gb for reductionIdeal
--   - if not: it may be possible to get lower degree generators

-- if the computation should terminate then set sagbiComputation#SAGBIdata#"sagbiDone" to true
-- if the computation should not terminate then:
--   if AutoSubductOnPartialCompletion and (not autoSubductedSagbiGenerators) then:
--     autosubduceSagbi(sagbiComputation)


checkTermination = method();
checkTermination SAGBIComputation := (sagbiComputation) -> (
    
    local terminationCondition0;
    local terminationCondition1;
    local terminationCondition2;
    local terminationCondition3;
    
    -- NB sagbGB's gb should be computed in processPending -> updateComputation (for incremental) or collectSpairs (for DegreeByDegree)
    -- that computation depends on the option: "DegreeByDegree" or "Incremental" 
    sagbiGB := gb(sagbiComputation#SAGBIideals#"reductionIdeal", DegreeLimit => sagbiComputation#SAGBIdata#degree);
    terminationCondition0 = #(sagbiComputation#SAGBIpending) == 0;
    terminationCondition1 = rawStatus1 raw sagbiGB == 6; -- is the GB computation completed?
    
    -- check if there are still generators of higher degree to add to the sagbiGenerators
    terminationCondition2 = sagbiComputation#SAGBIdata#degree > max flatten (degrees sagbiComputation#SAGBIdata#"sagbiGenerators")_1;
    
    -- check to make sure it is not possible to get lower degree sagbiGenerators
    -- by taking them modulo the reductionIdeal
    terminationCondition3 = sagbiComputation#SAGBIdata#degree > max flatten (degrees gens sagbiGB)_1; 
    if sagbiComputation#SAGBIoptions#PrintLevel > 0 then(
	print("-- Stopping conditions:");
	print("--    No higher degree candidates: "|toString(terminationCondition0));
	print("--    S-poly ideal GB completed:   "|toString(terminationCondition1));
	print("--    Degree lower bound:          "|toString(terminationCondition2));
	print("--    Degree bound by sagbiGB:     "|toString(terminationCondition3));
	);
    
    if terminationCondition0 and terminationCondition1 and terminationCondition2 and terminationCondition3 then (
	sagbiComputation#SAGBIdata#"sagbiDone" = true;
	if sagbiComputation#SAGBIoptions#PrintLevel > 0 then (
	    print("-- Computation complete. Finite sagbi basis found!")
	    );
	) 
    else (
	if (sagbiComputation#SAGBIoptions#AutoSubduceOnPartialCompletion) and (not sagbiComputation#SAGBIdata#"autoSubductedSagbiGenerators") then (
	    -- apply autosubduction to the sagbiGenerators
	    sagbiComputation#SAGBIdata#"sagbiGenerators" = autosubduceSagbi(sagbiComputation);
	    sagbiComputation#SAGBIdata#"autoSubductedSagbiGenerators" = true;
	    ); 
	);        
    )


end --
