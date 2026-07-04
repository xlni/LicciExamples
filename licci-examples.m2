PartitionPair = new Type of HashTable

net(PartitionPair) := LM -> (
    return net {LM#"lambda", LM#"mu"}
    )

PartitionPair_ZZ := (LM,i) -> (
    if i == 0 then return LM#"lambda";
    if i == 1 then return LM#"mu";
    error "index for PartitionPair must be 0 (lambda) or 1 (mu)"
    )

partitionPair = method()
partitionPair(List,List) := (lambda,mu) -> (
    return new PartitionPair from {"lambda" => delete(0,lambda), "mu" => delete(0,mu), cache => new CacheTable}
    )

-*
    --first check that the input is plausibly a valid pair of partitions
    if min(lambda|mu) < 0 then error "parts must be nonnegative";
    if not ((isSorted reverse lambda) and (isSorted reverse mu)) then error "partitions must be weakly decreasing";
    lambda = delete(0,lambda);
    mu = delete(0, mu);
    k := sum mu;
    if k == 0 and lambda == {1} then (
	LM := new PartitionPair from {"lambda" => lambda, "mu" => mu, cache => new CacheTable};
    	LM.cache#"ciLinks" = {};
	LM.cache#"grade" = infinity;
	return LM
	);
    if (k <= 0) then error "invalid partitions";
    if not zero ((sum lambda - 1)%k) then error "invalid partitions";
    c := ((sum lambda) - 1)//k + 1;
    --smallest minimal link
    SML := (lambda,mu) -> (
    	rseq := take(lambda,c);
    	shift := (sum lambda) - (sum rseq) - (sum mu);
    	return(rsort(delete(0,apply(rseq, i -> i + shift))|mu),drop(lambda,c))
    	);
    --record links to c.i.
    stepcounter := 0;
    linksfromci := {(lambda,mu)};
    --if k fails to decrease after two links, partitions must be invalid
    --otherwise, k eventually reaches 1, must be c.i. (otherwise invalid)
    (lambda',mu') := (lambda,mu);
    while true do (
	if (sum mu' <= 1) then (
	    if (mu' == {1} and lambda' == toList(c:1)) then break;
	    error "invalid partitions"
	    );
    	stepcounter = stepcounter + 1;
    	(lambda',mu') = SML(lambda',mu');
    	if (stepcounter >= 2 and (sum mu' >= sum(linksfromci_1_1))) then error "invalid partitions";
    	linksfromci = {(lambda',mu')}|linksfromci
	);
    --looking at the sequence of pairs of partitions, get degree sequences to link with
    --i.e. k + 1 - lambda_1, ... , k + 1 - lambda_c
    --start is always random reg seq of linear forms
    LM = new PartitionPair from {"lambda" => lambda, "mu" => mu, cache => new CacheTable};
    LM.cache#"ciLinks" = linksfromci;
    LM.cache#"grade" = c;
    return LM
    )
*-

verify = method()
verify(PartitionPair) := LM -> (
    --first check that the input is plausibly a valid pair of partitions
    lambda := LM_0; mu := LM_1;
    if min(lambda|mu) < 0 then error "parts must be nonnegative";
    if not ((isSorted reverse lambda) and (isSorted reverse mu)) then error "partitions must be weakly decreasing";
    k := sum mu;
    if k == 0 and lambda == {1} then return;
    if (k <= 0) then error "invalid partitions";
    if not zero ((sum lambda - 1)%k) then error "invalid partitions";
    ciLinks LM;
    )

grade = method()
grade(PartitionPair) := LM -> (
    if LM.cache#?"grade" then return LM.cache#"grade";
    lambda := LM_0; mu := LM_1;
    k := sum mu;
    if k == 0 then return LM.cache#"grade" = infinity;
    return LM.cache#"grade" = ((sum lambda) - 1)//k + 1;
    )

ciLinks = method()
ciLinks(PartitionPair) := LM -> (
    if LM.cache#?"ciLinks" then return LM.cache#"ciLinks";
    c := grade LM; lambda := LM_0; mu := LM_1;
    --smallest minimal link
    SML := (lambda,mu) -> (
    	rseq := take(lambda,c);
    	shift := (sum lambda) - (sum rseq) - (sum mu);
    	return(rsort(delete(0,apply(rseq, i -> i + shift))|mu),drop(lambda,c))
    	);
    --record links to c.i.
    stepcounter := 0;
    linksfromci := {(lambda,mu)};
    --if k fails to decrease after two links, partitions must be invalid
    --otherwise, k eventually reaches 1, must be c.i. (otherwise invalid)
    (lambda',mu') := (lambda,mu);
    while true do (
	if (sum mu' <= 1) then (
	    if (mu' == {1} and lambda' == toList(c:1)) then break;
	    error "invalid partitions"
	    );
    	stepcounter = stepcounter + 1;
    	(lambda',mu') = SML(lambda',mu');
    	if (stepcounter >= 2 and (sum mu' >= sum(linksfromci_1_1))) then error "invalid partitions";
    	linksfromci = {(lambda',mu')}|linksfromci
	);
    return LM.cache#"ciLinks" = linksfromci
    )

SMLDegrees = method()
SMLDegrees(PartitionPair) := LM -> (
    if #(ciLinks LM) == 0 then return {};
    return apply(ciLinks LM, i -> apply(take(i_0,grade LM), j -> (sum i_1) + 1 - j))
    )    


link = method(Options => {Extras => false})
link(PartitionPair,List) := opts -> (LM, linkparts) -> (
    c := grade LM;
    if c == infinity then c = #linkparts;
    if not c == #linkparts then error "grade mismatch";
    newmu := LM_0|toList(c:0);
    for i in linkparts do (
	dropindex := position(newmu, j -> j == i);
	if dropindex === null then error "invalid link";
	newmu = drop(newmu,{dropindex,dropindex})
	);
    shift := sum newmu - sum LM_1;
    newLM := partitionPair(rsort(apply(linkparts, i -> i + shift)|LM_1), newmu);
    if opts.Extras then (
	if LM.cache#?"CellDimension" then (
	    oldL := LM_0|toList(c:0); newL := newLM_0|toList(c:0);
	    oldpos := {}; newpos := {};
	    for linkpart in linkparts do (
		pos := first select(1,positions(oldL, i -> i == linkpart), i -> not member(i, oldpos));
		oldpos = append(oldpos,pos);
		pos' := first select(1,positions(newL, i -> i == linkpart + shift), i -> not member(i, newpos));
		newpos = append(newpos,pos')
		);
	    newLM.cache#"CellDimension" = LM.cache#"CellDimension" + sum oldpos - sum newpos
	    );
	);
    return newLM
    )

HSS = method()
HSS(PartitionPair,ZZ) := (LM,M) -> (
    LM' := partitionPair( toList(M:(sum LM_1)) | LM_0, LM_1);
    if LM.cache#?"CellDimension" then LM'.cache#"CellDimension" = LM.cache#"CellDimension" + M;
    if LM.cache#?"grade" then LM'.cache#"grade" = LM.cache#"grade" + M;
    return LM'
    )

--N = 0: minimal links only
--N = c: all links
links = method()
links(PartitionPair,Thing) := (LM,N) -> (
    c := grade LM; if c == infinity then error "links not implemented for unit ideal";
    N' := min(N, c);
    return uniquesubsets(LM_0|toList(N':0),c)
    )

reverseSML = method()
reverseSML(PartitionPair,Thing) := (LM,N) -> (
    c := grade LM; if c == infinity then error "links not implemented for unit ideal";
    N' := min(N, c);
    return select(uniquesubsets(LM_0|toList(N':0),c),
	rseq -> min(rseq) + sum LM_0 - sum rseq - sum LM_1 >= first LM_1)
    )


--M is number of hypersurface sections, N is max non-minimality
reverseSMLwithHSS = method()
reverseSMLwithHSS(PartitionPair,ZZ,Thing) := (LM,M,N) -> (
    c := grade LM; if c == infinity then error "links not implemented for unit ideal";
    k := sum LM_1;
    links := {};
    --prefix := toList(M:k);
    trimmedlambda := select(LM_0, i -> i < k);
    N' := min(N,c+M);
    return select(uniquesubsets(trimmedlambda|toList(N':0),c+M),
	rseq -> min(rseq) + M*k + sum LM_0 - sum rseq - k >= first LM_1)
    )


enumeratePartitions = method(Options => {Limit => infinity, Sort => "Distance"})
enumeratePartitions(ZZ,Thing,Thing) := opts -> (c,d,t) -> (
    LL := new MutableHashTable;
    enumeratePartitions(LL,c,d,t,Limit => opts.Limit, Sort => opts.Sort);
    return LL
    )
enumeratePartitions(MutableHashTable,ZZ,Thing,Thing) := opts -> (LL,c,d,t) -> (
    N := opts.Limit;
    if opts.Sort == "Distance" then (
    	LL#"dt" = new MutableHashTable;
    	LL#"dt"#(-1) = {partitionPair({1},{})};
    	LL#"dt"#0 = {partitionPair(toList(c:1),{1})};
    	LL#"td" = new MutableHashTable;
    	LL#"td"#(-1) = {partitionPair({1},{})};
    	LL#"td"#0 = {partitionPair(toList(c:1),{1})};
    	i := 1;
    	while (i <= N) do (
	    newlist := {};
	    for oldpp in LL#"dt"#(i-1) do (
	    	for rseq in reverseSML(oldpp, d - #(oldpp_0) + c) do (
		    newlist = append(newlist, link(oldpp, rseq))
		    )
	    	);
	    LL#"td"#i = newlist;
	    newlist' = {};
	    for oldpp in LL#"td"#(i-1) do (
	    	for rseq in reverseSML(oldpp, t - #(oldpp_0) + c) do (
		    newlist' = append(newlist', link(oldpp, rseq))
		    )
	    	);
	    LL#"dt"#i = newlist';
	    if (#newlist == 0 and #newlist' == 0) then break;
	    i = i+1;
	    );
    	);
    if opts.Sort == "Dimension" then (
    	ci := partitionPair(toList(c:1),{1});
	ci.cache#"CellDimension" = c;
	LL#"dt" = new MutableHashTable;
    	LL#"dt"#0 = {partitionPair({1},{})};
    	LL#"dt"#c = {ci};
    	LL#"td" = new MutableHashTable;
    	LL#"td"#0 = {partitionPair({1},{})};
    	LL#"td"#c = {ci};
    	i = c; maxkey := c;
    	while (i < N and i <= maxkey) do (
	    if LL#"dt"#?i then (
		for oldpp in LL#"dt"#i do (
	    	    for rseq in reverseSML(oldpp, d - #(oldpp_0) + c) do (
		    	newLM := link(oldpp, rseq, Extras => true);
			newdim := newLM.cache#"CellDimension";
			if newdim <= N then (
			    maxkey = max(maxkey,newdim);
			    if LL#"td"#?newdim then (
			    	LL#"td"#newdim = append(LL#"td"#newdim,newLM)
			    	) else (
			    	LL#"td"#newdim = {newLM}
			    	)
			    )
		    	)
	    	    )
		);
	    if LL#"td"#?i then (
		for oldpp in LL#"td"#i do (
	    	    for rseq in reverseSML(oldpp, t - #(oldpp_0) + c) do (
		    	newLM := link(oldpp, rseq, Extras => true);
			newdim := newLM.cache#"CellDimension";
			if newdim <= N then (
			    maxkey = max(maxkey,newdim);
			    if LL#"dt"#?newdim then (
			    	LL#"dt"#newdim = append(LL#"dt"#newdim,newLM)
			    	) else (
			    	LL#"dt"#newdim = {newLM}
			    	)
			    )
		    	)
	    	    )
		);
	    i = i+1;
	    );
    	);
    )



cellDegrees = method()
cellDegrees(PartitionPair) := LM -> (
    c := grade LM; if c == infinity then return {};
    gendeglist := drop(apply(ciLinks LM, i -> apply(i_0, j -> (sum i_1)+1-j)),-1);
    linkdeglist := SMLDegrees LM;
    vardegs := linkdeglist_0;
    linkdeglist = drop(linkdeglist,1);
    for i from 0 to (#linkdeglist - 1) do (
	linkdegs := linkdeglist_i; gendegs := gendeglist_i;
	nonpivots := gendegs;
	for j in linkdegs do (
	    vardegs = vardegs | apply(select(nonpivots, s -> s < j), s -> j - s);
	    pivotpos := position(nonpivots, s -> s == j);
	    if not pivotpos === null then nonpivots = drop(nonpivots,{pivotpos,pivotpos})
	    )
	);
    return sort vardegs
    )

generateLicciExample = method()
generateLicciExample(Ring,PartitionPair) := (R,LM) -> (
    linksfromci := ciLinks LM;
    --first check that the input is plausibly a valid pair of partitions
    -*
    k := sum mu;
    if (k <= 0) then error "invalid partitions";
    if not zero ((sum lambda - 1)%k) then error "invalid partitions";
    c := ((sum lambda) - 1)//k + 1;
    --smallest minimal link
    SML := (lambda,mu) -> (
    	rseq := take(lambda,c);
    	shift := (sum lambda) - (sum rseq) - (sum mu);
    	return(rsort(delete(0,apply(rseq, i -> i + shift))|mu),drop(lambda,c))
    	);
    --record links to c.i.
    stepcounter := 0;
    linksfromci := {(lambda,mu)};
    --if k fails to decrease after two links, partitions must be invalid
    --otherwise, k eventually reaches 1, must be c.i. (otherwise invalid)
    while true do (
	if (sum mu <= 1) then (
	    if (mu == {1} and lambda == toList(c:1)) then break;
	    error "invalid partitions"
	    );
    	stepcounter = stepcounter + 1;
    	(lambda,mu) = SML(lambda,mu);
    	if (stepcounter >= 2 and (sum mu >= sum(linksfromci_1_1))) then error "invalid partitions";
    	linksfromci = {(lambda,mu)}|linksfromci
	);
    *-
    --looking at the sequence of pairs of partitions, get degree sequences to link with
    --i.e. k + 1 - lambda_1, ... , k + 1 - lambda_c
    --start is always random reg seq of linear forms
    rseqpicker := (II,degs) -> (
	mg := mingens II;
    	F := source mg;
    	n := number(degs, i -> member(i,flatten degrees F));
    	while true do (
	    coef := random(F, R^(-degs));
	    if (rank sub(coef, coefficientRing R) == n) then return mg*coef
	    )
    	);
    c := grade LM;
    deglist := apply(linksfromci, i -> apply(take(i_0,c), j -> (sum i_1) + 1 - j));
    while true do (
	I := ideal(1_R);
        ATTEMPTS := 10; --number of times to try looking for reg seq before restarting from unit ideal
    	for degs in deglist do (
    	    while (ATTEMPTS > 0) do (
    	    	alpha = rseqpicker(I,degs);
	        if (codim ideal alpha == c) then break;
		ATTEMPTS = ATTEMPTS - 1
	    	);
    	    if (ATTEMPTS > 0) then I = (ideal alpha):I
    	    );
	if (ATTEMPTS > 0) then return I
    	)
    )

genericLicci = method()
genericLicci(Ring,PartitionPair) := (kk,LM) -> (
    --first check that the input is plausibly a valid pair of partitions
    c := grade LM;
    linksfromci := ciLinks LM;
    deglist := apply(linksfromci, i -> apply(take(i_0,c), j -> (sum i_1) + 1 - j));
    linksfromunit := {({1},{})}|linksfromci;
    rseqpartlist := apply(#deglist, i ->
	apply(deglist_i, j -> (sum linksfromunit_i_1) + 1 - j)
	);
    I := ideal(1_kk);
    genmultidegs := {toList((#LM_0+#LM_1-1):0)};
    x := symbol x;
    vartable := new MutableHashTable;
    R' := kk;
    for stepcounter from 0 to (#deglist-1) do (
	yzswap := odd (#linksfromci - stepcounter);
	newrefdegsraw := RSMultidegrees(
	    partitionPair(linksfromunit_stepcounter),rseqpartlist_stepcounter);
	if yzswap then (
	    newrefdegs := apply(newrefdegsraw, seq ->
		seq_0|seq_2|toList((#LM_0-c-#seq_2):0)|seq_1|toList((#LM_1-#seq_1):0))
	    ) else (
	    newrefdegs = apply(newrefdegsraw, seq ->
		seq_0|seq_1|toList((#LM_0-c-#seq_1):0)|seq_2|toList((#LM_1-#seq_2):0))
	    );
	--linkdegs := deglist_stepcounter;
	--<< "variable count: " << #gens R' << ". linking with degrees " << linkdegs << endl;	   
	--I = (positiveSemigenericLink(I,linkdegs))_1;
	coeffmatrixentries := {};
	pivotlist := {};
	for rowindex from 0 to #newrefdegs-1 do (
	    deg := newrefdegs_rowindex;
	    samedegs := positions(genmultidegs, i -> i == deg);
	    if #samedegs > 0 then (
		pivot := first select(samedegs, i -> not member(i,pivotlist));
		coeffmatrixentries = append(coeffmatrixentries, (rowindex,pivot) => 1);
		pivotlist = append(pivotlist, pivot);
		);
    	    for colindex from 0 to #genmultidegs-1 do (
		vardeg := deg - genmultidegs_colindex;
		if vardeg_0 > 0 and not member(colindex,pivotlist) then (
	    	    if (not vartable#?(vardeg_0)) then (
    			vartable#(vardeg_0) = {{vardeg,x_(vardeg_0,1)}}
    			) else (
    			vartable#(vardeg_0) = append(vartable#(vardeg_0),{vardeg,x_(vardeg_0,#vartable#(vardeg_0) + 1)})
    			);
	    	    coeffmatrixentries = append(coeffmatrixentries, (rowindex,colindex) => last last vartable#(vardeg_0))
	    	    )
		)
    	    );
	vardata := transpose flatten values vartable;
	R' = kk[vardata_1, Degrees => vardata_0];
	newcoeffmatrixentries := apply(coeffmatrixentries, opt -> opt#0 => (opt#1)_(R'));
	regseq := (gens sub(I,R'))*(transpose map(R'^(c),R'^(#genmultidegs),newcoeffmatrixentries));
	I = ideal(regseq) : sub(I,R');
	genmultidegs = (degree\(flatten entries gens I));
    	);
    return I
    )


listcomps = method()
listcomps(List,ZZ) := (N,k) -> (
    listcompss := (N,k) -> (
	if N == {} or k < 0 then {}
	else if k == 0 then {toList(#N:0)}
	else if last N == 0 then apply(listcompss(drop(N,-1),k), s -> s|{0})
	else join(
	    apply(listcompss(drop(N,-1),k), s -> s|{0}),
	    apply(listcompss(drop(N,-1)|{last N - 1},k-1), s -> s + (toList(#N-1:0) | {1}))
	    )
	);
    listcompss = memoize listcompss;
    result := listcompss(N,k);
    listcompss = null;
    return result
    )

uniquesubsets = method()
uniquesubsets(List,ZZ) := (L,k) -> (
    uniq := unique L;
    N := apply(uniq, i -> number(L, s -> s === i));
    return apply(listcomps(N,k), l -> join toSequence apply(#l, j -> toList(l_j:uniq_j)))
    )


RSMultidegrees = method()
RSMultidegrees(PartitionPair,List) := (LM,rseqparts) -> (
    c := #rseqparts; d := #LM_0 - c; t := #LM_1; nm := number(rseqparts,i -> i==0);
    pivotlist := {};
    for rseqpart in rseqparts do (
	sameparts := positions(LM_0|toList(c:0), i -> i == rseqpart);
	pivot := first select(sameparts, i -> not member(i,pivotlist));
	pivotlist = append(pivotlist,pivot)
	);
    Fweights := apply(pivotlist, i -> (
	    if i == 0 then (
		toprow := {1}|toList((c+d+nm-1):0);
		botcol := toList((t+1):0)
		) else if i <= c-2 then (
		toprow = toList((i-1):0)|{-1,1}|toList((c+d+nm-1-i):0);
		botcol = toList((t+1):0)
		) else (
		toprow = toList((i-1):0)|{-1,1}|toList((c+d+nm-1-i):0);
		botcol = {1}|toList(t:0)
		);
	    return TLabel(
		{toprow_(c-2)},
		reverse take(toprow,c-2),
		drop(toprow,c-1),
		botcol
		)
	    )
    	);
    if LM_1 == {} then (
	sigma := {}
	) else (
    	weightLM := TFromPartitions(LM_0,LM_1);
    	sigma = first makePositive(weightLM,{})
    	);
    deglist := {};
    for Fweight in Fweights do (
	newgenweight := simpleRefs(reverse sigma, Fweight);
    	disp := TLabel(
    	    newgenweight#"u",
    	    drop(newgenweight#"x",-1)|{last newgenweight#"x" - 1},
    	    newgenweight#"y",
    	    newgenweight#"z"
    	    );
    	yy := reverse(disp#"y");
	alphay := {0,0};
	for i from 0 to (#yy-1) do (
    	    alphay = {2*alphay_0 - alphay_1 + yy_i}|alphay
    	    );
	zz := reverse(disp#"z");
	alphaz := {0,0};
	for i from 0 to (#zz-1) do (
    	    alphaz = {2*alphaz_0 - alphaz_1 + zz_i}|alphaz
    	    );
	--alphay_0 == alphaz_0
	xx := disp#"x";
	alphax := {2*alphay_0 - alphay_1 - alphaz_1 + first disp#"u",alphay_0};
	for i from 0 to (#xx-2) do (
    	    alphax = {2*alphax_0 - alphax_1 + xx_i}|alphax
    	    );
	deglist = deglist|{(alphax,drop(drop(alphay,1),-2),drop(drop(alphaz,1),-2))}
	);
    return deglist
    )

