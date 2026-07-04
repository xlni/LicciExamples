TLabeling = new Type of HashTable

--creating a TLabeling
TLabel = method();
TLabel (List,List,List,List) := TLabeling => (u,x,y,z) -> (
    if not (#u == 1) then error "u should have length 1";
    return new TLabeling from hashTable{
	"u" => u,
	"x" => x,
	"y" => y,
	"z" => z,
	cache => new CacheTable
	}
    )

--displaying a TLabeling in a T shape
net TLabeling := h -> netList (
    {(reverse h#"x")|(h#"u")|(h#"y")}
    |
    transpose(
	apply(#h#"x", i -> apply(#h#"z", i -> null))
	|
	{h#"z"}
	|
	apply(#h#"y", i -> apply(#h#"z", i -> null))
	)
    )

--performing the simple reflection arm_node on T
simpleRef = method();
simpleRef(Sequence,TLabeling) := TLabeling => (armnode,T) -> simpleRef(armnode_0,armnode_1,T)
simpleRef(String,ZZ,TLabeling) := TLabeling => (arm,node,T) -> (
    newT := new IndexedVariableTable;
    arms := {"x","y","z"};
    for xyz in arms do newT_xyz = new MutableList from T#xyz;
    newT_"u" = new MutableList from T#"u";
    if arm == "u" then (
	for xyz in arms do (
	    if #T#xyz > 0 then newT_xyz#0 = T#xyz_0 + T#"u"_0
	    );
	newT_"u"#0 = (-1)*T#"u"_0;
	) else (
	if node < 1 or node > #T#arm then error "invalid node";
	if node == 1 then (
	    newT_"u"#0 = T#"u"_0 + T#arm_0;
	    );
	if node > 1 then (
	    newT_arm#(node-2) = newT_arm#(node-2) + T#arm_(node-1);
            );
	if node < #T#arm then (
	    newT_arm#node = newT_arm#node + T#arm_(node-1);
	    );
	newT_arm#(node-1) = (-1)*T#arm_(node-1)
	);
    return TLabel(toList newT_"u",toList newT_"x",toList newT_"y",toList newT_"z")
    )

--apply a sequence of reflections, from right to left
--i.e. think of it as s_i...s_1*T
simpleRefs = method();
simpleRefs(List,TLabeling) := TLabeling => (refs,T) -> (
    fold(refs,T,(l,i) -> simpleRef(l_0,l_1,i))
    )

--list of all nodes
listNodes = method();
listNodes(TLabeling) := List => T -> (
    apply(reverse toList(1..#T#"x"), i -> ("x",i))
    |{("u",0)}
    |apply(toList(1..#T#"y"), i -> ("y",i))
    |apply(toList(1..#T#"z"), i -> ("z",i))
    )

label = method();
label(Sequence,TLabeling) := ZZ => (armnode,T) -> label(armnode_0,armnode_1,T)
label(String,ZZ,TLabeling) := ZZ => (arm,node,T) -> (
    if arm == "u" then (
	return T#"u"#node
	) else if node <= 0 then (
	error "invalid node"
	) else (
	return T#arm#(node-1)
	)
    )

neighbors = method();
neighbors(Sequence,TLabeling) := List => (armnode,T) -> neighbors(armnode,#T#"x"+1,#T#"y"+1,#T#"z"+1)
neighbors(Sequence,ZZ,ZZ,ZZ) := List => (armnode,p,q,r) -> (
    arm := armnode_0; node := armnode_1;
    nn := new IndexedVariableTable; arms := {"x","y","z"};
    nn_"u" = {};
    num := new IndexedVariableTable; num_"x" = p-1; num_"y" = q-1; num_"z" = r-1;
    for xyz in arms do nn_xyz = {};
    if arm == "u" then (
	for xyz in arms do (
	    if num_xyz > 0 then nn_xyz = {1};
	    );
	) else (
	if node < 1 or node > num_arm then error "invalid node";
	if node == 1 then (
	    nn_"u" = {0};
	    );
	if node > 1 then (
	    nn_arm = nn_arm|{node-1}
            );
	if node < num_arm then (
	    nn_arm = nn_arm|{node+1}
	    );
	);
    return (
	apply(nn_"u", i -> ("u",i))
	|apply(nn_"x", i -> ("x",i))
	|apply(nn_"y", i -> ("y",i))
	|apply(nn_"z", i -> ("z",i))
	)
    )

--Tpqr notation
simpleRoot = method();
simpleRoot(Sequence,TLabeling) := TLabeling => (armnode,T) -> simpleRoot(armnode,#T#"x"+1,#T#"y"+1,#T#"z"+1);
simpleRoot(Sequence,ZZ,ZZ,ZZ) := TLabeling => (armnode,p,q,r) -> (
    neighs := neighbors(armnode,p,q,r);
    vec := new IndexedVariableTable; arms := {"x","y","z"};
    vec_"u" = {0};
    num := new IndexedVariableTable; num_"x" = p-1; num_"y" = q-1; num_"z" = r-1;
    for xyz in arms do vec_xyz = toList(num_xyz:0);
    for l in neighs do (
	if l_0 == "u" then (
	    vec_(l_0) = replace(0,-1,vec_(l_0))
	    ) else (
	    vec_(l_0) = replace(l_1-1,-1,vec_(l_0))
       	    )
	);
    if armnode_0 == "u" then (
	vec_(armnode_0) = replace(0,2,vec_(armnode_0))
	) else (
	vec_(armnode_0) = replace(armnode_1-1,2,vec_(armnode_0))
	);
    return TLabel(vec_"u",vec_"x",vec_"y",vec_"z")
    )

--apply reflections at negative labels other than exceptions
makePositive = method();
makePositive(TLabeling,List) := (TLabeling,List) => (T,exception) -> (
    subdiag := select(listNodes T, i -> not member(i,exception));
    tempT := T; refs := {};
    breaker := false;
    while not breaker do (
    	firstneg := position(subdiag, i -> label(i,tempT) < 0);
    	if not (firstneg === null) then (
    	    tempT = simpleRef(subdiag_firstneg,tempT);
    	    refs = refs|{subdiag_firstneg}
    	    ) else (
	    breaker = true
	    )
    	);
    return (refs,tempT)
    )

--apply reflections at positive labels other than exceptions
makeNegative = method();
makeNegative(TLabeling,List) := (TLabeling,List) => (T,exception) -> (
    subdiag := select(listNodes T, i -> not member(i,exception));
    tempT := T; refs := {};
    breaker := false;
    while not breaker do (
    	firstneg := position(subdiag, i -> label(i,tempT) > 0);
    	if not (firstneg === null) then (
    	    tempT = simpleRef(subdiag_firstneg,tempT);
    	    refs = refs|{subdiag_firstneg}
    	    ) else (
	    breaker = true
	    )
    	);
    return (refs,tempT)
    )

yzSwap = method();
yzSwap(TLabeling) := TLabeling => T -> (
    newT := TLabel(T#"u",T#"x",T#"z",T#"y");
    if T.cache#?"sigma" then (
	newT.cache#"sigma" = apply(T.cache#"sigma", (i,j) -> (
		if i == "y" then i' := "z" else if i == "z" then i' = "y" else i' = i;
		return (i',j)
		)
    	    )
	);
    return newT
    )

algebraStructure = method();
algebraStructure(TLabeling) := Thing => T' -> (
    c := #T'#"x"+2;
    if not c==3 then error "only implemented for c=3";
    if not T'.cache#?"sigma" then T'.cache#"sigma" = (makePositive(T',{}))_0;
    sigma := T'.cache#"sigma";
    d := max({0}|apply(select(sigma,i -> i_0 == "y"),i -> i_1));
    t := max(apply(select(sigma,i -> i_0 == "z"),i -> i_1));
    -*
    T := TLabel(
	T'#"u",
	T'#"x",
	take(T'#"y",d),
	take(T'#"z",t)
	);
    *-
    --omega := new IndexedVariableTable;
    if d == 0 then (
	omegay := TLabel(
    	    {1},
    	    apply(c-2,i->0),
    	    {-1},
    	    apply(t+1,i->0)
    	    )
	) else (
	omegay = TLabel(
    	    {0},
    	    apply(c-2,i->0),
    	    apply(d-1,i->0)|{1,-1},
    	    apply(t+1,i->0)
    	    );
    	);
    omegaz := TLabel(
    	{0},
    	apply(c-2,i->0),
    	apply(d+1,i->0),
    	apply(t-1,i->0)|{1,-1}
    	);
    F2refs := (
    	apply(d, i -> ("y",d-i))
    	|
    	{("u",0)}
    	|
    	apply(t, i -> ("z",i+1))
    	);
    --dual basis to fn ... f1
    ztop := reverse (accumulate(F2refs,omegaz,simpleRef)|{omegaz});
    --basis f1 ... fn
    ytop := reverse (accumulate(reverse F2refs,omegay,simpleRef)|{omegay});
    ynew := apply(ytop, i -> simpleRefs(sigma,i));
    znew := apply(ztop, i -> simpleRefs(sigma,i));
    --how to tell if this is in the multiplicative structure or past it?
    --maybe it's best to do it on a **larger** diagram
    if (number(ynew, i -> (matrix{i#"z"}*(transpose matrix{toList(0..t)}))_(0,0) == 0)
	+number(znew, i -> (matrix{i#"z"}*(transpose matrix{toList(0..t)}))_(0,0) == -1) > 0) then << "WARNING: this resolution is not minimal!" << endl;
    ymulti := positions(ynew, i -> (matrix{i#"z"}*(transpose matrix{toList(0..t)}))_(0,0) == 1);
    zmulti := positions(znew, i -> (matrix{i#"z"}*(transpose matrix{toList(0..t)}))_(0,0) == 0);
    F1pairs = apply(znew_zmulti, i -> {1,1} + positions(
	    reverse accumulate((x,y)->x+y,{0}|(reverse i#"y")|i#"u"|i#"x"),
	    j -> j == 1
	    ));
    F1F3pairs = apply(ynew_ymulti, i -> {1 + position(
		(reverse i#"x")|i#"u"|i#"y",
		j -> j == 1
		), position(
		i#"z",
		j -> j == 1
		)});
    p := #F1pairs;
    r := #F1F3pairs;
    q := max ({0}|apply(F1F3pairs, i -> i_1));
    q' := #unique(apply(F1F3pairs, i -> i_1));
    if (not q == q') then error "Debug: q != q', this should not happen!!";
    if (p,q,r) == (1,1,2) then (
	CLASS := ("B")
	) else if (p,q,r) == (3,1,3) then (
	CLASS = ("CI")
	) else if ((p,q) == (0,1) and r >= 2) then (
	CLASS = ("G",r)
	) else if (q == r and p == number(F1pairs, i -> i_0 == 1)) then (
	CLASS = ("H",p,q)
	) else if (p,q,r) == (3,0,0) then (
	CLASS = ("TE")
	) else (
	error "Debug: unclassified multiplication---this should not happen!!"
	);
    -*
    e := symbol e; f := symbol f; g := symbol g;
    mult11 := apply(#zmulti, i -> net e_(F1pairs_i_0)|net e_(F1pairs_i_1)|"="|net f_(t+d+2-zmulti_i));
    mult12 := apply(#ymulti, i -> net e_(F1F3pairs_i_0)|net f_(ymulti_i+1)|"="|net g_(F1F3pairs_i_1));
    mmax := max(#mult11,#mult12);
    --<< "These products are only up to sign!" << endl;
    T'.cache#"visualmulti" = transpose {mult11|apply(mmax-#mult11,i->null),mult12|apply(mmax-#mult12,i->null)};
    *-
    return CLASS
    )

partitionsFromT = method()
partitionsFromT(TLabeling) := Sequence => T -> (
    if T.cache#?"partitions" then return T.cache#"partitions";
    (c,d,t) := (#T#"x"+2,#T#"y",#T#"z");
    if not T.cache#?"sigma" then T.cache#"sigma" = (makePositive(T,{}))_0;
    sigma := T.cache#"sigma";
    omega := new IndexedVariableTable;
    omega_x = TLabel(
	{0},
	apply(c-3,i->0)|{1},
	apply(d+1,i->0),
	apply(t+1,i->0)
	);
    newT := simpleRefs(sigma,omega_x);
    return T.cache#"partitions" = (
	accumulate((reverse newT#"x")|newT#"u"|newT#"y"|{0},(x,y) -> x+y),
	accumulate(drop(newT#"z",1)|{0},(x,y) -> x+y)
	)
    )
TFromPartitions = method()
TFromPartitions(List,List) := TLabeling => (lambda,mu) -> (
    c := ((sum lambda)-1)//(sum mu) + 1;
    toprow := apply(#lambda, i -> lambda_i - (lambda|{0})_(i+1));
    botcol := apply(#mu, i -> mu_i - (mu|{0})_(i+1));
    x := reverse take(toprow,c-2);
    u := {toprow_(c-2)};
    y := drop(toprow,c-1);
    z1 := matrix({toList(1..(#toprow-c+1))})*(transpose matrix {y}) - matrix({toList(2..(#botcol+1))})*(transpose matrix {botcol});
    return TLabel(
	u,
	x,
	y,
	{z1_(0,0)}|botcol
	)
    )

shrinkT = method()
shrinkT(TLabeling) := TLabeling => T -> (
    sigma := (makePositive(T,{}))_0;
    d := max(apply(select(sigma,i -> i_0 == "y"),i -> i_1));
    t := max(apply(select(sigma,i -> i_0 == "z"),i -> i_1));
    T' := TLabel(
	T#"u",
	T#"x",
	take(T#"y",d),
	take(T#"z",t)
	);
    T'.cache#"sigma" = sigma;
    if T.cache#?"partitions" then T'.cache#"partitions" = T.cache#"partitions";
    return T'
    )

cartanMatrix = method()
cartanMatrix(TLabeling) := Matrix => T -> cartanMatrix(#T#"x"+1,#T#"y"+1,#T#"z"+1)
cartanMatrix(ZZ,ZZ,ZZ) := Matrix => (p,q,r) -> (
    n := p+q+r-2;
    return map(QQ^n,QQ^n,
    	apply(n, i -> (i,i) => 2)
    	|
    	{(0,1) => -1, (1,0) => -1, (0,p) => -1, (p,0) => -1, (p+q-1,0) => -1, (0,p+q-1) => -1}
    	|
    	apply(p-2, i -> (i+1,i+2) => -1)|apply(p-2, i -> (i+2,i+1) => -1)
    	|
    	apply(q-2, i -> (p+i,p+i+1) => -1)|apply(q-2, i -> (p+i+1,p+i) => -1)
    	|
    	apply(r-2, i -> (p+q+i-1,p+q+i) => -1)|apply(r-2, i -> (p+q+i,p+q+i-1) => -1)
    	)
    )

vectorFromT = method()
vectorFromT(TLabeling) := Matrix => T -> transpose matrix{T#"u"|T#"x"|T#"y"|T#"z"}
