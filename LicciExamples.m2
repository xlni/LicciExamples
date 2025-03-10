generateLicciExample = method()
generateLicciExample(Ring,List,List) := (R,lambda,mu) -> (
    --first check that the input is plausibly a valid pair of partitions
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
    --looking at the sequence of pairs of partitions, get degree sequences to link with
    --i.e. k + 1 - lambda_1, ... , k + 1 - lambda_c
    --start is always random reg seq of linear forms
    deglist := apply(linksfromci, i -> apply(take(i_0,c), j -> (sum i_1) + 1 - j));
    while true do (
	I := ideal(1_R);
        ATTEMPTS := 10; --number of times to try looking for reg seq before restarting from unit ideal
    	for degs in deglist do (
    	    while (ATTEMPTS > 0) do (
    	    	alpha = (gens I)*(transpose random(R^degs,R^(degree\(flatten entries gens I))));
	        if (codim ideal alpha == c) then break;
		ATTEMPTS = ATTEMPTS - 1
	    	);
    	    if (ATTEMPTS > 0) then I = (ideal alpha):I
    	    );
	if (ATTEMPTS > 0) then return I
    	)
    )

end--
restart
load "LicciExamples.m2"

R = ZZ/101[x_1..x_3]

--c.i.
(lambda,mu) = ({1,1,1},{1})
I = generateLicciExample(R,lambda,mu)
minimalBetti I

--Brown 1562
(lambda,mu) = ({2,2,1,1,1},{2,1})
I = generateLicciExample(R,lambda,mu)
minimalBetti I

--CKLW 1562
(lambda,mu) = ({2,2,2,2,1},{2,2})
I = generateLicciExample(R,lambda,mu)
minimalBetti I

R = ZZ/101[x_1..x_5]

--double hypersurface section of BE
(lambda,mu) = ({2,2,1,1,1,1,1},{2})
I = generateLicciExample(R,lambda,mu)
minimalBetti I

--Huneke-Ulrich
(lambda,mu) = ({2,2,2,2,2,2,1},{3})
I = generateLicciExample(R,lambda,mu)
minimalBetti I




