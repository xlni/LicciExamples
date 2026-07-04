restart
load "licci-combinatorics.m2"
load "licci-examples.m2"

-------------------------------------
-- Operation in Theorems 3.1 / 8.1 --
-------------------------------------

--usage: link(partitionPair(lambda,mu), {lambda'_1,...,lambda'_c})
--outputs partitionPair(lambda^link, mu^link)
link(partitionPair({1,1,1},{1}), {1,0,0})

--------------------
-- Algorithm 3.16 --
--------------------

generateLicciExample(
    ZZ/101[x,y,z],
    partitionPair({2,1,1,1},{1,1})
    )

-----------------
-- Section 4.1 --
-----------------

--usage: links(partitionPair(lambda,mu),N) returns the possible choices of lambda'_1,...,lambda'_c where at most N are equal to 0
--setting N higher than c has the same effect as setting it equal to c
ss = partitionPair({2,2,1,1,1},{2,1})
links(ss,infinity)
netList apply(links(ss,infinity), ll -> {ll,link(ss,ll)})

link(partitionPair({1,1,1},{1}), {1,0,0})

-----------------
-- Section 4.2 --
-----------------

--this enumerates families of licci ideals up to CIDISTANCE links away from a c.i.
--with grade c, deviation <= d, and type <= t.
--CIDISTANCE may be set to infinity, but then the calculation will not terminate
--unless (c,d,t) corresponds to a Dynkin diagram.

(c,d,t) = (3,4,2);

CIDISTANCE = infinity; LMList = enumeratePartitions(c,d,t,Limit => CIDISTANCE);
peek LMList#"dt" --these have deviation <= d and type <= t
peek LMList#"td" --these have deviation <= t and type <= d

(d',t') = (4,2) --enumerates for (1,7,8,2)
--select the ones that have deviation exactly d' and type exactly t', sort by k = sum(mu)
netList sort(
    apply(
        select(
            flatten values LMList#"dt", ss -> (#ss_0 == c+d') and (#ss_1 == t')
            ),
        ss -> {sum ss_1, ss_0, ss_1}
        )
    )

(d',t') = (2,4) --enumerates for (1,5,8,4)
--select the ones that have deviation exactly d' and type exactly t', sort by k = sum(mu)
netList sort(
    apply(
        select(
            flatten values LMList#"td", ss -> (#ss_0 == c+d') and (#ss_1 == t')
            ),
        ss -> {sum ss_1, ss_0, ss_1}
        )
    )



-------------------------
-- Section 7.2 and 7.3 --
-------------------------

k = 4
ss = partitionPair(toList((k-1):2) | {1,1,1}, {k-1,1})
I = genericLicci(QQ,ss)

F = res I;
netList entries transpose F.dd_1
netList entries F.dd_2
netList entries F.dd_3

-----------------
-- Section 8.2 --
-----------------

--same code as for Section 4.2, just with different parameters
(c,d,t) = (4,4,1);

CIDISTANCE = infinity; LMList = enumeratePartitions(c,d,t,Limit => CIDISTANCE);
peek LMList#"dt"
peek LMList#"td"

(d',t') = (4,1); --grade 4 Gorenstein on 8 generators
netList sort(
    apply(
        select(
            flatten values LMList#"dt", ss -> (#ss_0 == c+d') and (#ss_1 == t')
            ),
        ss -> {sum ss_1, ss_0, ss_1}
        )
    )

(d',t') = (1,4); --grade 4 a.c.i. with type 4
netList sort(
    apply(
        select(
            flatten values LMList#"td", ss -> (#ss_0 == c+d') and (#ss_1 == t')
            ),
        ss -> {sum ss_1, ss_0, ss_1}
        )
    )

-----------------
-- Section 8.3 --
-----------------

--same code as for Section 4.2, just with different parameters
(c,d,t) = (6,2,1);

CIDISTANCE = infinity; LMList = enumeratePartitions(c,d,t,Limit => CIDISTANCE);
peek LMList#"dt"
peek LMList#"td"

(d',t') = (2,1);
netList sort(
    apply(
        select(
            flatten values LMList#"dt", ss -> (#ss_0 == c+d') and (#ss_1 == t')
            ),
        ss -> {sum ss_1, ss_0, ss_1}
        )
    )
--note that in the output, one is a triple hypersurface section of ({1,1,1,1,1},{2}) and another is
--a hypersurface section of ({2,2,2,2,2,2,1},{3}).