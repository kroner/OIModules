--compute ordered surjections [m]->[n]
orderedSurjections = method()
orderedSurjections (ZZ,ZZ) := List => (n,m) -> (
    if n>m then return {};
    ans:={};
    for c in compositions(n,m-n) do (
	temp:={{}};
	for i from 1 to n do (
	    temp=apply(temp,j->append(j,i));
	    for j from 1 to c_(i-1) do temp=flatten(apply(i,k->apply(temp,w->append(w,k+1))));
	    );
	ans=join(ans,temp);
	);
    ans
    )

end
restart
load "OSmodules.m2"

