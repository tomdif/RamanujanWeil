default(nbthreads,1);
h(k,a,q) = sum(j=0,k\2, (-q)^j*binomial(k-j,j)*a^(k-2*j));
SL(p) = { my(S=0); for(l=2,p-1, my(E=ellinit([0,-(1+l),0,l,0],p)); S+=h(10,p+1-ellcard(E),p)); S };
for(N=2,4, my(mf=mfinit([N,12],0)); print("N=",N," new dim ",mfdim(mf)));
mf4=mfinit([4,12],0); L4=mfeigenbasis(mf4); print("level4 new eigenforms: ",#L4);
mf2=mfinit([2,12],0); L2=mfeigenbasis(mf2); print("level2 new eigenforms: ",#L2);
g=L4[1]; cg=mfcoefs(g,400); print("g coeffs: ",cg[1..12]);
\\ fit S_L(p) = x0 + x1*tau(p) + x2*a_p(g)  over odd primes
rows=[]; rhs=[];
forprime(p=3,200, my(S=SL(p)); rows=concat(rows,[[1,ramanujantau(p),cg[p+1]]]); rhs=concat(rhs,[S]));
M=Mat(rows~)~; M=matrix(#rows,3,i,j,rows[i][j]); b=rhs~;
x=matsolve(M[1..3,],b[1..3]); print("fit from first 3 primes: ",x);
print("residual on all p<200: ", M*x-b == 0);
forprime(p=3,23, print(p," SL=",SL(p)," tau=",ramanujantau(p)," a_g=",cg[p+1]));
