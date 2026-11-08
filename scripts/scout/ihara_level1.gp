\\ Ihara/Birch identity, level 1, weight 12, verified numerically.
\\ h_k(a,q) = tr Sym^k of a 2x2 matrix with trace a, det q.
default(nbthreads,1);
h(k,a,q) = sum(j=0,k\2, (-q)^j*binomial(k-j,j)*a^(k-2*j));
\\ alpha^n+beta^n for X^2 - tau(p) X + p^11
pw(p,n) = my(t=ramanujantau(p), s0=2, s1=t, s2); if(n==0,return(2)); for(i=2,n, s2=t*s1-p^11*s0; s0=s1; s1=s2); s1;
\\ field elements of F_{p^n} via the polynomial basis of ffgen
fq(p,n) = { if(n==1, return(vector(p,i,Mod(i-1,p)))); my(g=ffgen(p^n,'g), v=vector(p^n), c=0);
  forvec(e=vector(n,i,[0,p-1]), c++; v[c]=sum(i=1,n,e[i]*g^(i-1)) + 0*g); v };
S_short(p,n) = { my(q=p^n, F=fq(p,n), S=0, E, a);
  for(i=1,q, for(j=1,q, my(A=F[i],B=F[j]); if(4*A^3+27*B^2!=0, E=ellinit([A,B]); a=q+1-ellcard(E); S+=h(10,a,q)))); S };
\\ full 5-parameter Weierstrass sum (any p)
S_full(p,n) = { my(q=p^n, F=fq(p,n), S=0, E, a);
  forvec(e=vector(5,i,[1,q]), my(c=vector(5,i,F[e[i]])); E=ellinit(c); if(E!=[] && E.disc!=0, a=q+1-ellcard(E); S+=h(10,a,q))); S };
print("short Weierstrass, q=p: S(p) vs (p-1)(-1-tau(p))");
forprime(p=5,61, my(S=S_short(p,1), R=(p-1)*(-1-ramanujantau(p))); print(p," ",S," ",R," ",S==R));
print("short Weierstrass, q=p^2: S vs (q-1)(-1-(alpha^2+beta^2))");
forprime(p=5,13, my(q=p^2,S=S_short(p,2), R=(q-1)*(-1-pw(p,2))); print(q," ",S," ",R," ",S==R));
print("short Weierstrass, q=5^3:");
my(q=125,S=S_short(5,3),R=(q-1)*(-1-pw(5,3))); print(q," ",S," ",R," ",S==R);
print("full 5-parameter Weierstrass, small q: S vs q^3(q-1)(-1-(alpha^n+beta^n))");
foreach([[2,1],[3,1],[2,2],[5,1],[2,3],[3,2]], v, my(p=v[1],n=v[2],q=p^n,S=S_full(p,n),R=q^3*(q-1)*(-1-pw(p,n))); print(q," ",S," ",R," ",S==R));
