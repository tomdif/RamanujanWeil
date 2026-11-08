\\ (1) Eichler–Selberg, weight 12 level 1:  sum_{t^2<=4n} h10(t,n) H(4n-t^2) = -2 tau(n) - sum_{dd'=n} min(d,d')^11
\\     with Hurwitz H(0) = -1/12 (qfbhclassno(0) = -1/12 in PARI).
\\ (2) Deuring (q = p prime): sum_{A,B} [a_{A,B} = t] = (p-1) * H(4p - t^2)/2   (p >= 5)
default(nbthreads,1);
h(k,a,q) = sum(j=0,k\2, (-q)^j*binomial(k-j,j)*a^(k-2*j));
ES(n) = sum(t=-sqrtint(4*n),sqrtint(4*n), h(10,t,n)*qfbhclassno(4*n-t^2)) + sumdiv(n,d,min(d,n/d)^11);
ok=1; for(n=1,300, if(ES(n) != -2*ramanujantau(n), ok=0; print("ES fails at ",n))); print("ES weight 12 level 1, n<=300: ",ok);
deur(p) = { my(cnt=vector(4*sqrtint(p)+5), ok=1, o=2*sqrtint(p)+2);
  for(A=0,p-1, for(B=0,p-1, if((4*A^3+27*B^2)%p, my(t=p+1-ellcard(ellinit([A,B],p))); cnt[t+o]++)));
  for(t=-sqrtint(4*p),sqrtint(4*p), if(t^2<4*p, if(cnt[t+o] != (p-1)*qfbhclassno(4*p-t^2)/2, ok=0)));
  ok };
ok=1; forprime(p=5,101, if(!deur(p), ok=0; print("Deuring fails ",p))); print("Deuring prime-field count p<=101: ",ok);
\\ (3) prime powers: does N(t,q) = (q-1) H(4q-t^2)/2 hold for q=p^2?  (expected: NO for p | t)
fq(p,n) = { my(g=ffgen(p^n,'g), v=vector(p^n), c=0); forvec(e=vector(n,i,[0,p-1]), c++; v[c]=sum(i=1,n,e[i]*g^(i-1)) + 0*g); v };
deurq(p,n) = { my(q=p^n,F=fq(p,n),o=2*sqrtint(q)+2,cnt=vector(4*sqrtint(q)+5));
  for(i=1,q,for(j=1,q, my(A=F[i],B=F[j]); if(4*A^3+27*B^2!=0, my(t=q+1-ellcard(ellinit([A,B]))); cnt[t+o]++)));
  for(t=-2*sqrtint(q),2*sqrtint(q), my(c=cnt[t+o], hh=(q-1)*qfbhclassno(4*q-t^2)/2); if(c!=hh, print("  q=",q," t=",t," count=",c," (q-1)H/2=",hh))) };
print("prime-power discrepancies (q=25, 49):"); deurq(5,2); deurq(7,2);
