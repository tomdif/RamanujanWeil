\\ Ordinary-locus version: O(q) := sum_{p !| t, t^2<4q} h10(t,q) H(4q-t^2)   (q = p^n)
\\ Compare with -2 s_n  (s_n = alpha^n+beta^n); print the defect D(q) = O(q) + 2 s_n and D / p^(5n).
default(nbthreads,1);
h(k,a,q) = sum(j=0,k\2, (-q)^j*binomial(k-j,j)*a^(k-2*j));
pw(p,n) = my(t=ramanujantau(p), s0=2, s1=t, s2); if(n==0,return(2)); for(i=2,n, s2=t*s1-p^11*s0; s0=s1; s1=s2); s1;
Ord(p,n) = my(q=p^n); sum(t=-sqrtint(4*q),sqrtint(4*q), if(t%p && t^2<4*q, h(10,t,q)*qfbhclassno(4*q-t^2), 0));
forprime(p=2,13, for(n=1,6, my(D=Ord(p,n)+2*pw(p,n)); print("p=",p," n=",n," D=",D,"  D/p^(5n)=",D/p^(5*n))));
