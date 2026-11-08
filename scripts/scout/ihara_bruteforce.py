"""Independent brute-force check (no PARI) of the level-1 Ihara/Birch identity over F_p:
   sum_{A,B in F_p, 4A^3+27B^2 != 0} h10(a_{A,B}, p) = (p-1) * (-1 - tau(p)),
   a_{A,B} = p + 1 - #E_{A,B}(F_p),  tau from the q-expansion of Delta = q prod (1-q^n)^24."""
from math import comb
def tau_list(N):
    c = [0]*(N+1); c[0] = 1
    for n in range(1, N+1):
        for _ in range(24):
            for m in range(N, n-1, -1):
                c[m] -= c[m-n]
    return [0] + c[:N]          # tau(n) = coeff of q^n in q*prod
def h(k, a, q):
    return sum((-q)**j * comb(k-j, j) * a**(k-2*j) for j in range(k//2+1))
def check(p, tau):
    sq = [0]*p
    for y in range(p): sq[y*y % p] += 1
    S = 0
    for A in range(p):
        for B in range(p):
            if (4*A**3 + 27*B**2) % p == 0: continue
            n = 1 + sum(sq[(x**3 + A*x + B) % p] for x in range(p))
            S += h(10, p + 1 - n, p)
    return S, (p-1)*(-1 - tau[p])
tau = tau_list(60)
assert tau[1:6] == [1, -24, 252, -1472, 4830]
for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]:
    S, R = check(p, tau)
    print(p, S, R, S == R)
