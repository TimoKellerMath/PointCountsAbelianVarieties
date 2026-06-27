#!/usr/bin/env python3
"""
General-g threshold search: for an abelian variety of dim g over F_q, what is the
minimal N such that (c_1,...,c_N) determines the isogeny class for large q?

Enumeration: integer real-Weil polynomials h(T)=prod(T-beta_i), beta_i real in
[-2rq,2rq], are enumerated by a recursive "integration-constant interval" DFS.
Writing  htilde_j = (j!/g!) h^{(g-j)}  (monic, degree j), one has htilde_j' = j*htilde_{j-1},
so htilde_j = j*int(htilde_{j-1}) + C_j and Rolle forces htilde_{j-1} (hence every
prefix) to be real-rooted in [m,M].  The constant C_j <-> integer b_j is restricted to
an interval; we DFS over it.  b_j = (-1)^{j+1} C(g,j) * c', where c'=-C_j and A(T)=j*int(htilde_{j-1}).

Point counts: c_n = prod_i (1-alpha_i^n) = prod_{d|n} F_d, with
F_d = prod_{ord(zeta)=d} f(zeta) = Res(Phi_d, f) computed EXACTLY in Z[zeta_d].
Bucketing by (F_1,...,F_N) is equivalent to bucketing by (c_1,...,c_N).
f(zeta) = sum_{k=0}^g (-1)^k b_k zeta^k (zeta^2+q)^{g-k}, b_0=1, evaluated in Z[zeta_d].
"""
import math, sys
import numpy as np
from collections import defaultdict

# ----- cyclotomic data: Phi_d (monic, high->low int coeffs) and norm form -----
PHI = {
    1: [1, -1],
    2: [1, 1],
    3: [1, 1, 1],
    4: [1, 0, 1],
    5: [1, 1, 1, 1, 1],
    6: [1, -1, 1],
}
PHIDEG = {d: len(PHI[d]) - 1 for d in PHI}

def polymulmod(a, b, phi):
    """integer poly mult mod monic phi (all high->low lists) -> list length deg(phi)."""
    # multiply
    res = [0]*(len(a)+len(b)-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b):
                res[i+j]+=ai*bj
    # reduce mod phi (monic): while degree >= deg(phi)
    dphi=len(phi)-1
    res=res[:]  # high->low
    # length of res
    while len(res)-1>=dphi:
        lead=res[0]
        if lead!=0:
            # subtract lead*phi*T^(len(res)-1-dphi)
            shift=len(res)-1-dphi
            for j,pj in enumerate(phi):
                res[j]-=lead*pj
        res=res[1:]  # drop leading (now zero)
    # pad to length dphi
    res=[0]*(dphi-len(res))+res
    return res  # high->low, length dphi

def weight_elts(g, q, d):
    """w_k(zeta_d) in Z[zeta_d] (power basis, returned as low->high int list length phi(d)),
       for k=0..g, where w_k = (-1)^k zeta^k (zeta^2+q)^{g-k}."""
    phi=PHI[d]; dphi=PHIDEG[d]
    # zeta as poly T (high->low): [1,0]
    zeta=[1,0] if dphi>=1 else [0]
    # zeta^2+q  high->low
    z2=polymulmod(zeta,zeta,phi)         # zeta^2 mod phi (length dphi, high->low)
    z2q=z2[:]; z2q[-1]+=q                 # +q to constant term
    out=[]
    for k in range(g+1):
        zk=[1]  # zeta^0
        for _ in range(k): zk=polymulmod(zk,zeta,phi)
        pw=[1]
        for _ in range(g-k): pw=polymulmod(pw,z2q,phi)
        wk=polymulmod(zk,pw,phi)
        if k%2==1: wk=[-x for x in wk]
        # convert high->low (length dphi) to low->high
        low=wk[::-1]
        out.append(low)
    return out  # list over k of low->high int vectors length dphi

def make_norm(d):
    """return function: element (low->high int list len phi(d)) -> integer norm Res(Phi_d, elt)."""
    dphi=PHIDEG[d]
    if dphi==1:
        return lambda e: e[0]
    if d==3:  # x+y w, N=x^2-xy+y^2
        return lambda e: e[0]*e[0]-e[0]*e[1]+e[1]*e[1]
    if d==4:  # x+y i, N=x^2+y^2
        return lambda e: e[0]*e[0]+e[1]*e[1]
    if d==6:  # x+y z6, N=x^2+xy+y^2
        return lambda e: e[0]*e[0]+e[0]*e[1]+e[1]*e[1]
    # general: det of mult-by-e matrix in power basis, exact integer (Bareiss)
    phi=PHI[d]
    # companion: multiply-by-zeta matrix M (power basis 1,z,...,z^{dphi-1})
    # z * z^j = z^{j+1}; for j=dphi-1, z^dphi = -(phi[1..])... phi high->low monic
    # phi = [1, p1, p2, ..., p_dphi]; z^dphi = -(p1 z^{dphi-1}+...+p_dphi)
    tail=phi[1:]  # length dphi, high->low coeffs of z^{dphi-1..0}
    def mat_mult_by_z():
        M=[[0]*dphi for _ in range(dphi)]
        for j in range(dphi):
            if j<dphi-1:
                M[j+1][j]=1
            else:
                for i in range(dphi):
                    # z^dphi coeff of z^i is -tail[dphi-1-i]
                    M[i][j]=-tail[dphi-1-i]
        return M
    Mz=mat_mult_by_z()
    def norm(e):  # e low->high length dphi
        # build mult-by-e = sum_k e[k] Mz^k
        # Mz^k via repeated mult
        n=dphi
        # accumulate E = sum e[k] Mz^k
        E=[[0]*n for _ in range(n)]
        Pk=[[1 if i==j else 0 for j in range(n)] for i in range(n)]  # Mz^0=I
        for k in range(n):
            ek=e[k]
            if ek:
                for i in range(n):
                    for j in range(n):
                        E[i][j]+=ek*Pk[i][j]
            # Pk *= Mz
            if k<n-1:
                Pk=[[sum(Pk[i][t]*Mz[t][j] for t in range(n)) for j in range(n)] for i in range(n)]
        return int_det(E)
    return norm

def int_det(A):
    """exact integer determinant via Bareiss."""
    A=[row[:] for row in A]; n=len(A); sign=1; prev=1
    for k in range(n-1):
        if A[k][k]==0:
            piv=None
            for i in range(k+1,n):
                if A[i][k]!=0: piv=i;break
            if piv is None: return 0
            A[k],A[piv]=A[piv],A[k]; sign=-sign
        for i in range(k+1,n):
            for j in range(k+1,n):
                A[i][j]=(A[i][j]*A[k][k]-A[i][k]*A[k][j])//prev
        prev=A[k][k]
    return sign*A[n-1][n-1]

# ----------------------- recursive Weil enumeration -----------------------
def enumerate_and_bucket(g, q, N):
    rq=math.sqrt(q); m,M=-2*rq,2*rq; eps=1e-7
    ds=list(range(1,N+1))
    W={d: weight_elts(g,q,d) for d in ds}      # W[d][k] low->high vector
    norm={d: make_norm(d) for d in ds}
    binom=[math.comb(g,j) for j in range(g+1)]
    keys=[]   # list of tuples (F_1,...,F_N)
    # DFS over normalized polys htilde_j (numpy high->low) carrying b-list
    # We special-case the innermost level (j=g) with increment over b_g.
    def Fvals(bs):
        # bs = (b_1,...,b_g); compute F_d for d in ds
        out=[]
        for d in ds:
            Wd=W[d]; dphi=PHIDEG[d]
            elt=[0]*dphi
            # k=0 term b_0=1
            for t in range(dphi): elt[t]+=Wd[0][t]
            for k in range(1,g+1):
                bk=bs[k-1]
                if bk:
                    Wk=Wd[k]
                    for t in range(dphi): elt[t]+=bk*Wk[t]
            out.append(norm[d](elt))
        return tuple(out)

    nW=[0]
    def rec(j, htilde, bs):
        # htilde: monic numpy high->low of degree j-1 (real-rooted in [m,M]); add b_j..b_g
        if j==g+1:
            keys.append(Fvals(bs)); nW[0]+=1; return
        # A = j * antiderivative(htilde), monic degree j, constant 0
        A=np.polyint(htilde)*j
        A[-1]=0.0
        # critical points of A = roots of htilde (degree j-1); must all be real in [m,M].
        if len(htilde)>1:
            r=np.roots(htilde)
            realr=[z.real for z in r if abs(z.imag)<1e-6*(1+abs(z))]
            if len(realr) < len(htilde)-1:   # a complex pair => A can't have j real roots
                return
            crit=sorted(min(max(x,m),M) for x in realr)
        else:
            crit=[]
        # A(T)=c' has j real roots all in [m,M]  iff  c' lies between A's values at
        # every consecutive pair of breakpoints [m, rho_1,...,rho_{j-1}, M].
        bp=[m]+crit+[M]
        V=[np.polyval(A,x) for x in bp]
        c_lo=-1e18; c_hi=1e18
        for i in range(1,len(bp)):
            a_,b_=V[i-1],V[i]
            lo_i=a_ if a_<b_ else b_
            hi_i=b_ if a_<b_ else a_
            if lo_i>c_lo: c_lo=lo_i
            if hi_i<c_hi: c_hi=hi_i
        if c_lo>c_hi+1e-7: return
        # b_j = (-1)^{j+1} binom * c' , c' in [c_lo,c_hi]
        sgn=1 if (j%2==1) else -1   # (-1)^{j+1}
        B=binom[j]
        if sgn==1:
            blo=math.ceil(B*c_lo-eps); bhi=math.floor(B*c_hi+eps)
        else:
            blo=math.ceil(-B*c_hi-eps); bhi=math.floor(-B*c_lo+eps)
        for bj in range(blo,bhi+1):
            cp=(bj/(sgn*B))
            hj=A.copy(); hj[-1]=-cp     # htilde_j = A + C, C=-c'
            rec(j+1, hj, bs+[bj])
    rec(1, np.array([1.0]), [])
    # bucket per N' in 1..N
    return nW[0], keys

def report(g, qs, Nmax):
    print(f"# g={g}: minimal N so that (c_1..c_N) determines isogeny class?",flush=True)
    head="   q     #Weil " + " ".join(f"N={n}" for n in range(1,Nmax+1))
    print(head,flush=True)
    for q in qs:
        nW, keys = enumerate_and_bucket(g,q,Nmax)
        row=[f"{q:>4}", f"{nW:>9}"]
        for n in range(1,Nmax+1):
            seen=set(); coll=0
            for key in keys:
                kp=key[:n]
                if kp in seen: coll+=1
                else: seen.add(kp)
            inj = (len(seen)==nW)
            row.append(("inj" if inj else f"{nW-len(seen)}c"))
        print(" ".join(row),flush=True)

if __name__=="__main__":
    g=int(sys.argv[1]) if len(sys.argv)>1 else 3
    Nmax=int(sys.argv[2]) if len(sys.argv)>2 else g
    qs=[int(x) for x in sys.argv[3:]] if len(sys.argv)>3 else [3,4,5,7,9]
    report(g, qs, Nmax)
