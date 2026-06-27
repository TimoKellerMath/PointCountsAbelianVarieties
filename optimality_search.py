#!/usr/bin/env python3
"""
Do N point counts determine the isogeny class of a g=3 abelian variety over F_q?

This script answers the question by an *exhaustive* and *self-contained* search:
it enumerates every q-Weil polynomial of dimension 3 from scratch -- it does NOT
read any precomputed table (in particular it is independent of the LMFDB, whose
g=3 data is complete only for q <= 25) -- buckets them by their first N point
counts (c_1,...,c_N), and reports any collision (two distinct isogeny classes
with identical counts).  Because the search ranges over a finite box of integer
coefficients, it terminates and is provably complete for every q; the only limit
is running time.  See the bottom of the file for a `--verify` mode that re-runs
the enumeration in exact integer arithmetic to certify there is no floating-point
error at the boundary of the Weil region.

Why this enumeration is exhaustive
----------------------------------
The characteristic polynomial of Frobenius of an abelian threefold A/F_q is a
degree-6 q-Weil polynomial
   P(T) = prod_i (T^2 - beta_i T + q),     i = 1,2,3,
whose roots come in conjugate pairs alpha_i, q/alpha_i of absolute value sqrt q.
P is determined by the real Weil (or "trace") polynomial
   h(T) = prod_i (T - beta_i) = T^3 - b1 T^2 + b2 T - b3,
where beta_i = alpha_i + q/alpha_i is the i-th Frobenius trace and lies in the
Hasse-Weil interval [-2 sqrt q, 2 sqrt q].  Since h has integer coefficients, the
symmetric functions are bounded:
   |b1| = |sum beta_i|       <= 3 * 2 sqrt q   =  6 sqrt q,
   |b2| = |sum_{i<j} beta_i beta_j| <= 3 * (2 sqrt q)^2 = 12 q,
   |b3| = |prod beta_i|      <= (2 sqrt q)^3   =  8 q^{3/2}.
So every isogeny class corresponds to a lattice point (b1,b2,b3) in an explicit
finite box.  Conversely we keep exactly those (b1,b2,b3) whose cubic has all three
roots real and inside [-2 sqrt q, 2 sqrt q]; this is precisely the set of degree-6
q-Weil polynomials.  Not every q-Weil polynomial is the characteristic polynomial
of an abelian variety (Honda-Tate imposes further p-adic conditions), so the box
is a SUPERSET of the actual isogeny classes.  That is exactly what we want for the
injectivity direction: if (c_1,...,c_N) is injective on the whole box, it is a
fortiori injective on isogeny classes -- no completeness/realizability input is
needed.  (For a NON-injective q, e.g. q <= 13, one still has to check that a
colliding pair is realized by genuine abelian varieties; in the range q <= 25
this is confirmed against the LMFDB -- see verify_g3_family.sage.)

Coefficient dictionary (h <-> P) and point counts
-------------------------------------------------
From P(T) = prod_i (T^2 - beta_i T + q) one gets, with P normalized as
   P(T) = T^6 + a1 T^5 + a2 T^4 + a3 T^3 + q a2 T^2 + q^2 a1 T + q^3,
the relations
   a1 = -b1,  a2 = 3q + b2,  a3 = -2q b1 - b3.
Point counts are resultants with the cyclotomic polynomials:
   c_n = #A(F_{q^n}) = prod_i (1 - alpha_i^n) = prod_{zeta^n = 1} P(zeta).
In particular
   c1 = P(1),                    c2 = P(1) P(-1),
   c3 = P(1) |P(omega)|^2,  ...  (omega a primitive cube root of unity),
and each c_n is a rational integer.
"""
import math, sys, cmath
from collections import defaultdict

def g0(t, b1, b2):
    """The depressed cubic h(t) + b3 = t^3 - b1 t^2 + b2 t (i.e. h with b3 = 0).
    The roots of h(T) = T^3 - b1 T^2 + b2 T - b3 are the solutions of g0(t) = b3,
    so g0 turns the 'three real roots in [m, M]' conditions into bounds on b3."""
    return t*t*t - b1*t*t + b2*t

def weil_cubics(q):
    """Yield (b1, b2, b3) for every integer real-Weil cubic, i.e. every monic
    integer cubic h(T) = T^3 - b1 T^2 + b2 T - b3 whose three roots are real and
    lie in [m, M] = [-2 sqrt q, 2 sqrt q].  These are in bijection with the
    degree-6 q-Weil polynomials of dimension 3 (see the module docstring).

    For fixed (b1, b2) the admissible b3 form a contiguous integer interval, found
    as follows.  Write g0(t) = t^3 - b1 t^2 + b2 t, so h(t) = g0(t) - b3.  The
    critical points of g0 (and of h) are t_minus < t_plus, the roots of
    g0'(t) = 3 t^2 - 2 b1 t + b2; here t_minus is the local max and t_plus the
    local min.  Then:
      * three real roots          <=>  g0(t_plus) <= b3 <= g0(t_minus)
                                       (b3 between the local-min and local-max values);
      * smallest root >= m        <=>  h(m) <= 0  <=>  b3 >= g0(m),   and  t_minus >= m;
      * largest  root <= M        <=>  h(M) >= 0  <=>  b3 <= g0(M),   and  t_plus  <= M.
    Intersecting the three lower bounds and the three upper bounds gives the b3
    interval [b3lo, b3hi].  (Everything here is in floating point with a small eps
    slack; the `--verify` mode below re-derives the same lists exactly.)
    """
    rq = math.sqrt(q)
    m, M = -2*rq, 2*rq
    Mb1 = int(math.floor(6*rq)) + 1     # |b1| <= 6 sqrt q
    Mb2 = 12*q + 2                      # |b2| <= 12 q
    eps = 1e-7
    for b1 in range(-Mb1, Mb1+1):
        for b2 in range(-Mb2, Mb2+1):
            disc = b1*b1 - 3*b2          # discriminant of g0'; <0 => g0 monotone => <3 real roots
            if disc < 0:
                continue
            s = math.sqrt(disc)
            tminus = (b1 - s)/3.0       # local max location
            tplus  = (b1 + s)/3.0       # local min location
            if tminus < m - eps or tplus > M + eps:   # a critical point fell outside [m, M]
                continue
            lo = max(g0(tplus, b1, b2), g0(m, b1, b2))   # b3 >= max(local-min value, g0(m))
            hi = min(g0(tminus, b1, b2), g0(M, b1, b2))  # b3 <= min(local-max value, g0(M))
            b3lo = int(math.ceil(lo - eps))
            b3hi = int(math.floor(hi + eps))
            for b3 in range(b3lo, b3hi+1):
                yield (b1, b2, b3)

def counts(b1, b2, b3, q, N):
    """Return ((c_1, ..., c_N), (a1, a2, a3)) for the cubic (b1, b2, b3).

    c_1 and c_2 are computed with exact integer arithmetic (P has integer
    coefficients, evaluated at +-1).  For n >= 3 we evaluate P at the n-th roots
    of unity in floating point and round the product to the nearest integer; the
    product prod_{zeta^n = 1} P(zeta) is a rational integer (a resultant), so the
    rounding is harmless for the moderate q used here.
    """
    a1, a2, a3 = -b1, 3*q + b2, -2*q*b1 - b3
    P = [1, a1, a2, a3, q*a2, q*q*a1, q**3]    # P(T) coefficients, high -> low degree
    def Pval_complex(z):
        r = 0+0j
        for c in P:
            r = r*z + c
        return r
    def Pval_int(z):
        r = 0
        for c in P:
            r = r*z + c
        return r
    cs = []
    P1 = Pval_int(1)
    for n in range(1, N+1):
        if n == 1:
            cs.append(P1)                       # c1 = P(1)  (exact)
        elif n == 2:
            cs.append(P1 * Pval_int(-1))        # c2 = P(1) P(-1)  (exact)
        else:
            val = 1.0+0j                        # c_n = prod over n-th roots of unity of P(zeta)
            for k in range(n):
                val *= Pval_complex(cmath.exp(2j*math.pi*k/n))
            cs.append(int(round(val.real)))
    return tuple(cs), (a1, a2, a3)

def study(q, N=2):
    """Enumerate all dimension-3 q-Weil polynomials, bucket them by (c_1,...,c_N),
    and return (number of Weil polynomials, number of distinct count-vectors,
    {count-vector: list of colliding cubics}).  (c_1,...,c_N) is injective on
    isogeny classes iff there are no collisions, i.e. #buckets == #Weil polys."""
    buckets = defaultdict(list)
    nW = 0
    for (b1, b2, b3) in weil_cubics(q):
        nW += 1
        key, a = counts(b1, b2, b3, q, N)
        buckets[key].append((b1, b2, b3, a))
    colls = {k: v for k, v in buckets.items() if len(v) > 1}
    return nW, len(buckets), colls

def is_ordinary(a3, q):
    """An abelian variety is ordinary iff its p-rank is maximal, equivalently iff
    the middle coefficient a3 of P (the coefficient of T^g = T^3) is prime to the
    characteristic p.  Here a3 is passed in and p is the unique prime dividing q."""
    pp = None                               # smallest prime factor of q (= the characteristic p)
    n = q
    d = 2
    while d*d <= n:
        if n % d == 0:
            pp = d
            break
        d += 1
    if pp is None:
        pp = n
    return a3 % pp != 0

# ---------------------------------------------------------------------------
# Exact-arithmetic certification of weil_cubics (no floating point).
#
# weil_cubics uses math.sqrt and a small eps, so in principle a cubic whose
# largest root sits exactly on the boundary +-2 sqrt q could be mis-classified.
# The functions below redo the membership test with pure integer arithmetic and
# are used by `--verify` to confirm the two enumerations agree.  Every boundary
# comparison has the shape  (integer)  vs  (integer) * sqrt(q)  and is resolved
# exactly by isolating the surd and squaring.
# ---------------------------------------------------------------------------
def _sgn(x):
    return (x > 0) - (x < 0)

def _sign_P_minus_R_sqrt(P, R, q):
    """Exact sign of  P - R*sqrt(q)  for integers P, R and integer q >= 0."""
    if R == 0:
        return _sgn(P)
    if R > 0:
        if P <= 0:
            return -1                       # P <= 0 < R sqrt q
        return _sgn(P*P - R*R*q)            # both > 0: square
    else:
        if P >= 0:
            return 1                        # P >= 0 > R sqrt q
        return _sgn(R*R*q - P*P)            # both < 0: square (flips)

def _u_sqrt_ge_v(u, v, q):
    """Exact truth of  u*sqrt(q) >= v  (i.e. v - u*sqrt q <= 0)."""
    return _sign_P_minus_R_sqrt(v, u, q) <= 0

def _sqrt_le_b_sqrt_plus_c(A, B, C, q):
    """Exact truth of  sqrt(A) <= B*sqrt(q) + C,  for integer A >= 0."""
    if _sign_P_minus_R_sqrt(-C, B, q) > 0:           # right-hand side B sqrt q + C < 0
        return False
    # both sides >= 0; square: A <= B^2 q + C^2 + 2 B C sqrt q
    return _sign_P_minus_R_sqrt(A - B*B*q - C*C, 2*B*C, q) <= 0

def _disc_cubic(b1, b2, b3):
    """Discriminant of T^3 - b1 T^2 + b2 T - b3; >= 0 iff all three roots are real."""
    return 18*b1*b2*b3 - 4*b1**3*b3 + b1*b1*b2*b2 - 4*b2**3 - 27*b3*b3

def weil_cubics_exact(q):
    """Exactly the same set as weil_cubics(q), recomputed in integer arithmetic.

    Conditions for h(T) = T^3 - b1 T^2 + b2 T - b3 to have three real roots, all
    in [m, M] = [-2 sqrt q, 2 sqrt q]:
      (1) disc(h) >= 0                          (all roots real);
      (2) h(M) >= 0  and  h(m) <= 0             (the interval contains the roots), where
          h(+-2 sqrt q) = +-(8q + 2 b2) sqrt q - (4 q b1 + b3),  so with
          U = 8q + 2 b2 and V = 4 q b1 + b3 these read  U sqrt q >= V  and  U sqrt q >= -V;
      (3) the critical points t_minus, t_plus = (b1 -+ sqrt D)/3, D = b1^2 - 3 b2,
          lie in [m, M], i.e.  sqrt D <= 6 sqrt q - b1  and  sqrt D <= 6 sqrt q + b1.
    """
    rq = math.sqrt(q)
    Mb1 = int(math.floor(6*rq)) + 1
    Mb2 = 12*q + 2
    Mb3 = int(math.floor((2*rq)**3)) + 2     # |b3| <= 8 q^{3/2}
    for b1 in range(-Mb1, Mb1+1):
        for b2 in range(-Mb2, Mb2+1):
            D = b1*b1 - 3*b2
            if D < 0:                        # no real critical points => < 3 real roots
                continue
            U = 8*q + 2*b2
            for b3 in range(-Mb3, Mb3+1):
                if _disc_cubic(b1, b2, b3) < 0:          # (1)
                    continue
                V = 4*q*b1 + b3
                if not _u_sqrt_ge_v(U, V, q):            # (2) h(M) >= 0
                    continue
                if not _u_sqrt_ge_v(U, -V, q):           # (2) h(m) <= 0
                    continue
                if not _sqrt_le_b_sqrt_plus_c(D, 6, -b1, q):   # (3) t_plus  <= M
                    continue
                if not _sqrt_le_b_sqrt_plus_c(D, 6,  b1, q):   # (3) t_minus >= m
                    continue
                yield (b1, b2, b3)

def verify(qs):
    """Certify that the floating-point enumeration weil_cubics agrees, set for
    set, with the exact integer enumeration weil_cubics_exact, for each q in qs.
    Returns True iff every q matches.  (Exact enumeration loops the full b3 box,
    so it is O(q^3) and meant for a sanity range such as q <= 25.)"""
    ok = True
    print(f"{'q':>4} {'float':>9} {'exact':>9} {'agree?':>8}", flush=True)
    for q in qs:
        A = set(weil_cubics(q))
        B = set(weil_cubics_exact(q))
        agree = (A == B)
        ok = ok and agree
        print(f"{q:>4} {len(A):>9} {len(B):>9} {'YES' if agree else 'NO':>8}", flush=True)
        if not agree:
            print(f"     only in float: {sorted(A-B)[:6]}", flush=True)
            print(f"     only in exact: {sorted(B-A)[:6]}", flush=True)
    return ok

if __name__ == "__main__":
    # Prime powers up to 49; matches the range quoted in the paper.  (c1,c2) is
    # non-injective for q <= 13 and injective for every prime power 16 <= q <= 49.
    QS_DEFAULT = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25,
                  27, 29, 31, 32, 37, 41, 43, 47, 49]
    args = sys.argv[1:]
    import sys
    print(sys.argv)

    # `--verify [q ...]`: certify the enumeration in exact integer arithmetic.
    if args and args[0] == "--verify":
        vqs = [int(x) for x in args[1:]] or [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25]
        sys.exit(0 if verify(vqs) else 1)

    N = 2
    # qs = QS_DEFAULT
    # qs = [n for n in range(2, 252) if is_prime_power(n)]
    qs = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53, 59, 61, 64, 67, 71, 73, 79, 81, 83, 89, 97, 101, 103, 107, 109, 113, 121, 125, 127, 128, 131, 137, 139, 149, 151, 157, 163, 167, 169, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 243, 251]
    # qs = [397]

    if args and args[0].startswith("N="):
        N = int(args[0][2:]); args = args[1:]
    if args:
        qs = [int(x) for x in args]
    print(f"# g=3, N={N}: does (c1..cN) determine the isogeny class?", flush=True)
    print(f"{'q':>4} {'#Weil':>9} {'#images':>9} {'#coll':>7} {'maxfib':>7} {'inject?':>8}", flush=True)
    for q in qs:
        nW, nI, colls = study(q, N)
        maxfib = max((len(v) for v in colls.values()), default=1)
        inj = "YES" if nW == nI else "NO"
        print(f"{q:>4} {nW:>9} {nI:>9} {len(colls):>7} {maxfib:>7} {inj:>8}", flush=True)
        shown = 0
        for key, members in sorted(colls.items()):
            if shown >= 3: break
            tags = []
            for (b1,b2,b3,a) in members:
                tags.append(f"a={a}{'(ord)' if is_ordinary(a[2],q) else ''}")
            print(f"      collide (c1..cN)={key}: " + " | ".join(tags), flush=True)
            shown += 1


'''
Output of running
sage optimality_search.py

# g=3, N=2: does (c1..cN) determine the isogeny class?
   q     #Weil   #images   #coll  maxfib  inject?
   2       215       183      29       3       NO
      collide (c1..cN)=(3, 45): a=(-1, 0, -1)(ord) | a=(-2, 0, 4)
      collide (c1..cN)=(3, 63): a=(-1, 1, -4) | a=(-2, 1, 1)(ord)
      collide (c1..cN)=(4, 32): a=(0, -1, -2) | a=(-1, -1, 3)(ord)
   3       677       607      69       3       NO
      collide (c1..cN)=(14, 588): a=(-1, 0, -4)(ord) | a=(-2, 0, 6)
      collide (c1..cN)=(15, 615): a=(-1, 0, -3) | a=(-2, 0, 7)(ord)
      collide (c1..cN)=(15, 735): a=(-1, 1, -7)(ord) | a=(-2, 1, 3)
   4      1641      1519     122       2       NO
      collide (c1..cN)=(36, 5184): a=(-2, 5, -20) | a=(-3, 5, -3)(ord)
      collide (c1..cN)=(38, 2736): a=(-1, -2, 0) | a=(-2, -2, 17)(ord)
      collide (c1..cN)=(39, 3159): a=(-1, -1, -4) | a=(-2, -1, 13)(ord)
   5      2953      2805     148       2       NO
      collide (c1..cN)=(87, 13311): a=(-1, -1, -7)(ord) | a=(-2, -1, 19)(ord)
      collide (c1..cN)=(88, 14432): a=(-1, 0, -12)(ord) | a=(-2, 0, 14)(ord)
      collide (c1..cN)=(89, 14507): a=(-1, 0, -11)(ord) | a=(-2, 0, 15)
   7      7979      7795     184       2       NO
      collide (c1..cN)=(271, 113007): a=(-1, 0, -23)(ord) | a=(-2, 0, 27)(ord)
      collide (c1..cN)=(274, 117820): a=(-1, 1, -28) | a=(-2, 1, 22)(ord)
      collide (c1..cN)=(275, 117975): a=(-1, 1, -27)(ord) | a=(-2, 1, 23)(ord)
   8     11823     11653     170       2       NO
      collide (c1..cN)=(426, 270936): a=(-1, 2, -40) | a=(-2, 2, 25)(ord)
      collide (c1..cN)=(427, 271145): a=(-1, 2, -39)(ord) | a=(-2, 2, 26)
      collide (c1..cN)=(429, 279279): a=(-1, 3, -46) | a=(-2, 3, 19)(ord)
   9     17121     16967     154       2       NO
      collide (c1..cN)=(624, 559104): a=(-1, 3, -54) | a=(-2, 3, 28)(ord)
      collide (c1..cN)=(625, 559375): a=(-1, 3, -53)(ord) | a=(-2, 3, 29)(ord)
      collide (c1..cN)=(664, 488704): a=(0, -3, -36) | a=(-1, -3, 46)(ord)
  11     30543     30451      92       2       NO
      collide (c1..cN)=(1243, 1676807): a=(0, -3, -53)(ord) | a=(-1, -3, 69)(ord)
      collide (c1..cN)=(1244, 1676912): a=(0, -3, -52)(ord) | a=(-1, -3, 70)(ord)
      collide (c1..cN)=(1245, 1677015): a=(0, -3, -51)(ord) | a=(-1, -3, 71)(ord)
  13     50371     50353      18       2       NO
      collide (c1..cN)=(2098, 4762460): a=(0, -1, -86)(ord) | a=(-1, -1, 84)(ord)
      collide (c1..cN)=(2099, 4762631): a=(0, -1, -85)(ord) | a=(-1, -1, 85)(ord)
      collide (c1..cN)=(2100, 4762800): a=(0, -1, -84)(ord) | a=(-1, -1, 86)(ord)
  16     94363     94363       0       1      YES
  17    112283    112283       0       1      YES
  19    156589    156589       0       1      YES
  23    277517    277517       0       1      YES
  25    357691    357691       0       1      YES
  27    448739    448739       0       1      YES
  29    555843    555843       0       1      YES
  31    678957    678957       0       1      YES
  32    746693    746693       0       1      YES
  37   1153875   1153875       0       1      YES
  41   1569637   1569637       0       1      YES
  43   1810805   1810805       0       1      YES
  47   2364089   2364089       0       1      YES
  49   2682631   2682631       0       1      YES
  53   3389675   3389675       0       YES
  59   4675707   4675707       0       YES
  61   5167277   5167277       0       YES
  64   5973195   5973195       0       YES
  67   6846631   6846631       0       YES
  71   8147047   8147047       0       YES
  73   8855295   8855295       0       YES
  79  11222313  11222313       0       YES
  81  12104353  12104353       0       YES
  83  13014767  13014767       0       YES
  89  16045439  16045439       0       YES
  97  20772343  20772343       0       1      YES
 101  23449327  23449327       0       1      YES
 103  24870063  24870063       0       1      YES
 107  27880975  27880975       0       YES
 109  29473619  29473619       0       YES
 113  32839031  32839031       0       YES
 121  40332557  40332557       0       YES
 125  44450147  44450147       0       YES
 127  46617799  46617799       0       YES
 128  47727465  47727465       0       YES
 131  51162221  51162221       0       YES
 137  58518933  58518933       0       YES
 139  61119049  61119049       0       YES
 149  75281219  75281219       0       1      YES
 151  78353223  78353223       0       1      YES
 157  88069295  88069295       0       1      YES
 163  98556325  98556325       0       1      YES
 167 105990753 105990753       0       1      YES
 169 109868493 109868493       0       1      YES
 173 117830375 117830375       0       1      YES
 179 130519335 130519335       0       1      YES
 181 134943037 134943037       0       1      YES
 191 158567025 158567025       0       1      YES
 193 163600239 163600239       0       1      YES
 197 173984493 173984493       0       1      YES
 199 179337533 179337533       0       1      YES
 211 213775187 213775187       0       1      YES
 223 252360195 252360195       0       1      YES
 227 266185615 266185615       0       1      YES
 229 273283379 273283379       0       1      YES
 233 287854771 287854771       0       1      YES
 239 310669019 310669019       0       1      YES
 241 318534461 318534461       0       1      YES
 243 326530461 326530461       0       1      YES
 251 359852405 359852405       0       1      YES 
 397 1423855571 1423855571     0       1      YES
'''