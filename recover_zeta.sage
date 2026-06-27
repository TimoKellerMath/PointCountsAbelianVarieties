# recover_zeta.sage
#
# Sage implementation of the algorithm from
#
#   S. Chidambaram, T. Keller,
#   "Point counts of abelian varieties over finite fields determining
#    their zeta function".
#
# Given the dimension g, the field size q, and the g point counts
#
#       c_i = #A(F_{q^i}),   1 <= i <= g,
#
# of an abelian variety A/F_q with q > Q(g), the algorithm recovers the
# L-polynomial f_A(T) = prod_i (1 - alpha_i T) = a_0 + a_1 T + ... + a_{2g} T^{2g}
# (the reverse characteristic polynomial of Frobenius), and hence the zeta
# function and the isogeny class of A.
#
# Notation follows the paper:
#   beta_i = alpha_i^{-1},          |beta_i| = q^{-1/2}
#   s_n    = sum_i beta_i^n          (power sums; n-th power sum of inverse Frobenius eigenvalues)
#   e_n    = elem. symmetric of deg n in the beta_i
#   L_m    = log(q^{g m} / c_m) = sum_{j>=1} s_{jm}/j          (Lemma "counts-to-sums")
#
# Key facts used:
#   * q^n s_n in Z, so s_n is recovered by rounding q^n*(approx) to the
#     nearest integer once the additive error is < (1/2) q^{-n}   (Lemma "integrality").
#   * Functional equation  e_{g+n} = q^{-n} e_{g-n}              (Lemma "functional-eq").
#   * Newton's identities relate the e_n and s_n                 (Lemma "sym-identities").
#
# The recovery splits into two ranges, exactly as in the proof of the main theorem:
#   small range  1 <= i <= g/2 : truncated Moebius inversion of the L_m  (Lemma "small-i")
#   large range  g/2 < i <= g  : an induction that sharpens the estimate of
#                                s_{2i} via the functional equation        (Lemma "induction-step")


# ---------------------------------------------------------------------------
# The explicit constant Q(g) of the main theorem.
# ---------------------------------------------------------------------------
def Q_bound(g):
    r"""
    The explicit constant Q(g) = (16 g^3 p(2g))^{2g+2} from the main theorem,
    above which the algorithm is *proven* to recover f_A.  (The bound is far
    from optimal; in practice recovery succeeds for much smaller q.)
    """
    g = Integer(g)
    D = 16 * g**3 * number_of_partitions(2*g)
    return D**(2*g + 2)


# ---------------------------------------------------------------------------
# Point counts of an abelian variety from its L-polynomial (for testing).
# ---------------------------------------------------------------------------
def point_counts_from_Lpoly(f_A, N):
    r"""
    Return the list [ #A(F_{q^n}) : 1 <= n <= N ] for the L-polynomial f_A.

    Uses  c_n = prod_i (1 - alpha_i^n) = prod_{zeta^n = 1} f_A(zeta)
              = Res_T(T^n - 1, f_A(T)),
    which is an exact integer computation.
    """
    R = f_A.parent()
    T = R.gen()
    return [Integer((T**n - 1).resultant(f_A)) for n in range(1, N + 1)]


# ---------------------------------------------------------------------------
# Elementary symmetric functions e_0,...,e_N from power sums s_1,...,s_N
# via Newton's identities  n e_n = sum_{i=1}^n (-1)^{i-1} e_{n-i} s_i.
# ---------------------------------------------------------------------------
def _elem_from_power(sval, N):
    r"""
    Given a dictionary ``sval`` with sval[k] = s_k for 1 <= k <= N (entries may
    be exact rationals or real approximations), return the list [e_0, ..., e_N].
    """
    e = [None] * (N + 1)
    e[0] = ZZ(1)
    for n in range(1, N + 1):
        acc = sval[1] * 0  # zero in the right parent (handles mixed QQ/RR)
        for i in range(1, n + 1):
            acc = acc + (-1)**(i - 1) * e[n - i] * sval[i]
        e[n] = acc / n
    return e


# ---------------------------------------------------------------------------
# The main algorithm.
# ---------------------------------------------------------------------------
def recover_Lpoly(g, q, counts, prec=None, verbose=False):
    r"""
    Recover the L-polynomial f_A(T) in ZZ[T] from the g point counts.

    INPUT:

    - ``g``      -- dimension of the abelian variety
    - ``q``      -- size of the finite field (a prime power)
    - ``counts`` -- list [c_1, ..., c_g] with c_i = #A(F_{q^i})
    - ``prec``   -- (optional) working real precision in bits; chosen
                    automatically if omitted
    - ``verbose``-- print the recovered power sums s_1, ..., s_g

    OUTPUT:

    the L-polynomial f_A in ZZ[T], with a_0 = 1 and a_{2g} = q^g.
    """
    g = Integer(g)
    q = Integer(q)
    if len(counts) < g:
        raise ValueError("need g = %s point counts, got %s" % (g, len(counts)))
    counts = [Integer(c) for c in counts]

    # Working precision: q^i*(approx) must be accurate to < 1/2, and the
    # multiplier q^i is as large as q^g, so we need well over g*log2(q) bits.
    if prec is None:
        prec = 256 + 2 * Integer(g) * q.nbits()
    Rf = RealField(prec)
    logq = Rf(q).log()

    # L_m = log(q^{g m} / c_m) = g*m*log q - log c_m, known exactly for m <= g.
    L = {m: g * m * logq - Rf(counts[m - 1]).log() for m in range(1, g + 1)}

    def round_to_power(approx, i):
        # s_i = m q^{-i} with m the nearest integer to q^i * approx (Lemma "integrality").
        m = (q**i * approx).round()
        return QQ(m) / q**i

    s = {}          # exact values s_i (rationals m/q^i) once determined
    s_approx = {}   # best current estimate of s_j (exact rational or real)

    half = g // 2   # floor(g/2)

    # -- Small range 1 <= i <= g/2 : truncated Moebius inversion (Lemma "small-i").
    for i in range(1, half + 1):
        approx = sum((moebius(j) / j) * L[j * i]
                     for j in range(1, g // i + 1) if j * i <= g)
        s[i] = round_to_power(approx, i)
        s_approx[i] = s[i]

    # -- Seed estimates for the large range:  s_j ~ L_j for g/2 < j <= g
    #    (Lemma "seed"; sharpened below).
    for j in range(half + 1, g + 1):
        s_approx[j] = L[j]

    # Compute the doubled-power-sum estimate s_hat_m for m > g, by solving the
    # functional equation e_m = q^{-(m-g)} e_{2g-m} for the top power sum s_m
    # that occurs (linearly) in e_m.  Concretely, with
    #   e_m = e_m^{(no s_m)} + (-1)^{m-1} s_m / m   and   e_m = q^{-(m-g)} e_{2g-m},
    # one gets
    #   s_m / m = (-1)^m ( e_m^{(no s_m)} - q^{-(m-g)} e_{2g-m} ).
    # This is formula (sm-formula) of the paper; the s_k it uses (k < m) are the
    # current estimates in s_approx.
    def s_hat(m):
        m = Integer(m)
        n = m - g                       # >= 1 since m > g
        ev = _elem_from_power(s_approx, m - 1)   # e_0, ..., e_{m-1} from s_1..s_{m-1}
        # e_m without the top term (-1)^{m-1} s_m / m :
        e_m_no_top = sum((-1)**(i - 1) * ev[m - i] * s_approx[i]
                         for i in range(1, m)) / m
        e_2gm = ev[2 * g - m]           # 2g - m <= m - 1, already computed
        return m * (-1)**m * (e_m_no_top - q**(-n) * e_2gm)

    # -- Large range g/2 < i <= g, processed in increasing order
    #    (Lemma "induction-step" + the rounding step of the main proof).
    for i in range(half + 1, g + 1):
        # Sharpen s_{2i-1} and s_{2i} (those > g) for use here and at later steps.
        # Compute the odd index first: it needs only indices <= 2i-2, while the
        # even index m = 2i needs s_approx[2i-1], which we set here.
        if 2 * i - 1 > g:
            s_approx[2 * i - 1] = s_hat(2 * i - 1)
        s_approx[2 * i] = s_hat(2 * i)

        # Recover s_i:  s_i = L_i - (1/2) s_{2i} - sum_{j>=3} s_{ji}/j, and the
        # tail is < (1/4) q^{-i}, absorbed by rounding (proof of main theorem).
        approx = L[i] - s_approx[2 * i] / 2
        s[i] = round_to_power(approx, i)
        s_approx[i] = s[i]              # now exact for subsequent steps

    if verbose:
        for i in range(1, g + 1):
            print("  s_%s = %s" % (i, s[i]))

    # -- Reconstruct f_A from s_1, ..., s_g.
    # e_1, ..., e_g from Newton; e_{g+n} = q^{-n} e_{g-n} from the functional eq.
    e = _elem_from_power(s, g)                       # e_0, ..., e_g (exact in QQ)
    for n in range(1, g + 1):
        e.append(q**(-n) * e[g - n])                 # e_{g+1}, ..., e_{2g}

    # a_k = (-1)^k * q^g * e_{2g-k}   (so a_0 = 1, a_{2g} = q^g).
    RT = PolynomialRing(ZZ, 'T')
    T = RT.gen()
    coeffs = [(-1)**k * q**g * e[2 * g - k] for k in range(0, 2 * g + 1)]
    for k, a in enumerate(coeffs):
        if a not in ZZ:
            raise ArithmeticError("recovered coefficient a_%s = %s is not an "
                                  "integer; q is likely below the required bound" % (k, a))
    return RT([ZZ(a) for a in coeffs])


# ---------------------------------------------------------------------------
# Convenience: full check that a recovered f_A reproduces the input counts.
# ---------------------------------------------------------------------------
def verify_recovery(g, q, f_true):
    r"""
    Given a true L-polynomial ``f_true`` of an abelian variety of dimension g
    over F_q (constant term 1; e.g. ``W.reverse()`` for a monic Weil polynomial
    ``W`` returned by ``WeilPolynomials``), recompute its g point counts, run the
    recovery, and report whether

      (a) the recovered f_A reproduces the same point counts c_1,...,c_g, and
      (b) the recovered f_A equals f_true.

    Polynomials are compared by their coefficient lists, so that the comparison
    does not depend on the name of the variable.  Below the working threshold on
    q the recovery may fail outright (non-integral rounding, ``f_recovered``
    is ``None``); when it succeeds but (b) fails while (a) holds, q is small
    enough that distinct isogeny classes share the first g point counts -- see
    Remark "optimality".
    """
    counts = point_counts_from_Lpoly(f_true, g)
    try:
        f_rec = recover_Lpoly(g, q, counts)
    except ArithmeticError:
        # rounding produced non-integral coefficients: q below the working bound
        f_rec = None
    counts_rec = point_counts_from_Lpoly(f_rec, g) if f_rec is not None else None
    return {
        "counts": counts,
        "f_true": f_true,
        "f_recovered": f_rec,
        "counts_match": counts_rec == counts,
        "exact_match": f_rec is not None and f_rec.list() == f_true.list(),
    }


# ---------------------------------------------------------------------------
# Demo / smoke test, using Sage's enumeration of Weil polynomials.
# ---------------------------------------------------------------------------
def run_demo(g_range=(1, 3), q_list=None, sample=150):
    r"""
    For each dimension g and field size q, sample abelian varieties (via Sage's
    ``WeilPolynomials``) spread across the enumeration, run the recovery, and
    report the exact-recovery rate.

    Note the *proven* bound Q(g) is astronomically large; in practice recovery
    succeeds for every variety once q is moderately large (well below Q(g)).
    Failures at small q are expected and concentrate near the boundary of the
    Weil region, where the inverse-Frobenius power sums are near-maximal.
    """
    from sage.rings.polynomial.weil.weil_polynomials import WeilPolynomials
    import itertools
    if q_list is None:
        q_list = [121, 1009, 5003]
    for g in range(g_range[0], g_range[1] + 1):
        print("g = %s   (proven bound Q(g) = %s)" % (g, Q_bound(g)))
        for q in q_list:
            pool = list(itertools.islice(WeilPolynomials(2 * g, q), 4000))
            step = max(1, len(pool) // sample)
            fs = pool[::step]
            total = ok_counts = ok_exact = fails = 0
            for W in fs:
                res = verify_recovery(g, q, W.reverse())   # L-polynomial convention
                total += 1
                ok_counts += 1 if res["counts_match"] else 0
                ok_exact += 1 if res["exact_match"] else 0
                fails += 1 if res["f_recovered"] is None else 0
            print("  q = %5s : %3s samples, exact %3s/%-3s, recovery failed %3s "
                  "(too far below Q(g))" % (q, total, ok_exact, total, fails))


# ---------------------------------------------------------------------------
# Usage (from a Sage session or `sage` prompt):
#
#   sage: load("recover_zeta.sage")
#
#   # Recover f_A from point counts c_1, ..., c_g of an abelian variety A/F_q:
#   sage: f_A = recover_Lpoly(g, q, [c_1, ..., c_g])
#
#   # End-to-end check on Sage's enumerated Weil polynomials:
#   sage: run_demo(g_range=(1, 3), q_list=[121, 1009, 5003])
# ---------------------------------------------------------------------------
