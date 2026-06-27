# Point counts of abelian varieties over finite fields determining their zeta function

Accompanying code for the paper

> Shiva Chidambaram and Timo Keller,
> *Point counts of abelian varieties over finite fields determining their zeta function*, 2026.
> Repository: <https://github.com/TimoKellerMath/PointCountsAbelianVarieties>

This repository contains the LaTeX source (`pointcountzeta.tex`), the Sage/Python
scripts that implement the paper's algorithm and verify its computational claims, and
a Lean 4 / Mathlib formalization of Theorem 1.1 in `PointCountZeta/`.

## Requirements

- **SageMath** (tested with 10.9) for the `.sage` scripts.
- **Python 3** for the `.py` scripts; `weil_general.py` additionally needs **NumPy**.

## Scripts

Run a Sage script with `sage <script>` and a Python script with `python3 <script>`.

### Main algorithm

- **`recover_zeta.sage`** — Sage implementation of the paper's algorithm. Given the
  dimension `g`, the field size `q`, and the `g` point counts `c_i = #A(F_{q^i})`
  (`1 ≤ i ≤ g`) of an abelian variety `A/F_q` with `q > Q(g)`, it recovers the
  L-polynomial `f_A(T) = ∏_i (1 − α_i T)` (the reverse characteristic polynomial of
  Frobenius), and hence the zeta function and the isogeny class of `A`.

### Optimality of the number of point counts (Proposition 7.1 and surrounding remarks)

These study, for given `g`, the smallest `N` such that the first `N` point counts
`(c_1,…,c_N)` already determine the isogeny class for all large `q`.

- **`optimality_search.py`** — self-contained, pure-Python exhaustive search (no external
  data, no Sage); this is the script that establishes the `g = 3` optimality claims in the
  paper. For `g = 3` it enumerates every degree-6 `q`-Weil polynomial from a finite integer
  box of trace-polynomial coefficients, buckets them by `(c_1,…,c_N)`, and reports
  collisions. It shows `(c_1,c_2)` is non-injective for `q ≤ 13` but injective for every
  prime power `16 ≤ q ≤ 251` (the paper's full range). By default it runs the prime powers
  up to 49; pass an explicit list of `q` to extend the search (e.g.
  `python3 optimality_search.py 53 59 64`), or a leading `N=<k>` to bucket by `(c_1,…,c_k)`.
  A `--verify` mode re-runs the enumeration in exact integer arithmetic to rule out
  floating-point error at the Weil boundary.
  Run: `python3 optimality_search.py` or `python3 optimality_search.py --verify`.

- **`weil_general.py`** — general-`g` threshold search: for each `g`, find the minimal `N`
  such that `(c_1,…,c_N)` determines the isogeny class for large `q`. It enumerates integer
  real-Weil polynomials by a Rolle-based DFS and buckets by the cyclotomic norms
  `(F_1,…,F_N)`, `F_d = Res(Φ_d, f)`, computed exactly in `Z[ζ_d]` (equivalent to bucketing
  by `(c_1,…,c_N)`). Pure Python + NumPy.

### Symbolic verification of the explicit families

Each script verifies, as identities in `q` valid for all `q`, the explicit colliding
families used for the optimality lower bounds in Proposition 7.1. Being `q`-Weil "for all
`q`" is proved via the trace polynomial `h` (with `P(T) = T^g h(T + q/T)`): `P` is `q`-Weil
iff all roots of `h` lie in `[−2√q, 2√q]`, and `#A(F_q) = P(1) = h(1+q)`.

- **`verify_g2_family.sage`** — the `g = 2` family `P_A, P_B`; both have `#A(F_q) = q²+q−1`
  and are separated at `c_2` (`N(2) = 2`).
- **`verify_g3_family.sage`** — the `g = 3` family; both members have the same `#A(F_q) = q³`
  but differ at `c_2`, witnessing `N(3) ≥ 2`.
- **`verify_g4_family.sage`** — the `g = 4` family: `P_A, P_B` are `q`-Weil for `q ≥ 8`
  (the threshold is sharp), share `c_1, c_2, c_3` identically in `q`, and differ at `c_4`,
  witnessing `N(4) ≥ 4`.

## Other files

- `pointcountzeta.tex` — the LaTeX source of the paper; `optimality_section_draft.tex` is a
  standalone draft of the optimality section.
- `PointCountZeta/` — Lean 4 / Mathlib formalization of Theorem 1.1.
- Additional scripts in the repository root (`g6_family.py`, `verify.py`, `test.sage`, …)
  are exploratory/auxiliary and are not referenced by the paper.
</content>
