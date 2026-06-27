# Lean formalization of `pointcountzeta`

A Lean 4 / Mathlib formalization of **Theorem 1.1** of

> S. Chidambaram, T. Keller, *Point counts of abelian varieties over finite fields
> determining their zeta function.*

The development lives in [`PointCountZeta/Determination.lean`](PointCountZeta/Determination.lean).

## Building

```sh
lake exe cache get      # prebuilt Mathlib oleans
lake build              # builds PointCountZeta (+ PointCountZeta.Determination)
```

Toolchain: `leanprover/lean4:v4.31.0`, Mathlib pinned in `lake-manifest.json`.

## What the theorem says

For an abelian variety `A/F_q` of dimension `g`, if `q > Q(g) = (16 g³ p(2g))^{2g+2}`
(with `p` the partition function), the `g` point counts `#A(F_{q^i})`, `1 ≤ i ≤ g`,
determine the `L`-polynomial `f_A`, hence the zeta function and isogeny class.

## Scope: what is proved vs. axiomatized

The statement mixes deep algebraic geometry with an elementary but delicate
arithmetic/analytic recovery argument. The deep inputs are **not** in Mathlib and
are taken as explicit hypotheses, packaged in `structure FrobeniusData`:

* **Riemann Hypothesis** for `A` (`weil`): `|βᵢ| = q^{-1/2}`;
* **integrality** (`integral`): `qⁿ sₙ = Tr(Frobⁿ|H¹) ∈ ℤ` (Lemma 2.3);
* the **Poincaré duality pairing** (`pairing`): `β(σ i) = (q βᵢ)⁻¹` (Lemma 2.2);
* the **determinant normalisation** (`prod_eq`): `∏ βᵢ = q^{-g}` (fixes the sign that
  `pairing` leaves ambiguous);
* **conjugate symmetry** (`conj_pairing`): the `βᵢ` are closed under complex conjugation
  (the characteristic polynomial of Frobenius has real coefficients);
* **Tate's theorem** — interpretive only ("same `f_A`" ⇒ "same isogeny class").

Everything downstream is the actual content of the paper and is formalized here.

### Fully proved (depend only on `propext`/`Classical.choice`/`Quot.sound`)

| Lemma | Paper | Lean name |
|---|---|---|
| Weil bound on power sums | Lemma 2.4 | `FrobeniusData.norm_s_le` |
| Integrality + rounding (determination principle) | Lemma 2.3 | `FrobeniusData.s_eq_of_close` |
| Functional equation `e_{g+n} = q^{-n} e_{g-n}` | Lemma 2.2 | `FrobeniusData.functional_eq` |
| Newton–Girard identity | Lemma 2.5 | `FrobeniusData.newton_identity` |
| `s₁..sₘ` determine `eₘ` | Lemma 2.5 | `FrobeniusData.e_eq_of_s_eq` |
| Point counts → power sums `L n = log(q^{gn}/cₙ)` | Lemma 3.2 | `FrobeniusData.counts_to_sums` |
| Rounding from a direct difference (`< q^{-n}`) | Lemma 2.3 | `FrobeniusData.s_eq_of_close_diff` |
| Seed estimate `‖Lᵢ - sᵢ‖ ≤ 4g q^{-i}` | Lemma 3.4 | `FrobeniusData.seed` |
| Weil bound on `L`: `‖Lₘ‖ ≤ 4g q^{-m/2}` | Lemma 3.4 | `FrobeniusData.norm_L_le` |
| `L` tail `‖Lᵢ - sᵢ - s_{2i}/2‖ ≤ 4g q^{-3i/2}` | §6 | `FrobeniusData.norm_L_sub_two` |
| Large-range reconstruction `sₘ = sEst m` (exact) | Lemma 5.1 | `FrobeniusData.sEst_eq` |
| Base case `4g q^{-j} ≤ B_j` | Lemma 5.3 | `FrobeniusData.base_case` |
| **Large-range determination** (`g/2 < i ≤ g`, `g ≥ 2`) | §6 | `FrobeniusData.large_range_determines` |

`seed` is proved for `q ≥ 2` (the elementary tail bound `1/(1-q^{-i/2}) ≤ 4` it uses
genuinely fails as `q → 1`; in the paper's regime `q` is enormous).  `counts_to_sums`
runs through the analytic core `L n = ∑ᵢ -log(1-βᵢⁿ)` (Mercator series), is shown real
via `conj_pairing`, and recovers the paper's `log(q^{gn}/cₙ)` form using `prod_eq`.

### Proved modulo named `sorry` lemmas

The theorem now carries an extra hypothesis `hg2 : 2 ≤ g` (threaded through
`pointCounts_determine_zeta`, `exists_recovery`, `large_range_determines`): the large-range
recovery's closing inequality `2g·D^{2i-g} < q^{g/4}` reduces to `2 ≤ g`, failing only at
`g = 1` (where `Q(g) = D^{2g+2}` is tight, matching the paper's "`g ≥ 2`" caveat; the
elliptic-curve case `g = 1` is classically trivial from a single point count).

| Lemma | Paper | Lean name | Relies on |
|---|---|---|---|
| **Theorem 1.1** (`g ≥ 2`, determination of `e₀..e_{2g}`) | Thm 1.1 | `pointCounts_determine_zeta` | `exists_recovery` |
| Recovery of `s₁..s_g` | §6 | `exists_recovery` | `mobius_inversion`, `reconstruction_step` |
| Small range `‖sᵢ - s̃ᵢ‖ < ½ q^{-i}` (`i ≤ g/2`) | Lemma 4.1 | `FrobeniusData.small_range` | `mobius_inversion` |
| Large range `g/2 < i ≤ g` (`g ≥ 2`) | §6 | `FrobeniusData.large_range_determines` | `reconstruction_step` |
| Power-sum-difference budget (`g < m ≤ 2i`) | §5 | `FrobeniusData.s_diff_budget` | `reconstruction_step` |

The recovery is the paper's **combined induction** (the earlier pure-budget factoring was
unsound — it dropped the small-index exactness that §5 needs, so the bound did not close).
`exists_recovery`'s `det` is a `Nat.strong_induction_on i` establishing `F₁.sᵢ = F₂.sᵢ` for
`1 ≤ i ≤ g`: the small range (`2i ≤ g`) rounds the common truncated-Möbius estimate; the large
range threads the already-recovered exact `sⱼ` (`j < i`) as `hexact` into `large_range_determines`,
which bounds `s_{2i}` via `s_diff_budget` and rounds.  `s_diff_budget` is a strong induction over
`1 ≤ k ≤ 2i` (small `2k≤g` → exact; seed `g/2<k≤g` → `8g q^{-k} ≤ 2B_k`; reconstruction `g<k≤2i` →
`reconstruction_step`, fed the exactness slice `2j<k ⟹ j<i`).  All of `exists_recovery`, `s_diff_budget`,
`large_range_determines`, and `reconstruction_step` itself are proved in full — the latter from
`sm_formula` (see below); the only remaining `sorry`s in the development are `mobius_inversion` and
`sm_formula`.

The extra hypothesis `hg2 : 2 ≤ g` is threaded through `pointCounts_determine_zeta`,
`exists_recovery`, `large_range_determines`: the §6 closing inequality `2g·D^{2i-g} < q^{g/4}`
reduces to `2 ≤ g`, failing only at `g = 1` (where `Q(g) = D^{2g+2}` is tight, matching the
paper's "`g ≥ 2`" caveat; the elliptic-curve case `g = 1` is classically trivial).

### Stated faithfully, proof `sorry` — **exactly two**, both classical identities

| Statement | Paper | Lean name |
|---|---|---|
| Möbius inversion `sᵢ = Σ_{r≥1} μ(r)/r · L_{ri}` | Lemma 4.1 | `FrobeniusData.mobius_inversion` |
| Explicit power-sum formula `sₘ = …` (eq:sm-formula) | Lemma 5.1 | `FrobeniusData.sm_formula` |

These are the **only** two `sorry`s in the entire development.  Both are standard classical results
that are simply absent from Mathlib; everything else — including the technical heart `reconstruction_step`
— is fully proved.

`mobius_inversion` is the *infinite* Möbius inversion over multiples (dual to
`L(m) = Σ_{r≥1} s(rm)/r`): a regrouping of a double infinite sum by the product map
`(j,r) ↦ jr` (fibres = divisors).  Mathlib's Möbius inversion is for finite divisor sums
only, so this is a genuine ~250-line development (summability + Fubini over `ℕ×ℕ` + the
divisor identity `Σ_{d∣m} μ(d) = [m=1]`).

`sm_formula` is the classical explicit Newton–Girard / Waring formula for the power sums
(from `∑ eₙ Tⁿ = ∏(1+βᵢT) = exp(∑_k (-1)^{k-1} s_k Tᵏ/k)`), specialised through the functional
equation so that `sₘ` is expressed **purely in the lower `s_k`** — avoiding the `eₙ` (whose norms
`≤ binom(2g,n) ≤ 4^g` would overwhelm the sub-exponential `D`).  Mathlib has only the *recursive*
Newton identities (`MvPolynomial.mul_esymm_eq_sum`).

### The `reconstruction_step` proof (§5 induction step) — fully proved

This is the technical heart and the deepest part of the paper.  It is now proved **end-to-end** from
`sm_formula`: the reduction `‖Δsₘ‖ ≤ m(q^{-(m-g)}‖ΔΣ₁‖ + ‖ΔΣ₂‖)`, the norm reduction to the two
partition sums, the partition count `≤ p(2g)` (`partitionCount_mono`, proved via an append-ones
injection), the per-partition combinatorial estimates, and the full `rpow` **closure** to `2 Bₘ`
(closing because `8g³p(2g)/D = ½`, with room to spare).  Each partition term's `F₁`–`F₂` difference is
controlled by `partTerm_diff_factored`: the small parts are exact, so the difference factors as the
large-part difference times the (sharp) exact small product `≤ (2g)^{|S|} q^{-(ΣS)/2}`
(`norm_prod_map_s_le`).  At most one part is large in the first sum (two would sum to `≥ m > M`); the
second sum additionally admits the single two-large term `{m/2, m/2}` (`m` even), handled via the
`s²`-difference product rule.  The whole supporting toolkit — `partTerm_diff_factored`,
`norm_prod_sub_of_rest_eq`, `norm_prod_map_s_le`, `norm_prod_map_neg`, `one_le_norm_zPart`,
`partitionCount_mono` — is proved and **axiom-clean**.  Run `#print axioms pointCounts_determine_zeta`
for the `sorryAx` dependency (it traces back only to the two identities above).
