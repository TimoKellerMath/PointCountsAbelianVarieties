/-
Copyright (c) 2026 Shiva Chidambaram, Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shiva Chidambaram, Timo Keller
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Field
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# Point counts of abelian varieties determine their zeta function

A Lean 4 / Mathlib formalization of the main theorem of

  Shiva Chidambaram, Timo Keller,
  *Point counts of abelian varieties over finite fields determining their zeta
  function* (`pointcountzeta.tex`).

**Theorem 1.1.** Let `A` be an abelian variety of dimension `g` over `F_q`.  If
`q > Q(g) = (16 g³ p(2g))^{2g+2}` (where `p` is the partition function), then the
`g` point counts `#A(F_{q^i})`, `1 ≤ i ≤ g`, determine the `L`-polynomial `f_A`,
hence the zeta function and the isogeny class.

## What is and is not proved here

The statement of Theorem 1.1 mixes deep algebraic geometry with an elementary but
delicate arithmetic/analytic recovery argument.  The deep inputs are **not** in
Mathlib and each is a major formalization in its own right; we take them as
explicit hypotheses, packaged in `FrobeniusData`:

* the **Riemann Hypothesis** for `A` (Weil): every reciprocal Frobenius
  eigenvalue has absolute value `q^{-1/2}` (field `weil`);
* **integrality**: `qⁿ sₙ = Tr(Frobⁿ | H¹) ∈ ℤ` (field `integral`, Lemma 2.3);
* the **functional equation / Poincaré duality pairing** `αᵢ α_{i+g} = q`
  (field `pairing`), from which Lemma 2.2 follows;
* **Tate's theorem**, used only to read the conclusion "same `f_A`" as "same
  isogeny class" — it is purely interpretive and does not enter the proof.

Everything downstream of these inputs is the actual content of the paper and is
formalized here.  The two genuinely elementary primitives — the **Weil bound on
power sums** (Lemma 2.4) and the **integrality-plus-rounding** determination
principle (Lemma 2.3) — are proved in full.  The deeper estimates of Sections 3–6
(counts → power sums, the small range via truncated Möbius inversion, and the
inductive large-range error analysis) are stated faithfully; the hardest analytic
and combinatorial estimates are isolated as clearly marked `sorry`s, each
annotated with the corresponding lemma of the paper.

The headline theorem `pointCounts_determine_zeta` is then derived in full from the
recovery statement `exists_recovery`.
-/

open Finset
open scoped BigOperators

namespace PointCountZeta

/-! ## The constants of the theorem -/

/-- The partition function `p(n)`, i.e. the number of partitions of `n`. -/
noncomputable def partitionCount (n : ℕ) : ℕ := Nat.card (Nat.Partition n)

/-- The constant `D = 16 g³ p(2g)` driving the inductive error bound (§5). -/
noncomputable def Dconst (g : ℕ) : ℝ := 16 * (g : ℝ) ^ 3 * (partitionCount (2 * g) : ℝ)

/-- The explicit threshold `Q(g) = (16 g³ p(2g))^{2g+2} = D^{2g+2}` of Theorem 1.1. -/
noncomputable def Qbound (g : ℕ) : ℝ := (Dconst g) ^ (2 * g + 2)

/-- The inductive error budget `B_j = g · q^{-j/2 - g/4} · D^{j-g}` of §5. -/
noncomputable def Bbudget (g : ℕ) (q : ℝ) (j : ℕ) : ℝ :=
  (g : ℝ) * q ^ (-(j : ℝ) / 2 - (g : ℝ) / 4) * (Dconst g) ^ ((j : ℝ) - g)

/-! ## The Frobenius data of an abelian variety

`FrobeniusData g q` packages the reciprocal Frobenius eigenvalues `βᵢ = αᵢ⁻¹`
of an abelian variety of dimension `g` over `F_q`, together with the deep inputs
(RH, integrality, the duality pairing) as hypotheses; see the file header. -/
structure FrobeniusData (g : ℕ) (q : ℝ) where
  /-- The reciprocal Frobenius eigenvalues `βᵢ = αᵢ⁻¹`, `1 ≤ i ≤ 2g`. -/
  β : Fin (2 * g) → ℂ
  /-- Riemann Hypothesis for `A`: `|βᵢ| = q^{-1/2}` for all `i`. -/
  weil : ∀ i, ‖β i‖ = q ^ (-(1 : ℝ) / 2)
  /-- Integrality (Lemma 2.3): `qⁿ sₙ = Tr(Frobⁿ | H¹) ∈ ℤ` for `n ≥ 1`. -/
  integral : ∀ n : ℕ, 1 ≤ n → ∃ m : ℤ, (q : ℂ) ^ n * (∑ i, (β i) ^ n) = (m : ℂ)
  /-- Poincaré duality pairing (Lemma 2.2): an involution `σ` with
      `β (σ i) = (q · β i)⁻¹`, i.e. `α_{σ i} = q / αᵢ`. -/
  pairing : ∃ σ : Equiv.Perm (Fin (2 * g)),
    Function.Involutive σ ∧ ∀ i, β (σ i) = ((q : ℂ) * β i)⁻¹
  /-- Normalisation `∏ αᵢ = q^g`, i.e. `∏ βᵢ = q^{-g}` (the determinant of Frobenius
      on `H¹`).  `pairing` only forces `(∏ βᵢ)² = q^{-2g}`; this field fixes the sign. -/
  prod_eq : ∏ i, β i = (q : ℂ)⁻¹ ^ g
  /-- The reciprocal eigenvalues are closed under complex conjugation: the
      characteristic polynomial of Frobenius on `H¹` has rational (real) coefficients. -/
  conj_pairing : ∃ τ : Equiv.Perm (Fin (2 * g)), ∀ i, (starRingEnd ℂ) (β i) = β (τ i)

namespace FrobeniusData

variable {g : ℕ} {q : ℝ} (F : FrobeniusData g q)

/-- `n`-th power sum of the reciprocal eigenvalues: `sₙ = Σ βᵢⁿ`. -/
def s (n : ℕ) : ℂ := ∑ i, (F.β i) ^ n

/-- `m`-th elementary symmetric function of the `βᵢ`: `eₘ = Σ_{#I=m} Π_{i∈I} βᵢ`.
    These are, up to sign and the normalisation `a_{2g} = q^g`, the coefficients
    of the `L`-polynomial `f_A`. -/
def e (m : ℕ) : ℂ :=
  ∑ I ∈ (univ : Finset (Fin (2 * g))).powersetCard m, ∏ i ∈ I, F.β i

/-- The exactly-known quantity `Lₙ = log(q^{gn}/cₙ) = Σ_{j≥1} s_{jn}/j` attached to
    the point count `cₙ = #A(F_{qⁿ})` (Lemma 3.2).  Here it is written as the
    convergent series in the power sums; the equality with `log(q^{gn}/cₙ)` is the
    content of `counts_to_sums` below, which is why knowing `c₁,…,c_g` is the same
    as knowing `L₁,…,L_g`. -/
noncomputable def L (n : ℕ) : ℂ := ∑' j : ℕ, F.s ((j + 1) * n) / ((j + 1 : ℕ) : ℂ)

/-! ## Lemma 2.4 — the Weil bound on power sums -/

/-- **Weil bound** (Lemma 2.4): `‖sₙ‖ ≤ 2g · q^{-n/2}`. -/
theorem norm_s_le (hq : 0 ≤ q) (n : ℕ) :
    ‖F.s n‖ ≤ 2 * (g : ℝ) * q ^ (-(n : ℝ) / 2) := by
  have hterm : ∀ i : Fin (2 * g), ‖(F.β i) ^ n‖ = q ^ (-(n : ℝ) / 2) := by
    intro i
    rw [norm_pow, F.weil i, ← Real.rpow_natCast (q ^ (-(1 : ℝ) / 2)) n,
      ← Real.rpow_mul hq]
    ring_nf
  calc ‖F.s n‖ ≤ ∑ i, ‖(F.β i) ^ n‖ := norm_sum_le _ _
    _ = ∑ _i : Fin (2 * g), q ^ (-(n : ℝ) / 2) := by
        exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = 2 * (g : ℝ) * q ^ (-(n : ℝ) / 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

/-! ## Lemma 2.3 — integrality and rounding

The integrality of `qⁿ sₙ` turns "knowing `sₙ` to additive error `< ½ q^{-n}`"
into "knowing `sₙ` exactly", because distinct admissible values are `q^{-n}` apart.
We phrase this as the determination principle that drives the whole proof: two
abelian varieties whose `sₙ` are both within `½ q^{-n}` of a *common* value must
have *equal* `sₙ`. -/

/-- **Rounding / determination** (Lemma 2.3).  If `‖F.sₙ - x‖ < ½ q^{-n}` and
    `‖F'.sₙ - x‖ < ½ q^{-n}` for a common `x`, then `F.sₙ = F'.sₙ`.  This is the
    statement that `qⁿ sₙ ∈ ℤ` is recovered by rounding. -/
theorem s_eq_of_close (F F' : FrobeniusData g q) (hq : 1 < q) {n : ℕ} (hn : 1 ≤ n)
    {x : ℂ} (h : ‖F.s n - x‖ < 1 / (2 * (q ^ n : ℝ)))
    (h' : ‖F'.s n - x‖ < 1 / (2 * (q ^ n : ℝ))) : F.s n = F'.s n := by
  have hq0 : (0 : ℝ) < q := lt_trans one_pos hq
  have hqn : (0 : ℝ) < q ^ n := pow_pos hq0 n
  -- integrality of both
  obtain ⟨m, hm⟩ := F.integral n hn
  obtain ⟨m', hm'⟩ := F'.integral n hn
  -- the two integers are within distance < 1, hence equal
  have hnormqc : ‖(q : ℂ) ^ n‖ = (q ^ n : ℝ) := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hq0.le]
  have hdist : ‖(q : ℂ) ^ n * F.s n - (q : ℂ) ^ n * F'.s n‖ < 1 := by
    have htri : ‖F.s n - F'.s n‖ < 1 / (q ^ n : ℝ) := by
      calc ‖F.s n - F'.s n‖ = ‖(F.s n - x) - (F'.s n - x)‖ := by ring_nf
        _ ≤ ‖F.s n - x‖ + ‖F'.s n - x‖ := norm_sub_le _ _
        _ < 1 / (2 * (q ^ n : ℝ)) + 1 / (2 * (q ^ n : ℝ)) := by linarith
        _ = 1 / (q ^ n : ℝ) := by ring
    calc ‖(q : ℂ) ^ n * F.s n - (q : ℂ) ^ n * F'.s n‖
        = ‖(q : ℂ) ^ n‖ * ‖F.s n - F'.s n‖ := by rw [← mul_sub, norm_mul]
      _ = (q ^ n : ℝ) * ‖F.s n - F'.s n‖ := by rw [hnormqc]
      _ < (q ^ n : ℝ) * (1 / (q ^ n : ℝ)) := by
            apply mul_lt_mul_of_pos_left htri hqn
      _ = 1 := by field_simp
  rw [show F.s n = ∑ i, F.β i ^ n from rfl, show F'.s n = ∑ i, F'.β i ^ n from rfl,
    hm, hm'] at hdist
  -- `‖(m - m' : ℂ)‖ < 1` forces `m = m'`
  have hmm : ‖((m - m' : ℤ) : ℂ)‖ < 1 := by push_cast; exact hdist
  have : (m - m' : ℤ) = 0 := by
    have h1 : |((m - m' : ℤ) : ℝ)| < 1 := by rw [← Complex.norm_intCast]; exact hmm
    have h2 : |(m - m' : ℤ)| < 1 := by exact_mod_cast h1
    exact Int.abs_lt_one_iff.mp h2
  have hmeq : m = m' := by omega
  -- cancel `qⁿ ≠ 0`
  have hqcn : (q : ℂ) ^ n ≠ 0 := by
    apply pow_ne_zero; exact_mod_cast hq0.ne'
  have heq : (q : ℂ) ^ n * F.s n = (q : ℂ) ^ n * F'.s n := by
    rw [show F.s n = ∑ i, F.β i ^ n from rfl, show F'.s n = ∑ i, F'.β i ^ n from rfl,
      hm, hm', hmeq]
  exact mul_left_cancel₀ hqcn heq

/-- **Rounding from a direct difference** (Lemma 2.3 variant).  If
    `‖F.sₙ - F'.sₙ‖ < q^{-n}` then `F.sₙ = F'.sₙ`.  (The `< q^{-n}` bound — not
    `< ½ q^{-n}` — suffices because both `qⁿ sₙ` are integers.) -/
theorem s_eq_of_close_diff (F F' : FrobeniusData g q) (hq : 1 < q) {n : ℕ} (hn : 1 ≤ n)
    (h : ‖F.s n - F'.s n‖ < 1 / (q ^ n : ℝ)) : F.s n = F'.s n := by
  have hq0 : (0 : ℝ) < q := lt_trans one_pos hq
  have hqn : (0 : ℝ) < q ^ n := pow_pos hq0 n
  obtain ⟨m, hm⟩ := F.integral n hn
  obtain ⟨m', hm'⟩ := F'.integral n hn
  have hnormqc : ‖(q : ℂ) ^ n‖ = (q ^ n : ℝ) := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hq0.le]
  have hdist : ‖(q : ℂ) ^ n * F.s n - (q : ℂ) ^ n * F'.s n‖ < 1 := by
    calc ‖(q : ℂ) ^ n * F.s n - (q : ℂ) ^ n * F'.s n‖
        = ‖(q : ℂ) ^ n‖ * ‖F.s n - F'.s n‖ := by rw [← mul_sub, norm_mul]
      _ = (q ^ n : ℝ) * ‖F.s n - F'.s n‖ := by rw [hnormqc]
      _ < (q ^ n : ℝ) * (1 / (q ^ n : ℝ)) := by apply mul_lt_mul_of_pos_left h hqn
      _ = 1 := by field_simp
  rw [show F.s n = ∑ i, F.β i ^ n from rfl, show F'.s n = ∑ i, F'.β i ^ n from rfl,
    hm, hm'] at hdist
  have hmm : ‖((m - m' : ℤ) : ℂ)‖ < 1 := by push_cast; exact hdist
  have hmm0 : (m - m' : ℤ) = 0 := by
    have h1 : |((m - m' : ℤ) : ℝ)| < 1 := by rw [← Complex.norm_intCast]; exact hmm
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast h1)
  have hmeq : m = m' := by omega
  have hqcn : (q : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq0.ne')
  have heq : (q : ℂ) ^ n * F.s n = (q : ℂ) ^ n * F'.s n := by
    rw [show F.s n = ∑ i, F.β i ^ n from rfl, show F'.s n = ∑ i, F'.β i ^ n from rfl,
      hm, hm', hmeq]
  exact mul_left_cancel₀ hqcn heq

/-! ## Lemma 2.2 — the functional equation

`e_{g+n} = q^{-n} e_{g-n}` for `1 ≤ n ≤ g`, from the duality pairing
`β (σ i) = (q β i)⁻¹`. -/

/-- **Functional equation** (Lemma 2.2): `e_{g+n} = q^{-n} e_{g-n}` for `1 ≤ n ≤ g`.

    `eₘ = (∏ βᵢ) · eₘ'(β⁻¹)` (complement bijection, `m' = 2g-m`), and `eₘ'(β⁻¹) =
    q^{m'} eₘ'(β)` since `βᵢ⁻¹ = q β_{σ i}` and `σ` permutes the indices; with
    `∏ βᵢ = q^{-g}` (`prod_eq`) this gives `eₘ = q^{g-m} e_{2g-m}`. -/
theorem functional_eq (hq : 0 < q) {n : ℕ} (hn : 1 ≤ n) (hng : n ≤ g) :
    F.e (g + n) = (q : ℂ) ^ (-(n : ℤ)) * F.e (g - n) := by
  classical
  have hqcne : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hβne : ∀ i, F.β i ≠ 0 := by
    intro i h
    have hw := F.weil i; rw [h, norm_zero] at hw
    linarith [Real.rpow_pos_of_pos hq (-(1 : ℝ) / 2)]
  obtain ⟨σ, hσinv, hσβ⟩ := F.pairing
  -- per-subset: `∏_{i∈I} βᵢ = (∏ βᵢ) · ∏_{i∈Iᶜ} βᵢ⁻¹`
  have hAterm : ∀ I : Finset (Fin (2 * g)),
      ∏ i ∈ I, F.β i = (∏ i, F.β i) * ∏ i ∈ Iᶜ, (F.β i)⁻¹ := by
    intro I
    have key : (∏ i ∈ Iᶜ, F.β i) * ∏ i ∈ Iᶜ, (F.β i)⁻¹ = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun i _ => mul_inv_cancel₀ (hβne i))
    calc ∏ i ∈ I, F.β i
        = (∏ i ∈ I, F.β i) * ((∏ i ∈ Iᶜ, F.β i) * ∏ i ∈ Iᶜ, (F.β i)⁻¹) := by rw [key, mul_one]
      _ = ((∏ i ∈ Iᶜ, F.β i) * (∏ i ∈ I, F.β i)) * ∏ i ∈ Iᶜ, (F.β i)⁻¹ := by ring
      _ = (∏ i, F.β i) * ∏ i ∈ Iᶜ, (F.β i)⁻¹ := by rw [Finset.prod_compl_mul_prod I F.β]
  -- Step A: `e_{g+n} = (∏ βᵢ) · ∑_{|J|=g-n} ∏_{j∈J} βⱼ⁻¹`
  have hA : F.e (g + n)
      = (∏ i, F.β i) * ∑ J ∈ Finset.powersetCard (g - n) univ, ∏ j ∈ J, (F.β j)⁻¹ := by
    unfold FrobeniusData.e
    rw [Finset.mul_sum]
    refine Finset.sum_bij' (fun I _ => Iᶜ) (fun J _ => Jᶜ) ?_ ?_ ?_ ?_ ?_
    · intro I hI
      rw [Finset.mem_powersetCard_univ] at hI ⊢
      rw [Finset.card_compl, Fintype.card_fin, hI]; omega
    · intro J hJ
      rw [Finset.mem_powersetCard_univ] at hJ ⊢
      rw [Finset.card_compl, Fintype.card_fin, hJ]; omega
    · intro I _; exact compl_compl I
    · intro J _; exact compl_compl J
    · intro I _; exact hAterm I
  -- per-subset rescaling: `βⱼ⁻¹ = q · β_{σ j}`
  have hBelt : ∀ j, (F.β j)⁻¹ = (q : ℂ) * F.β (σ j) := by
    intro j
    rw [hσβ j, mul_inv, ← mul_assoc, mul_inv_cancel₀ hqcne, one_mul]
  have hBterm : ∀ J : Finset (Fin (2 * g)),
      ∏ j ∈ J, (F.β j)⁻¹ = (q : ℂ) ^ (#J) * ∏ j ∈ J, F.β (σ j) := by
    intro J
    rw [Finset.prod_congr rfl (fun j _ => hBelt j), Finset.prod_mul_distrib, Finset.prod_const]
  -- Step B: `∑_{|J|=g-n} ∏ βⱼ⁻¹ = q^{g-n} · e_{g-n}`
  have hB : (∑ J ∈ Finset.powersetCard (g - n) univ, ∏ j ∈ J, (F.β j)⁻¹)
      = (q : ℂ) ^ (g - n) * F.e (g - n) := by
    unfold FrobeniusData.e
    rw [Finset.mul_sum]
    refine Finset.sum_bij' (fun J _ => Finset.image σ J) (fun J' _ => Finset.image σ J')
      ?_ ?_ ?_ ?_ ?_
    · intro J hJ
      rw [Finset.mem_powersetCard_univ] at hJ ⊢
      rw [Finset.card_image_of_injective _ σ.injective, hJ]
    · intro J' hJ'
      rw [Finset.mem_powersetCard_univ] at hJ' ⊢
      rw [Finset.card_image_of_injective _ σ.injective, hJ']
    · intro J _
      rw [Finset.image_image, show (⇑σ ∘ ⇑σ) = id from funext hσinv, Finset.image_id]
    · intro J' _
      rw [Finset.image_image, show (⇑σ ∘ ⇑σ) = id from funext hσinv, Finset.image_id]
    · intro J hJ
      rw [Finset.mem_powersetCard_univ] at hJ
      rw [hBterm J, hJ]
      congr 1
      exact (Finset.prod_image (σ.injective.injOn)).symm
  -- scalar: `(∏ βᵢ) · q^{g-n} = q^{-n}`
  have hscalar : (q : ℂ)⁻¹ ^ g * (q : ℂ) ^ (g - n) = (q : ℂ) ^ (-(n : ℤ)) := by
    rw [inv_pow, ← zpow_natCast (q : ℂ) g, ← zpow_neg, ← zpow_natCast (q : ℂ) (g - n),
      ← zpow_add₀ hqcne]
    congr 1
    omega
  rw [hA, hB, prod_eq, ← mul_assoc, hscalar]

/-! ## Lemma 2.5 — Newton's identities

Knowing `s₁,…,sₘ` determines `e₁,…,eₘ` and conversely (closed form
`(2.5)`/Newton–Girard).  Specialized to the `βᵢ` from Mathlib's
`MvPolynomial.Symmetric.NewtonIdentities`. -/

/-- **Newton's identity** (Lemma 2.5): `n eₙ = Σ_{i=1}^n (-1)^{i-1} e_{n-i} sᵢ`.

    Proved by specializing Mathlib's polynomial Newton identity
    `MvPolynomial.mul_esymm_eq_sum` along the evaluation `X i ↦ β i` and reindexing
    the antidiagonal sum `{a + b = n, a < n}` by `i = b` to `Icc 1 n`. -/
theorem newton_identity {n : ℕ} (_hn : 1 ≤ n) (_hn2 : n ≤ 2 * g) :
    (n : ℂ) * F.e n = ∑ i ∈ Finset.Icc 1 n, (-1 : ℂ) ^ (i - 1) * F.e (n - i) * F.s i := by
  classical
  -- `aeval F.β` sends `esymm`/`psum` to our `e`/`s`
  have he : ∀ k, (MvPolynomial.aeval F.β) (MvPolynomial.esymm (Fin (2 * g)) ℂ k) = F.e k := by
    intro k
    simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.aeval_X]
    rfl
  have hs : ∀ k, (MvPolynomial.aeval F.β) (MvPolynomial.psum (Fin (2 * g)) ℂ k) = F.s k := by
    intro k
    simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
    rfl
  -- evaluate the polynomial identity
  have key : (n : ℂ) * F.e n
      = (-1) ^ (n + 1) * ∑ a ∈ {a ∈ Finset.antidiagonal n | a.1 < n},
          (-1) ^ a.1 * F.e a.1 * F.s a.2 := by
    have h0 := congrArg (⇑(MvPolynomial.aeval F.β))
      (MvPolynomial.mul_esymm_eq_sum (Fin (2 * g)) ℂ n)
    simpa only [map_mul, map_natCast, map_sum, map_pow, map_neg, map_one, he, hs] using h0
  -- sign reconciliation: `(-1)^(n+1) (-1)^(n-i) = (-1)^(i-1)` for `1 ≤ i ≤ n`
  have hsign : ∀ i, 1 ≤ i → i ≤ n → (-1 : ℂ) ^ (n + 1) * (-1) ^ (n - i) = (-1) ^ (i - 1) := by
    intro i hi1 hin
    rw [← pow_add, show n + 1 + (n - i) = (i - 1) + 2 * (n + 1 - i) by omega, pow_add, pow_mul,
      neg_one_sq, one_pow, mul_one]
  rw [key, Finset.mul_sum]
  refine Finset.sum_bij' (fun a _ => a.2) (fun i _ => (n - i, i)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at ha
    rw [Finset.mem_Icc]; omega
  · intro i hi
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_filter, Finset.mem_antidiagonal]; dsimp only; omega
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at ha
    rw [Prod.ext_iff]; dsimp only; omega
  · intro i hi; rfl
  · intro a ha
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at ha
    have ha2 : 1 ≤ a.2 ∧ a.2 ≤ n := by omega
    have ha1 : a.1 = n - a.2 := by omega
    rw [ha1, ← hsign a.2 ha2.1 ha2.2]; ring

/-- If `s₁,…,sₘ` are known, `eₘ` is determined: this is a clean strong induction
    on `m` from `newton_identity` (the only remaining input). -/
theorem e_eq_of_s_eq (F F' : FrobeniusData g q)
    {m : ℕ} (hm : m ≤ 2 * g) (hs : ∀ i, 1 ≤ i → i ≤ m → F.s i = F'.s i) :
    F.e m = F'.e m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp [FrobeniusData.e]
    · -- `m · eₘ = Σ (-1)^{i-1} e_{m-i} sᵢ`, with each summand equal for `F`, `F'`.
      have hN := newton_identity F hpos hm
      have hN' := newton_identity F' hpos hm
      have hRHS : (∑ i ∈ Finset.Icc 1 m, (-1 : ℂ) ^ (i - 1) * F.e (m - i) * F.s i)
                = ∑ i ∈ Finset.Icc 1 m, (-1 : ℂ) ^ (i - 1) * F'.e (m - i) * F'.s i := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [Finset.mem_Icc] at hi
        have hsi : F.s i = F'.s i := hs i hi.1 hi.2
        have hei : F.e (m - i) = F'.e (m - i) :=
          ih (m - i) (by omega) (by omega) (fun j hj1 hjmi => hs j hj1 (by omega))
        rw [hsi, hei]
      have hmul : (m : ℂ) * F.e m = (m : ℂ) * F'.e m := by rw [hN, hN', hRHS]
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      exact mul_left_cancel₀ hm0 hmul

/-! ## Lemma 3.2 — from point counts to power sums -/

/-- **Point counts determine perturbed power sums** (Lemma 3.2): with
    `cₙ = #A(F_{qⁿ}) = ∏ᵢ(1 - αᵢⁿ) = ∏ᵢ(1 - βᵢ⁻¹ⁿ)`, one has
    `F.L n = log(q^{gn}/cₙ)`.

    The proof runs through the genuine analytic content `F.L n = ∑ᵢ -log(1 - βᵢⁿ)`
    (Mercator expansion `-log(1-z) = Σ_{m≥1} zᵐ/m`, summation order exchanged); the
    sum is real by `conj_pairing`, its exponential is `∏ᵢ(1-βᵢⁿ)⁻¹`, and `prod_eq`
    turns `∏ᵢ(1-βᵢ⁻¹ⁿ)` into `q^{gn} ∏ᵢ(1-βᵢⁿ)`, so the principal logarithm of
    `q^{gn}/cₙ` returns the sum. -/
theorem counts_to_sums (hq : 1 < q) (n : ℕ) (hn : 1 ≤ n) :
    F.L n = Complex.log ((q : ℂ) ^ (g * n) / ∏ i, (1 - (F.β i)⁻¹ ^ n)) := by
  have hq0 : (0 : ℝ) < q := by linarith
  -- each `‖βᵢⁿ‖ = (q^{-1/2})ⁿ < 1`
  have hznorm : ∀ i : Fin (2 * g), ‖(F.β i) ^ n‖ < 1 := by
    intro i
    rw [norm_pow, F.weil i]
    refine pow_lt_one₀ (le_of_lt (Real.rpow_pos_of_pos hq0 _)) ?_ (by omega)
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num)
  -- analytic core: `L n = ∑ -log(1-βᵢⁿ)`
  have hcore : F.L n = ∑ i, -Complex.log (1 - (F.β i) ^ n) := by
    have hper : ∀ z : ℂ, ‖z‖ < 1 →
        (∑' j : ℕ, z ^ (j + 1) / ((j + 1 : ℕ) : ℂ)) = -Complex.log (1 - z) := by
      intro z hzz
      have hHS := Complex.hasSum_taylorSeries_neg_log hzz
      have hshift : Summable (fun j : ℕ => z ^ (j + 1) / ((j + 1 : ℕ) : ℂ)) :=
        (summable_nat_add_iff 1).mpr hHS.summable
      rw [← hHS.tsum_eq, tsum_eq_zero_add' (f := fun m : ℕ => z ^ m / (m : ℂ)) hshift]
      simp
    have hsumm : ∀ i : Fin (2 * g),
        Summable (fun j : ℕ => (F.β i) ^ ((j + 1) * n) / ((j + 1 : ℕ) : ℂ)) := by
      intro i
      have hHS := Complex.hasSum_taylorSeries_neg_log (hznorm i)
      refine ((summable_nat_add_iff 1).mpr hHS.summable).congr (fun j => ?_)
      rw [pow_mul']
    have hstep : F.L n = ∑' j : ℕ, ∑ i, (F.β i) ^ ((j + 1) * n) / ((j + 1 : ℕ) : ℂ) := by
      unfold FrobeniusData.L
      apply tsum_congr; intro j
      simp only [FrobeniusData.s, Finset.sum_div]
    rw [hstep, Summable.tsum_finsetSum (fun i _ => hsumm i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [tsum_congr (fun j => by rw [pow_mul'] :
      ∀ j : ℕ, (F.β i) ^ ((j + 1) * n) / ((j + 1 : ℕ) : ℂ)
        = ((F.β i) ^ n) ^ (j + 1) / ((j + 1 : ℕ) : ℂ))]
    exact hper ((F.β i) ^ n) (hznorm i)
  -- nonvanishing / positivity of `1 - βᵢⁿ`
  have hβne : ∀ i, F.β i ≠ 0 := by
    intro i h
    have hw := F.weil i
    rw [h, norm_zero] at hw
    linarith [Real.rpow_pos_of_pos hq0 (-(1 : ℝ) / 2)]
  have hre : ∀ i, 0 < (1 - (F.β i) ^ n).re := by
    intro i
    rw [Complex.sub_re, Complex.one_re]
    linarith [hznorm i, Complex.re_le_norm ((F.β i) ^ n)]
  have hne : ∀ i, (1 : ℂ) - (F.β i) ^ n ≠ 0 := by
    intro i h
    have hh := hre i; rw [h, Complex.zero_re] at hh; exact lt_irrefl 0 hh
  have harg : ∀ i, (1 - (F.β i) ^ n).arg ≠ Real.pi := by
    intro i hc
    rw [Complex.arg_eq_pi_iff] at hc
    linarith [hre i, hc.1]
  set S := ∑ i, -Complex.log (1 - (F.β i) ^ n) with hS
  -- `exp S = (∏ (1-βᵢⁿ))⁻¹`
  have hexpS : Complex.exp S = (∏ i, (1 - (F.β i) ^ n))⁻¹ := by
    rw [hS, Complex.exp_sum, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Complex.exp_neg, Complex.exp_log (hne i)]
  -- `S` is real (conjugation permutes the eigenvalues)
  have hconj : (starRingEnd ℂ) S = S := by
    obtain ⟨τ, hτ⟩ := F.conj_pairing
    rw [hS, map_sum]
    conv_rhs => rw [← Equiv.sum_comp τ (fun i => -Complex.log (1 - (F.β i) ^ n))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_neg]
    congr 1
    rw [← Complex.log_conj _ (harg i)]
    congr 1
    rw [map_sub, map_one, map_pow, hτ i]
  have him : S.im = 0 := Complex.conj_eq_iff_im.mp hconj
  -- product identity from `prod_eq`
  have hprodid : ∏ i, (1 - (F.β i)⁻¹ ^ n) = (q : ℂ) ^ (g * n) * ∏ i, (1 - (F.β i) ^ n) := by
    have hterm : ∀ i, (1 : ℂ) - (F.β i)⁻¹ ^ n = (F.β i)⁻¹ ^ n * (-(1 - (F.β i) ^ n)) := by
      intro i
      have hbne : (F.β i)⁻¹ ^ n * (F.β i) ^ n = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ (hβne i), one_pow]
      have hrw : (F.β i)⁻¹ ^ n * (-(1 - (F.β i) ^ n))
          = (F.β i)⁻¹ ^ n * (F.β i) ^ n - (F.β i)⁻¹ ^ n := by ring
      rw [hrw, hbne]
    have hneg : ∏ i, (-(1 - (F.β i) ^ n)) = ∏ i, (1 - (F.β i) ^ n) := by
      rw [Finset.prod_neg, Finset.card_univ, Fintype.card_fin, pow_mul, neg_one_sq, one_pow,
        one_mul]
    calc ∏ i, (1 - (F.β i)⁻¹ ^ n)
        = ∏ i, ((F.β i)⁻¹ ^ n * (-(1 - (F.β i) ^ n))) :=
          Finset.prod_congr rfl (fun i _ => hterm i)
      _ = (∏ i, (F.β i)⁻¹ ^ n) * ∏ i, (-(1 - (F.β i) ^ n)) := Finset.prod_mul_distrib
      _ = (∏ i, (F.β i)⁻¹ ^ n) * ∏ i, (1 - (F.β i) ^ n) := by rw [hneg]
      _ = (q : ℂ) ^ (g * n) * ∏ i, (1 - (F.β i) ^ n) := by
          rw [Finset.prod_pow, Finset.prod_inv_distrib, prod_eq]
          congr 1
          rw [inv_pow (q : ℂ) g, inv_inv, ← pow_mul]
  -- assemble: `q^{gn}/cₙ = (∏(1-βᵢⁿ))⁻¹ = exp S`, and `log (exp S) = S`
  rw [hcore, hprodid]
  have hpne : ∏ i, (1 - (F.β i) ^ n) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hne i)
  have hqne : (q : ℂ) ^ (g * n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq0.ne')
  rw [show (q : ℂ) ^ (g * n) / ((q : ℂ) ^ (g * n) * ∏ i, (1 - (F.β i) ^ n))
      = (∏ i, (1 - (F.β i) ^ n))⁻¹ by rw [← div_div, div_self hqne, one_div], ← hexpS,
    Complex.log_exp (by rw [him]; linarith [Real.pi_pos]) (by rw [him]; linarith [Real.pi_pos])]

/-! ## Lemma 3.4 — the seed estimate -/

/-- **Seed estimate** (Lemma 3.4): `‖Lᵢ - sᵢ‖ ≤ 4g · q^{-i}`, i.e. `Lᵢ` already
    pins down `sᵢ` to within `4g q^{-i}` (not yet `< ½ q^{-i}`).

    The elementary tail bound below needs `q ≥ 2`: writing `r = q^{-i/2}`, it uses
    `1/(1 - r) ≤ 4`, which already fails for `q` close to `1`.  In the regime of the
    paper `q` is enormous, so this is no loss. -/
theorem seed (hq : 2 ≤ q) {i : ℕ} (hi : 1 ≤ i) :
    ‖F.L i - F.s i‖ ≤ 4 * (g : ℝ) * q ^ (-(i : ℝ)) := by
  -- `Lᵢ - sᵢ = Σ_{j≥1} s_{(j+1)i}/(j+1)`; bound by `Σ_{j≥1} g r^{j+1}·…` with
  -- `r = q^{-i/2}`, summed as a geometric series, using `q ≥ 2 ⇒ 1/(1-r) ≤ 4`. (§3.)
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) < q := by linarith
  have hir : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hgr0 : (0 : ℝ) ≤ (g : ℝ) := by positivity
  set r : ℝ := q ^ (-(i : ℝ) / 2) with hr
  have hr0 : 0 ≤ r := le_of_lt (Real.rpow_pos_of_pos hq0 _)
  have hr1 : r < 1 := by
    rw [hr]; exact Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  -- `r² = q^{-i}`
  have hr2eq : r ^ 2 = q ^ (-(i : ℝ)) := by
    rw [hr, ← Real.rpow_natCast (q ^ (-(i : ℝ) / 2)) 2, ← Real.rpow_mul hq0.le]
    congr 1; push_cast; ring
  -- `r² ≤ 1/2`, hence `r ≤ 3/4` and `(1-r)⁻¹ ≤ 4`
  have hr2 : r ^ 2 ≤ 1 / 2 := by
    rw [hr2eq]
    have h1 : q ^ (-(i : ℝ)) ≤ q ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : q ^ (-(1 : ℝ)) = q⁻¹ := by rw [Real.rpow_neg hq0.le, Real.rpow_one]
    have h3 : q⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ hq0 (by norm_num : (0 : ℝ) < 2)]; linarith
    linarith
  have hr34 : r ≤ 3 / 4 := by nlinarith [hr0, hr2]
  have h1mr_pos : (0 : ℝ) < 1 - r := by linarith
  have hinv4 : (1 - r)⁻¹ ≤ 4 := by
    have hle : (1 : ℝ) ≤ 4 * (1 - r) := by linarith
    calc (1 - r)⁻¹ = 1 * (1 - r)⁻¹ := by ring
      _ ≤ (4 * (1 - r)) * (1 - r)⁻¹ :=
          mul_le_mul_of_nonneg_right hle (inv_pos.mpr h1mr_pos).le
      _ = 4 := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt h1mr_pos), mul_one]
  -- the `L`-series term function; `F.L i = ∑' j, term j`
  set term : ℕ → ℂ := fun j => F.s ((j + 1) * i) / ((j + 1 : ℕ) : ℂ) with hterm_def
  have hL_eq : F.L i = ∑' j, term j := rfl
  have hf0 : term 0 = F.s i := by rw [hterm_def]; simp
  -- the dominating geometric series `g·r² · r^j`
  have hgeom : HasSum (fun j : ℕ => r ^ j) (1 - r)⁻¹ := hasSum_geometric_of_lt_one hr0 hr1
  have hgdom : HasSum (fun j : ℕ => ((g : ℝ) * r ^ 2) * r ^ j) (((g : ℝ) * r ^ 2) * (1 - r)⁻¹) :=
    hgeom.mul_left _
  -- termwise bound on the shifted series
  have hbound : ∀ j, ‖term (j + 1)‖ ≤ ((g : ℝ) * r ^ 2) * r ^ j := by
    intro j
    have hval : term (j + 1) = F.s ((j + 1 + 1) * i) / ((j + 1 + 1 : ℕ) : ℂ) := by rw [hterm_def]
    rw [hval, norm_div]
    have hden : ‖((j + 1 + 1 : ℕ) : ℂ)‖ = ((j : ℝ) + 2) := by
      rw [Complex.norm_natCast]; push_cast; ring
    rw [hden]
    have hnum : ‖F.s ((j + 1 + 1) * i)‖ ≤ 2 * (g : ℝ) * q ^ (-(((j + 1 + 1) * i : ℕ) : ℝ) / 2) :=
      F.norm_s_le hq0.le _
    have hpow : q ^ (-(((j + 1 + 1) * i : ℕ) : ℝ) / 2) = r ^ (j + 2) := by
      rw [hr, ← Real.rpow_natCast (q ^ (-(i : ℝ) / 2)) (j + 2), ← Real.rpow_mul hq0.le]
      congr 1; push_cast; ring
    rw [hpow] at hnum
    have hr_pow : r ^ (j + 2) = r ^ 2 * r ^ j := by rw [pow_add]; ring
    rw [hr_pow] at hnum
    have hj2pos : (0 : ℝ) < (j : ℝ) + 2 := by positivity
    rw [div_le_iff₀ hj2pos]
    have hjr0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
    nlinarith [hnum,
      mul_nonneg (mul_nonneg (mul_nonneg hgr0 (sq_nonneg r)) (pow_nonneg hr0 j)) hjr0]
  -- summability of the shifted series, and the peeling identity
  have hsum_shift : Summable (fun j => term (j + 1)) :=
    Summable.of_norm_bounded hgdom.summable hbound
  have hLpeel : F.L i = term 0 + ∑' j, term (j + 1) := by
    rw [hL_eq]; exact tsum_eq_zero_add' hsum_shift
  have hdiff : F.L i - F.s i = ∑' j, term (j + 1) := by rw [hLpeel, hf0]; ring
  rw [hdiff]
  -- bound the tail and simplify the geometric sum
  have hX : (0 : ℝ) ≤ q ^ (-(i : ℝ)) := Real.rpow_nonneg hq0.le _
  calc ‖∑' j, term (j + 1)‖
      ≤ ((g : ℝ) * r ^ 2) * (1 - r)⁻¹ := tsum_of_norm_bounded hgdom hbound
    _ ≤ 4 * (g : ℝ) * q ^ (-(i : ℝ)) := by
        rw [hr2eq]
        nlinarith [mul_le_mul_of_nonneg_left hinv4 (mul_nonneg hgr0 hX)]

/-! ## Lemma 4.1 — the small range `i ≤ g/2` -/

/-- The truncated Möbius approximation `s̃ᵢ = Σ_{ji ≤ g} μ(j)/j · L_{ji}`, depending
    only on `c₁,…,c_g`. -/
noncomputable def truncMobius (i : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 (g / i), ((ArithmeticFunction.moebius j : ℤ) : ℂ) / (j : ℂ) * F.L (j * i)

/-- Weil-type bound on `L`: `‖L m‖ ≤ 4g · q^{-m/2}` (for `q ≥ 4`, `m ≥ 1`). -/
theorem norm_L_le (hq : 4 ≤ q) {m : ℕ} (hm : 1 ≤ m) :
    ‖F.L m‖ ≤ 4 * (g : ℝ) * q ^ (-(m : ℝ) / 2) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hgr0 : (0 : ℝ) ≤ (g : ℝ) := by positivity
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  set R : ℝ := q ^ (-(m : ℝ) / 2) with hR
  have hR0 : 0 ≤ R := le_of_lt (Real.rpow_pos_of_pos hq0 _)
  have hR1 : R < 1 := by
    rw [hR]; exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  -- `R ≤ 1/2`, via `(q^{-1/2})² = q⁻¹ ≤ 1/4`
  have hRhalf : R ≤ 1 / 2 := by
    have hs2 : (q ^ (-(1 : ℝ) / 2)) ^ 2 = (q : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast (q ^ (-(1 : ℝ) / 2)) 2, ← Real.rpow_mul hq0.le,
        show (-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = -(1 : ℝ) by push_cast; ring, Real.rpow_neg hq0.le,
        Real.rpow_one]
    have hs0 : 0 ≤ q ^ (-(1 : ℝ) / 2) := le_of_lt (Real.rpow_pos_of_pos hq0 _)
    have hqinv : (q : ℝ)⁻¹ ≤ 1 / 4 := by
      rw [inv_eq_one_div, div_le_div_iff₀ hq0 (by norm_num : (0 : ℝ) < 4)]; linarith
    have hs : q ^ (-(1 : ℝ) / 2) ≤ 1 / 2 := by nlinarith [hs2, hs0, hqinv]
    calc R = q ^ (-(m : ℝ) / 2) := hR
      _ ≤ q ^ (-(1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ 1 / 2 := hs
  have hbound : ∀ j : ℕ, ‖F.s ((j + 1) * m) / ((j + 1 : ℕ) : ℂ)‖ ≤ (2 * (g : ℝ) * R) * R ^ j := by
    intro j
    rw [norm_div, Complex.norm_natCast]
    have hnum : ‖F.s ((j + 1) * m)‖ ≤ 2 * (g : ℝ) * q ^ (-(((j + 1) * m : ℕ) : ℝ) / 2) :=
      F.norm_s_le hq0.le _
    have hpow : q ^ (-(((j + 1) * m : ℕ) : ℝ) / 2) = R ^ (j + 1) := by
      rw [hR, ← Real.rpow_natCast (q ^ (-(m : ℝ) / 2)) (j + 1), ← Real.rpow_mul hq0.le]
      congr 1; push_cast; ring
    rw [hpow, pow_succ] at hnum
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ))]
    have hcast : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    nlinarith [hnum, hcast,
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hgr0) (pow_nonneg hR0 j), hR0,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hgr0) hR0) (pow_nonneg hR0 j)]
  have hHS : HasSum (fun j : ℕ => (2 * (g : ℝ) * R) * R ^ j) ((2 * (g : ℝ) * R) * (1 - R)⁻¹) :=
    (hasSum_geometric_of_lt_one hR0 hR1).mul_left _
  have h1 : ‖F.L m‖ ≤ (2 * (g : ℝ) * R) * (1 - R)⁻¹ := by
    unfold FrobeniusData.L; exact tsum_of_norm_bounded hHS hbound
  have hinv2 : (1 - R)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : (0 : ℝ) < 1 - R)]; linarith
  calc ‖F.L m‖ ≤ (2 * (g : ℝ) * R) * (1 - R)⁻¹ := h1
    _ ≤ 4 * (g : ℝ) * R := by nlinarith [hinv2, hR0, hgr0, mul_nonneg hgr0 hR0]
    _ = 4 * (g : ℝ) * q ^ (-(m : ℝ) / 2) := by rw [hR]

/-- Tail bound after peeling the first two terms of `L`: `‖L i - sᵢ - s_{2i}/2‖ ≤
    4g q^{-3i/2}` (for `q ≥ 4`, `i ≥ 1`).  The residual `Σ_{r≥3} s_{ri}/r` is a geometric
    series in `r = q^{-i/2}` starting at `r³`. -/
theorem norm_L_sub_two (hq : 4 ≤ q) {i : ℕ} (hi : 1 ≤ i) :
    ‖F.L i - F.s i - F.s (2 * i) / 2‖ ≤ 4 * (g : ℝ) * q ^ (-(3 * (i : ℝ)) / 2) := by
  have hq0 : (0 : ℝ) < q := by linarith
  have hgr0 : (0 : ℝ) ≤ (g : ℝ) := by positivity
  have hir : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  set r : ℝ := q ^ (-(i : ℝ) / 2) with hr
  have hr0 : 0 ≤ r := le_of_lt (Real.rpow_pos_of_pos hq0 _)
  have hr1 : r < 1 := by
    rw [hr]; exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hrhalf : r ≤ 1 / 2 := by
    have h1 : r ≤ q ^ (-(1 : ℝ) / 2) := by
      rw [hr]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : (q ^ (-(1 : ℝ) / 2)) ^ 2 = (q : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast (q ^ (-(1 : ℝ) / 2)) 2, ← Real.rpow_mul hq0.le,
        show (-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = -(1 : ℝ) by push_cast; ring, Real.rpow_neg hq0.le,
        Real.rpow_one]
    have h4 : (0 : ℝ) ≤ q ^ (-(1 : ℝ) / 2) := le_of_lt (Real.rpow_pos_of_pos hq0 _)
    have h3 : (q : ℝ)⁻¹ ≤ 1 / 4 := by
      rw [inv_eq_one_div, div_le_div_iff₀ hq0 (by norm_num)]; linarith
    nlinarith [h1, h2, h3, h4]
  set term : ℕ → ℂ := fun j => F.s ((j + 1) * i) / ((j + 1 : ℕ) : ℂ) with hterm
  have htbound : ∀ j, ‖term j‖ ≤ (2 * (g : ℝ) * r) * r ^ j := by
    intro j
    rw [hterm]; simp only [norm_div, Complex.norm_natCast]
    have hnum : ‖F.s ((j + 1) * i)‖ ≤ 2 * (g : ℝ) * q ^ (-(((j + 1) * i : ℕ) : ℝ) / 2) :=
      F.norm_s_le hq0.le _
    have hpow : q ^ (-(((j + 1) * i : ℕ) : ℝ) / 2) = r ^ (j + 1) := by
      rw [hr, ← Real.rpow_natCast (q ^ (-(i : ℝ) / 2)) (j + 1), ← Real.rpow_mul hq0.le]
      congr 1; push_cast; ring
    rw [hpow, pow_succ] at hnum
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ))]
    have hcast : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j + 1)
    nlinarith [hnum, hcast,
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hgr0) (mul_nonneg (pow_nonneg hr0 j) hr0)]
  have hf_sum : Summable term :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) htbound
      ((hasSum_geometric_of_lt_one hr0 hr1).mul_left _).summable)
  have ht0 : term 0 = F.s i := by rw [hterm]; simp
  have ht1 : term 1 = F.s (2 * i) / 2 := by rw [hterm]; norm_num
  have hpeel := ((summable_nat_add_iff 2).mpr hf_sum).sum_add_tsum_nat_add'
  rw [Finset.sum_range_succ, Finset.sum_range_one, ht0, ht1] at hpeel
  have hdiff : F.L i - F.s i - F.s (2 * i) / 2 = ∑' j, term (j + 2) := by
    rw [show F.L i = ∑' j, term j from rfl, ← hpeel]; ring
  rw [hdiff]
  have htail : ‖∑' j, term (j + 2)‖ ≤ (2 * (g : ℝ) * r ^ 3) * (1 - r)⁻¹ := by
    refine tsum_of_norm_bounded
      ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (2 * (g : ℝ) * r ^ 3)) (fun j => ?_)
    calc ‖term (j + 2)‖ ≤ (2 * (g : ℝ) * r) * r ^ (j + 2) := htbound (j + 2)
      _ = (2 * (g : ℝ) * r ^ 3) * r ^ j := by rw [pow_add]; ring
  have hr3eq : r ^ 3 = q ^ (-(3 * (i : ℝ)) / 2) := by
    rw [hr, ← Real.rpow_natCast (q ^ (-(i : ℝ) / 2)) 3, ← Real.rpow_mul hq0.le]
    congr 1; push_cast; ring
  have hinv2 : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : (0 : ℝ) < 1 - r)]; linarith
  calc ‖∑' j, term (j + 2)‖ ≤ (2 * (g : ℝ) * r ^ 3) * (1 - r)⁻¹ := htail
    _ ≤ 4 * (g : ℝ) * r ^ 3 := by
        nlinarith [hinv2, hr0, hgr0, pow_nonneg hr0 3, mul_nonneg hgr0 (pow_nonneg hr0 3)]
    _ = 4 * (g : ℝ) * q ^ (-(3 * (i : ℝ)) / 2) := by rw [hr3eq]

/-- **Möbius inversion** (Lemma 4.1 input): `sᵢ = Σ_{j≥1} μ(j)/j · L(ji)`.  This is the
    Möbius inversion over multiples dual to `L(m) = Σ_{r≥1} s(rm)/r`; it is assumed here
    (its proof is a Dirichlet-convolution rearrangement of a double infinite series). -/
theorem mobius_inversion (hq : 4 ≤ q) {i : ℕ} (hi : 1 ≤ i) :
    F.s i = ∑' j : ℕ, ((ArithmeticFunction.moebius j : ℤ) : ℂ) / (j : ℂ) * F.L (j * i) := by
  sorry

-- This proof chains many `rpow`/`tsum` rewrites and several `nlinarith` calls over the
-- `set`-abstracted summand, so it needs more than the default heartbeat budget.
set_option maxHeartbeats 1000000 in
/-- **Small range** (Lemma 4.1): for `1 ≤ i ≤ g/2` and `q > 256 g²`,
    `‖sᵢ - s̃ᵢ‖ < ½ q^{-i}`; hence `sᵢ` is determined by `c₁,…,c_g`.

    From the Möbius inversion `sᵢ = Σ_{j≥1} μ(j)/j L(ji)`, the truncation error is the
    tail `Σ_{j > g/i} μ(j)/j L(ji)`, bounded by `Σ_{j > g/i} 4g q^{-ji/2}` (a geometric
    series), which `q > 256 g²` makes `< ½ q^{-i}`. -/
theorem small_range (hq : 256 * (g : ℝ) ^ 2 < q) {i : ℕ} (hi : 1 ≤ i) (hig : 2 * i ≤ g) :
    ‖F.s i - F.truncMobius i‖ < 1 / (2 * (q ^ i : ℝ)) := by
  classical
  have hg1 : 1 ≤ g := by omega
  have hgr1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg1
  have hg2 : (1 : ℝ) ≤ (g : ℝ) ^ 2 := one_le_pow₀ hgr1
  have hq4 : (4 : ℝ) ≤ q := by nlinarith [hq, hg2]
  have hq0 : (0 : ℝ) < q := by linarith
  have hir : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  -- `g/i ≥ 2`, and the index bounds `(g/i+1)i > g`, `(g/i-1)i ≥ 1`
  have hJ2 : 2 ≤ g / i := (Nat.le_div_iff_mul_le hi).mpr (by omega)
  have hidxlo : 1 ≤ (g / i - 1) * i := by
    have := Nat.mul_pos (by omega : 0 < g / i - 1) hi; omega
  set r : ℝ := q ^ (-(i : ℝ) / 2) with hr
  have hr0 : 0 ≤ r := le_of_lt (Real.rpow_pos_of_pos hq0 _)
  have hQpos : (0 : ℝ) < q ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hq0 _
  -- `q^{-1/2} < 1/(16g)`
  have hQ : q ^ (-(1 : ℝ) / 2) < 1 / (16 * (g : ℝ)) := by
    have hs2 : (q ^ (-(1 : ℝ) / 2)) ^ 2 = (q : ℝ)⁻¹ := by
      rw [← Real.rpow_natCast (q ^ (-(1 : ℝ) / 2)) 2, ← Real.rpow_mul hq0.le,
        show (-(1 : ℝ) / 2) * ((2 : ℕ) : ℝ) = -(1 : ℝ) by push_cast; ring, Real.rpow_neg hq0.le,
        Real.rpow_one]
    have hY2 : (q ^ (-(1 : ℝ) / 2) * (16 * (g : ℝ))) ^ 2 < 1 := by
      have he : (q ^ (-(1 : ℝ) / 2) * (16 * (g : ℝ))) ^ 2 = 256 * (g : ℝ) ^ 2 * (q : ℝ)⁻¹ := by
        rw [mul_pow, hs2]; ring
      rw [he, ← div_eq_mul_inv, div_lt_one hq0]; linarith [hq]
    have hYnn : (0 : ℝ) ≤ q ^ (-(1 : ℝ) / 2) * (16 * (g : ℝ)) := mul_nonneg hQpos.le (by positivity)
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 16 * (g : ℝ))]
    nlinarith [hY2, hYnn]
  have hr_le : r ≤ q ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hr_lt_half : r < 1 / 2 := by
    have : q ^ (-(1 : ℝ) / 2) < 1 / 2 := by
      have : (1 : ℝ) / (16 * (g : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hgr1]
      linarith [hQ]
    linarith [hr_le]
  have hr1 : r < 1 := by linarith
  -- the summand
  set f : ℕ → ℂ := fun j => ((ArithmeticFunction.moebius j : ℤ) : ℂ) / (j : ℂ) * F.L (j * i)
    with hf
  have hf0 : f 0 = 0 := by simp [hf, ArithmeticFunction.map_zero]
  -- `‖f k‖ ≤ 4g r^k`
  have hfbd : ∀ k, ‖f k‖ ≤ 4 * (g : ℝ) * r ^ k := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; rw [hf0, norm_zero]; positivity
    · rw [hf]
      simp only [norm_mul, norm_div, Complex.norm_intCast, Complex.norm_natCast]
      have hμ : |((ArithmeticFunction.moebius k : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
      have hki : (1 : ℝ) ≤ ((k : ℝ)) := by exact_mod_cast hkpos
      have hL : ‖F.L (k * i)‖ ≤ 4 * (g : ℝ) * q ^ (-((k * i : ℕ) : ℝ) / 2) :=
        F.norm_L_le hq4 (by have := Nat.mul_pos hkpos hi; omega)
      have hpow : q ^ (-((k * i : ℕ) : ℝ) / 2) = r ^ k := by
        rw [hr, ← Real.rpow_natCast (q ^ (-(i : ℝ) / 2)) k, ← Real.rpow_mul hq0.le]
        congr 1; push_cast; ring
      rw [hpow] at hL
      have hLnn : (0 : ℝ) ≤ ‖F.L (k * i)‖ := norm_nonneg _
      have h4gr : (0 : ℝ) ≤ 4 * (g : ℝ) * r ^ k := by positivity
      -- `(|μk|/k) * ‖L‖ ≤ 1 * (4g r^k)`
      calc |((ArithmeticFunction.moebius k : ℤ) : ℝ)| / (k : ℝ) * ‖F.L (k * i)‖
          ≤ 1 * (4 * (g : ℝ) * r ^ k) := by
            apply mul_le_mul _ hL hLnn (by norm_num)
            rw [div_le_one (by linarith)]; linarith [hμ, hki]
        _ = 4 * (g : ℝ) * r ^ k := one_mul _
  -- summability
  have hgeom : Summable (fun k : ℕ => 4 * (g : ℝ) * r ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hf_norm_sum : Summable (fun k => ‖f k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hfbd hgeom
  have hf_sum : Summable f := hf_norm_sum.of_norm
  -- split off the truncated head
  have htrunc : F.truncMobius i = ∑ j ∈ Finset.range (g / i + 1), f j := by
    unfold FrobeniusData.truncMobius
    refine Finset.sum_subset (fun x hx => ?_) (fun x hx hx' => ?_)
    · rw [Finset.mem_Icc] at hx; rw [Finset.mem_range]; omega
    · rw [Finset.mem_range] at hx; rw [Finset.mem_Icc] at hx'
      have : x = 0 := by omega
      rw [this]; exact hf0
  have hmi : F.s i = ∑' j, f j := mobius_inversion F hq4 hi
  have hsplit := ((summable_nat_add_iff (g / i + 1)).mpr hf_sum).sum_add_tsum_nat_add'
  have hdiff : F.s i - F.truncMobius i = ∑' j, f (j + (g / i + 1)) := by
    rw [hmi, htrunc, ← hsplit]; ring
  rw [hdiff]
  -- bound the tail by the geometric series
  have htail : ‖∑' j, f (j + (g / i + 1))‖ ≤ 4 * (g : ℝ) * r ^ (g / i + 1) * (1 - r)⁻¹ := by
    calc ‖∑' j, f (j + (g / i + 1))‖
        ≤ ∑' j, ‖f (j + (g / i + 1))‖ :=
          norm_tsum_le_tsum_norm ((summable_nat_add_iff (g / i + 1)).mpr hf_norm_sum)
      _ ≤ ∑' j, 4 * (g : ℝ) * r ^ (j + (g / i + 1)) :=
          Summable.tsum_le_tsum (fun j => hfbd _)
            ((summable_nat_add_iff (g / i + 1)).mpr hf_norm_sum)
            ((summable_nat_add_iff (g / i + 1)).mpr hgeom)
      _ = 4 * (g : ℝ) * r ^ (g / i + 1) * (1 - r)⁻¹ := by
          rw [show (fun j : ℕ => 4 * (g : ℝ) * r ^ (j + (g / i + 1)))
              = fun j : ℕ => (4 * (g : ℝ) * r ^ (g / i + 1)) * r ^ j from
            funext (fun j => by rw [pow_add]; ring),
            tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  -- the geometric bound is `< ½ q^{-i}`
  have hr2eq : r ^ 2 = ((q : ℝ) ^ i)⁻¹ := by
    rw [hr, ← Real.rpow_natCast (q ^ (-(i : ℝ) / 2)) 2, ← Real.rpow_mul hq0.le,
      ← Real.rpow_natCast q i, ← Real.rpow_neg hq0.le]
    congr 1; push_cast; ring
  have hr2pos : 0 < r ^ 2 := by positivity
  have hrJ1 : r ^ (g / i - 1) ≤ q ^ (-(1 : ℝ) / 2) := by
    rw [hr, ← Real.rpow_natCast (q ^ (-(i : ℝ) / 2)) (g / i - 1), ← Real.rpow_mul hq0.le]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have hcast : (1 : ℝ) ≤ ((g / i - 1 : ℕ) : ℝ) * (i : ℝ) := by exact_mod_cast hidxlo
    nlinarith [hcast]
  have hsplitpow : r ^ (g / i + 1) = r ^ 2 * r ^ (g / i - 1) := by
    rw [← pow_add]; congr 1; omega
  have hinv2 : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : (0 : ℝ) < 1 - r)]; linarith
  have hfinal : 4 * (g : ℝ) * r ^ (g / i + 1) * (1 - r)⁻¹ < 1 / (2 * (q ^ i : ℝ)) := by
    rw [show (1 : ℝ) / (2 * (q ^ i : ℝ)) = 1 / 2 * r ^ 2 by rw [hr2eq]; ring, hsplitpow]
    have key : 4 * (g : ℝ) * q ^ (-(1 : ℝ) / 2) * (1 - r)⁻¹ < 1 / 2 := by
      have h1 : 4 * (g : ℝ) * q ^ (-(1 : ℝ) / 2) * (1 - r)⁻¹
          ≤ 4 * (g : ℝ) * q ^ (-(1 : ℝ) / 2) * 2 := by
        apply mul_le_mul_of_nonneg_left hinv2; positivity
      have h2 : 4 * (g : ℝ) * q ^ (-(1 : ℝ) / 2) * 2 < 1 / 2 := by
        have h3 : 8 * (g : ℝ) * q ^ (-(1 : ℝ) / 2) < 8 * (g : ℝ) * (1 / (16 * (g : ℝ))) :=
          mul_lt_mul_of_pos_left hQ (by positivity)
        have hgne : (g : ℝ) ≠ 0 := by positivity
        have h4 : 8 * (g : ℝ) * (1 / (16 * (g : ℝ))) = 1 / 2 := by field_simp; ring
        nlinarith [h3, h4]
      linarith [h1, h2]
    -- multiply `key` by `r² > 0` and use `r^{g/i-1} ≤ q^{-1/2}`
    have hbound2 : 4 * (g : ℝ) * (r ^ 2 * r ^ (g / i - 1)) * (1 - r)⁻¹
        ≤ 4 * (g : ℝ) * (r ^ 2 * q ^ (-(1 : ℝ) / 2)) * (1 - r)⁻¹ := by
      gcongr
    calc 4 * (g : ℝ) * (r ^ 2 * r ^ (g / i - 1)) * (1 - r)⁻¹
        ≤ 4 * (g : ℝ) * (r ^ 2 * q ^ (-(1 : ℝ) / 2)) * (1 - r)⁻¹ := hbound2
      _ = r ^ 2 * (4 * (g : ℝ) * q ^ (-(1 : ℝ) / 2) * (1 - r)⁻¹) := by ring
      _ < r ^ 2 * (1 / 2) := by apply mul_lt_mul_of_pos_left key hr2pos
      _ = 1 / 2 * r ^ 2 := by ring
  exact lt_of_le_of_lt htail hfinal

/-! ## Lemma 5.1 — the large-range reconstruction

For `g < m ≤ 2g`, Newton's identity `(2.5)` isolates the top power sum `sₘ`:
`sₘ = (-1)^{m-1} (m eₘ - Σ_{i=1}^{m-1} (-1)^{i-1} e_{m-i} sᵢ)`, and the functional
equation replaces `eₘ` by `q^{-(m-g)} e_{2g-m}`.  Unlike the schematic version, this
reconstruction `sEst m` is *exact* (`sEst_eq`): every term is either a lower power sum
`sᵢ` (`i < m`) or an elementary symmetric function of index `< m` or `≤ g`. -/

/-- Reconstruction of `sₘ` (`g < m ≤ 2g`) from lower power sums and the functional
    equation, via Newton's identity solved for the top term. -/
noncomputable def sEst (m : ℕ) : ℂ :=
  (-1) ^ (m - 1) * ((m : ℂ) * ((q : ℂ) ^ (-(((m - g : ℕ)) : ℤ)) * F.e (2 * g - m))
    - ∑ i ∈ Finset.Icc 1 (m - 1), (-1) ^ (i - 1) * F.e (m - i) * F.s i)

/-- **Large-range reconstruction** (Lemma 5.1): for `g < m ≤ 2g` the power sum `sₘ`
    is *exactly* `sEst m`, by Newton's identity and the functional equation. -/
theorem sEst_eq (hq : 0 < q) {m : ℕ} (hm : g < m) (hm2 : m ≤ 2 * g) :
    F.s m = F.sEst m := by
  obtain ⟨m', rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hN := newton_identity F (by omega : 1 ≤ m' + 1) hm2
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m' + 1)] at hN
  have he0 : F.e 0 = 1 := by simp [FrobeniusData.e]
  simp only [Nat.add_sub_cancel, Nat.sub_self] at hN
  rw [he0, mul_one] at hN
  have hfe : F.e (m' + 1) = (q : ℂ) ^ (-(((m' + 1 - g : ℕ)) : ℤ)) * F.e (2 * g - (m' + 1)) := by
    have hfe0 := functional_eq F hq (by omega : 1 ≤ m' + 1 - g) (by omega : m' + 1 - g ≤ g)
    rwa [show g + (m' + 1 - g) = m' + 1 by omega,
      show g - (m' + 1 - g) = 2 * g - (m' + 1) by omega] at hfe0
  unfold FrobeniusData.sEst
  simp only [Nat.add_sub_cancel]
  rw [← hfe, hN]
  have hsq : (-1 : ℂ) ^ m' * (-1) ^ m' = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  linear_combination (-F.s (m' + 1)) * hsq

/-- **Base case** (Lemma 5.3): for `q ≥ D^{2g}` and `g/2 < j ≤ g`, the seed error
    is within budget: `4g q^{-j} ≤ B_j`. -/
theorem base_case (hq : (Dconst g) ^ (2 * g) ≤ q) {j : ℕ} (hj : g < 2 * j) (hjg : j ≤ g) :
    4 * (g : ℝ) * q ^ (-(j : ℝ)) ≤ Bbudget g q j := by
  -- Equivalent to `4 D^{g-j} ≤ q^{(2j-g)/4}`; the slack is exactly `D^{1/2} ≥ 4`
  -- (from `D ≥ 16`) together with `q ≥ D^{2g}` and the integer bound `g + 1 ≤ 2j`.
  -- (Paper §5.)
  have hg1 : 1 ≤ g := by omega
  have hgr1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg1
  -- the partition function is positive, so `D = 16 g³ p(2g) ≥ 16`
  have hp : 0 < partitionCount (2 * g) := by
    change 0 < Nat.card (Nat.Partition (2 * g))
    have : Nonempty (Nat.Partition (2 * g)) := ⟨default⟩
    exact Nat.card_pos
  have hpr1 : (1 : ℝ) ≤ (partitionCount (2 * g) : ℝ) := by exact_mod_cast hp
  have hcube : (1 : ℝ) ≤ (g : ℝ) ^ 3 := one_le_pow₀ hgr1
  have hD16 : (16 : ℝ) ≤ Dconst g := by
    unfold Dconst
    nlinarith [hcube, hpr1, mul_nonneg (sub_nonneg.mpr hcube) (sub_nonneg.mpr hpr1)]
  have hD0 : (0 : ℝ) < Dconst g := by linarith
  have hD1 : (1 : ℝ) ≤ Dconst g := by linarith
  have hDpow1 : (1 : ℝ) ≤ (Dconst g) ^ (2 * g) := one_le_pow₀ hD1
  have hq1 : (1 : ℝ) ≤ q := le_trans hDpow1 hq
  have hq0 : (0 : ℝ) < q := by linarith
  -- the key integer inequality, cast to `ℝ`
  have hcast : (g : ℝ) + 1 ≤ 2 * (j : ℝ) := by
    have : g + 1 ≤ 2 * j := by omega
    exact_mod_cast this
  have hexp_nonneg : (0 : ℝ) ≤ (2 * (j : ℝ) - (g : ℝ)) / 4 := by linarith
  -- the reconstructed exponent `E = g(2j-g)/2 + (j-g)` satisfies `E ≥ 1/2`
  have hE : (1 : ℝ) / 2 ≤ (g : ℝ) * (2 * (j : ℝ) - (g : ℝ)) / 2 + ((j : ℝ) - (g : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left hcast (show (0 : ℝ) ≤ (g : ℝ) + 1 by linarith)]
  -- `16^(1/2) = 4`, hence `4 ≤ D^(1/2) ≤ D^E`
  have h16 : (16 : ℝ) ^ ((1 / 2) : ℝ) = 4 := by
    rw [show (16 : ℝ) = (4 : ℝ) ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast 4 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
      show ((2 : ℕ) : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
  have hD4 : (4 : ℝ) ≤ (Dconst g) ^ ((1 / 2) : ℝ) := by
    rw [← h16]; exact Real.rpow_le_rpow (by norm_num) hD16 (by norm_num)
  have hDElow : (Dconst g) ^ ((1 / 2) : ℝ)
      ≤ (Dconst g) ^ ((g : ℝ) * (2 * (j : ℝ) - (g : ℝ)) / 2 + ((j : ℝ) - (g : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le hD1 hE
  have hCstepC : (4 : ℝ)
      ≤ (Dconst g) ^ ((g : ℝ) * (2 * (j : ℝ) - (g : ℝ)) / 2 + ((j : ℝ) - (g : ℝ))) :=
    le_trans hD4 hDElow
  -- `q ≥ D^{2g}` as an `rpow`, then monotonicity gives Step A
  have hDqr : (Dconst g) ^ (((2 * g : ℕ)) : ℝ) ≤ q := by rw [Real.rpow_natCast]; exact hq
  have hStepA : (Dconst g) ^ ((g : ℝ) * (2 * (j : ℝ) - (g : ℝ)) / 2)
      ≤ q ^ ((2 * (j : ℝ) - (g : ℝ)) / 4) := by
    have h1 : ((Dconst g) ^ (((2 * g : ℕ)) : ℝ)) ^ ((2 * (j : ℝ) - (g : ℝ)) / 4)
        ≤ q ^ ((2 * (j : ℝ) - (g : ℝ)) / 4) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hD0.le _) hDqr hexp_nonneg
    rwa [← Real.rpow_mul hD0.le,
      show ((2 * g : ℕ) : ℝ) * ((2 * (j : ℝ) - (g : ℝ)) / 4)
        = (g : ℝ) * (2 * (j : ℝ) - (g : ℝ)) / 2 by push_cast; ring] at h1
  have hStepB :
      (Dconst g) ^ ((g : ℝ) * (2 * (j : ℝ) - (g : ℝ)) / 2) * (Dconst g) ^ ((j : ℝ) - (g : ℝ))
        ≤ q ^ ((2 * (j : ℝ) - (g : ℝ)) / 4) * (Dconst g) ^ ((j : ℝ) - (g : ℝ)) :=
    mul_le_mul_of_nonneg_right hStepA (Real.rpow_nonneg hD0.le _)
  -- assemble `4 ≤ q^{(2j-g)/4} · D^{j-g}`
  have hCORE3 : (4 : ℝ) ≤ q ^ ((2 * (j : ℝ) - (g : ℝ)) / 4) * (Dconst g) ^ ((j : ℝ) - (g : ℝ)) := by
    calc (4 : ℝ)
        ≤ (Dconst g) ^ ((g : ℝ) * (2 * (j : ℝ) - (g : ℝ)) / 2 + ((j : ℝ) - (g : ℝ))) := hCstepC
      _ = (Dconst g) ^ ((g : ℝ) * (2 * (j : ℝ) - (g : ℝ)) / 2) * (Dconst g) ^ ((j : ℝ) - (g : ℝ)) :=
          Real.rpow_add hD0 _ _
      _ ≤ q ^ ((2 * (j : ℝ) - (g : ℝ)) / 4) * (Dconst g) ^ ((j : ℝ) - (g : ℝ)) := hStepB
  -- recombine the `q` exponents: `-j/2 - g/4 = -j + (2j-g)/4`
  have hrw : q ^ (-(j : ℝ) / 2 - (g : ℝ) / 4)
      = q ^ (-(j : ℝ)) * q ^ ((2 * (j : ℝ) - (g : ℝ)) / 4) := by
    rw [← Real.rpow_add hq0]; congr 1; ring
  have hCORE2 : 4 * q ^ (-(j : ℝ))
      ≤ q ^ (-(j : ℝ) / 2 - (g : ℝ) / 4) * (Dconst g) ^ ((j : ℝ) - (g : ℝ)) := by
    calc 4 * q ^ (-(j : ℝ)) = q ^ (-(j : ℝ)) * 4 := by ring
      _ ≤ q ^ (-(j : ℝ)) * (q ^ ((2 * (j : ℝ) - (g : ℝ)) / 4) * (Dconst g) ^ ((j : ℝ) - (g : ℝ))) :=
          mul_le_mul_of_nonneg_left hCORE3 (Real.rpow_nonneg hq0.le _)
      _ = q ^ (-(j : ℝ) / 2 - (g : ℝ) / 4) * (Dconst g) ^ ((j : ℝ) - (g : ℝ)) := by rw [hrw]; ring
  -- multiply through by `g ≥ 0`
  unfold Bbudget
  calc 4 * (g : ℝ) * q ^ (-(j : ℝ)) = (g : ℝ) * (4 * q ^ (-(j : ℝ))) := by ring
    _ ≤ (g : ℝ) * (q ^ (-(j : ℝ) / 2 - (g : ℝ) / 4) * (Dconst g) ^ ((j : ℝ) - (g : ℝ))) :=
        mul_le_mul_of_nonneg_left hCORE2 (by linarith)
    _ = (g : ℝ) * q ^ (-(j : ℝ) / 2 - (g : ℝ) / 4) * (Dconst g) ^ ((j : ℝ) - (g : ℝ)) := by ring

/-! ## §6 — recovery of the power sums and the main theorem -/

/-- The denominator `z_μ = ∏_k k^{m_k} m_k!` of a partition term, as a complex number. -/
noncomputable def zPart (μ : Multiset ℕ) : ℂ :=
  ∏ k ∈ μ.toFinset, ((k : ℂ) ^ μ.count k * ((μ.count k).factorial : ℂ))

/-- **Explicit power-sum formula** (Lemma 5.1, eq:sm-formula), the one remaining Mathlib gap of §5:
    for `g < m ≤ 2g`, isolating the top term `sₘ` of the Newton–Girard expansion of `eₘ` and
    substituting `eₘ = q^{-(m-g)} e_{2g-m}` (the functional equation) expresses `sₘ` **purely
    through the lower power sums `s_k`**:
    `sₘ/m = -q^{-(m-g)} Σ_{μ ⊢ 2g-m} ∏(-s)/z_μ  +  Σ_{μ ⊢ m, m∉μ} ∏(-s)/z_μ`,
    with `z_μ = ∏_k k^{m_k} m_k!`.  This is the classical explicit Newton–Girard / Waring formula
    (from `∑ eₙ Tⁿ = ∏(1+βᵢT) = exp(∑_k (-1)^{k-1} s_k Tᵏ/k)`) specialised by the functional
    equation; Mathlib provides only the *recursive* Newton identities
    (`MvPolynomial.mul_esymm_eq_sum`), so it is assumed here as a `sorry`.  It is the sharp tool
    of §5: working purely in the `s_k` avoids the elementary symmetric functions `eₙ` (whose norms
    `≤ binom(2g,n) ≤ 4^g` would overwhelm the sub-exponential `D`), so the only non-exact factors
    are the `s_k` with `2k ≥ m`. -/
theorem sm_formula (hq : 0 < q) {m : ℕ} (hm : g < m) (hm2 : m ≤ 2 * g) :
    F.s m = (m : ℂ) *
      (-(q : ℂ) ^ (-((m - g : ℕ) : ℤ)) *
          ∑ μ : Nat.Partition (2 * g - m),
            (μ.parts.map (fun k => -F.s k)).prod / zPart μ.parts
        + ∑ μ ∈ Finset.univ.filter (fun μ : Nat.Partition m => m ∉ μ.parts),
            (μ.parts.map (fun k => -F.s k)).prod / zPart μ.parts) := by
  sorry

/-- **Telescoping product-difference bound** (obstacle 2 of §5).  For a common index
    multiset `t`, if every factor of `f` and `g` has norm `≤ B`, then
    `‖∏ f - ∏ g‖ ≤ (Σ ‖f a - g a‖) · B^{|t|-1}`.  Pure telescoping; this is the tool that
    converts the partition-formula difference into a sum of single-power-sum differences. -/
theorem norm_multiset_prod_map_sub_le {ι : Type*} (B : ℝ) (hB0 : 0 ≤ B) (f h : ι → ℂ) :
    ∀ t : Multiset ι, (∀ a ∈ t, ‖f a‖ ≤ B) → (∀ a ∈ t, ‖h a‖ ≤ B) →
      ‖(t.map f).prod - (t.map h).prod‖
        ≤ (t.map (fun a => ‖f a - h a‖)).sum * B ^ (Multiset.card t - 1) := by
  have hPbound : ∀ s : Multiset ι, (∀ a ∈ s, ‖f a‖ ≤ B) →
      ‖(s.map f).prod‖ ≤ B ^ Multiset.card s := by
    intro s
    induction s using Multiset.induction with
    | empty => intro _; simp
    | cons a s' ih =>
      intro hs
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ']
      exact mul_le_mul (hs a (Multiset.mem_cons_self a s'))
        (ih (fun b hb => hs b (Multiset.mem_cons_of_mem hb))) (norm_nonneg _) hB0
  intro t
  induction t using Multiset.induction with
  | empty => intro _ _; simp
  | cons a t' ih =>
    intro hf hh
    have hha : ‖h a‖ ≤ B := hh a (Multiset.mem_cons_self a t')
    have hf' : ∀ b ∈ t', ‖f b‖ ≤ B := fun b hb => hf b (Multiset.mem_cons_of_mem hb)
    have hh' : ∀ b ∈ t', ‖h b‖ ≤ B := fun b hb => hh b (Multiset.mem_cons_of_mem hb)
    have hPf : ‖(t'.map f).prod‖ ≤ B ^ Multiset.card t' := hPbound t' hf'
    have hIH := ih hf' hh'
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Multiset.card_cons,
      Nat.add_sub_cancel]
    have key : ‖f a * (t'.map f).prod - h a * (t'.map h).prod‖
        ≤ ‖f a - h a‖ * ‖(t'.map f).prod‖ + ‖h a‖ * ‖(t'.map f).prod - (t'.map h).prod‖ := by
      calc ‖f a * (t'.map f).prod - h a * (t'.map h).prod‖
          = ‖(f a - h a) * (t'.map f).prod + h a * ((t'.map f).prod - (t'.map h).prod)‖ := by
            congr 1; ring
        _ ≤ ‖(f a - h a) * (t'.map f).prod‖ + ‖h a * ((t'.map f).prod - (t'.map h).prod)‖ :=
            norm_add_le _ _
        _ = ‖f a - h a‖ * ‖(t'.map f).prod‖ + ‖h a‖ * ‖(t'.map f).prod - (t'.map h).prod‖ := by
            rw [norm_mul, norm_mul]
    have hstep1 : ‖f a - h a‖ * ‖(t'.map f).prod‖ ≤ ‖f a - h a‖ * B ^ Multiset.card t' :=
      mul_le_mul_of_nonneg_left hPf (norm_nonneg _)
    have hstep2 : ‖h a‖ * ‖(t'.map f).prod - (t'.map h).prod‖
        ≤ (t'.map (fun a => ‖f a - h a‖)).sum * B ^ Multiset.card t' := by
      rcases Nat.eq_zero_or_pos (Multiset.card t') with hc0 | hcpos
      · rw [Multiset.card_eq_zero.mp hc0]; simp
      · calc ‖h a‖ * ‖(t'.map f).prod - (t'.map h).prod‖
            ≤ B * ((t'.map (fun a => ‖f a - h a‖)).sum * B ^ (Multiset.card t' - 1)) :=
              mul_le_mul hha hIH (norm_nonneg _) hB0
          _ = (t'.map (fun a => ‖f a - h a‖)).sum * (B * B ^ (Multiset.card t' - 1)) := by ring
          _ = (t'.map (fun a => ‖f a - h a‖)).sum * B ^ Multiset.card t' := by
              congr 1; rw [← pow_succ']; congr 1; omega
    calc ‖f a * (t'.map f).prod - h a * (t'.map h).prod‖
        ≤ ‖f a - h a‖ * ‖(t'.map f).prod‖ + ‖h a‖ * ‖(t'.map f).prod - (t'.map h).prod‖ := key
      _ ≤ ‖f a - h a‖ * B ^ Multiset.card t'
          + (t'.map (fun a => ‖f a - h a‖)).sum * B ^ Multiset.card t' := add_le_add hstep1 hstep2
      _ = (‖f a - h a‖ + (t'.map (fun a => ‖f a - h a‖)).sum) * B ^ Multiset.card t' := by ring

/-- **Multiset product–norm bound**: `‖∏ (t.map f)‖ ≤ ∏ (t.map ‖f ·‖)`. -/
theorem norm_multiset_prod_map_le {ι : Type*} (f : ι → ℂ) (t : Multiset ι) :
    ‖(t.map f).prod‖ ≤ (t.map (fun a => ‖f a‖)).prod := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a t' ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact mul_le_mul_of_nonneg_left ih (norm_nonneg _)

/-- **Sharp one-differing-factor product bound**: if `f` and `h` agree on `rest`, the difference
    of the products over `a₀ ::ₘ rest` factors *exactly* as `‖f a₀ - h a₀‖ · ‖∏ (rest.map f)‖`.
    This is sharper than `norm_multiset_prod_map_sub_le` (no lossy uniform `B^{card-1}`), which is
    what makes the §5 estimate close: the exact small factors contribute their true norm product. -/
theorem norm_prod_sub_of_rest_eq {ι : Type*} (f h : ι → ℂ) (a₀ : ι) (rest : Multiset ι)
    (hrest : ∀ b ∈ rest, f b = h b) :
    ‖((a₀ ::ₘ rest).map f).prod - ((a₀ ::ₘ rest).map h).prod‖
      = ‖f a₀ - h a₀‖ * ‖(rest.map f).prod‖ := by
  have heq : rest.map f = rest.map h := Multiset.map_congr rfl hrest
  rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, ← heq,
    ← sub_mul, norm_mul]

/-- **Sharp product–norm bound for power sums**: `‖∏_{k∈t} s_k‖ ≤ (2g)^{|t|} · q^{-(Σt)/2}`.
    This is the (sharp, `q`-decaying) bound on the product of the *exact* small factors in §5. -/
theorem norm_prod_map_s_le (hq0 : 0 < q) (t : Multiset ℕ) :
    ‖(t.map F.s).prod‖ ≤ (2 * (g : ℝ)) ^ Multiset.card t * q ^ (-(t.sum : ℝ) / 2) := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a t' ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, Multiset.sum_cons,
      Nat.cast_add]
    calc ‖F.s a‖ * ‖(t'.map F.s).prod‖
        ≤ (2 * (g : ℝ) * q ^ (-(a : ℝ) / 2))
            * ((2 * (g : ℝ)) ^ Multiset.card t' * q ^ (-(t'.sum : ℝ) / 2)) :=
          mul_le_mul (F.norm_s_le hq0.le a) ih (norm_nonneg _) (by positivity)
      _ = (2 * (g : ℝ)) ^ (Multiset.card t' + 1) * q ^ (-((a : ℝ) + (t'.sum : ℝ)) / 2) := by
          rw [show -((a : ℝ) + (t'.sum : ℝ)) / 2 = -(a : ℝ) / 2 + -(t'.sum : ℝ) / 2 by ring,
            Real.rpow_add hq0, pow_succ]
          ring

/-- Negating every factor does not change the norm of a multiset product. -/
theorem norm_prod_map_neg {ι : Type*} (f : ι → ℂ) (t : Multiset ι) :
    ‖(t.map (fun a => -f a)).prod‖ = ‖(t.map f).prod‖ := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a t' ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
      norm_mul, norm_mul, norm_neg, ih]

/-- The partition denominator `z_μ` has norm `≥ 1` (each factor `k^{m_k} m_k! ≥ 1`), so dividing
    by it only shrinks norms — this is why the `z_μ` denominators may be dropped in the §5 bound. -/
theorem one_le_norm_zPart {t : Multiset ℕ} (ht : ∀ k ∈ t, 0 < k) : 1 ≤ ‖zPart t‖ := by
  have hz : zPart t
      = ((∏ k ∈ t.toFinset, k ^ t.count k * (t.count k).factorial : ℕ) : ℂ) := by
    simp only [zPart, Nat.cast_prod, Nat.cast_mul, Nat.cast_pow]
  rw [hz, Complex.norm_natCast]
  have hnat : 1 ≤ ∏ k ∈ t.toFinset, k ^ t.count k * (t.count k).factorial := by
    refine Finset.one_le_prod' (fun k hk => ?_)
    rw [Multiset.mem_toFinset] at hk
    exact Nat.mul_pos (pow_pos (ht k hk) _) (Nat.factorial_pos _)
  exact_mod_cast hnat

/-- **Monotonicity of the partition function**: `m ≤ n → p(m) ≤ p(n)`.  Proved by the injection
    `μ ↦ μ.parts + (n-m)·[1]` (append `n-m` ones), which is injective because multiset addition is
    cancellative.  (Mathlib has no monotonicity lemma for `Nat.Partition`.) -/
theorem partitionCount_mono {m n : ℕ} (hmn : m ≤ n) : partitionCount m ≤ partitionCount n := by
  unfold partitionCount
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_le_of_injective
    (fun μ => ⟨μ.parts + Multiset.replicate (n - m) 1, ?_, ?_⟩) ?_
  · intro i hi
    rw [Multiset.mem_add] at hi
    rcases hi with hi | hi
    · exact μ.parts_pos hi
    · have : i = 1 := Multiset.eq_of_mem_replicate hi
      omega
  · rw [Multiset.sum_add, μ.parts_sum, Multiset.sum_replicate, smul_eq_mul, mul_one]
    omega
  · intro μ₁ μ₂ heq
    have hp : μ₁.parts + Multiset.replicate (n - m) 1 = μ₂.parts + Multiset.replicate (n - m) 1 :=
      congrArg Nat.Partition.parts heq
    exact Nat.Partition.ext (add_right_cancel hp)

/-- **Factorization of a partition-term difference** (§5).  Splitting a partition `t` into its
    *large* parts `L = {k : 2k ≥ m}` and *small* parts `S` (which are exact by `hexact`), the
    `F₁`–`F₂` difference of the term `∏(-s)/z_t` factors as the difference over the large parts
    times the (sharp, exact) small product `≤ (2g)^{|S|} q^{-(ΣS)/2}`. -/
theorem partTerm_diff_factored (F₁ F₂ : FrobeniusData g q) (hq0 : 0 < q) {m : ℕ}
    (hexact : ∀ j, 1 ≤ j → 2 * j < m → F₁.s j = F₂.s j) (t : Multiset ℕ) (htpos : ∀ k ∈ t, 0 < k) :
    ‖(t.map (fun k => -F₁.s k)).prod / zPart t - (t.map (fun k => -F₂.s k)).prod / zPart t‖
      ≤ ‖((t.filter (fun k => m ≤ 2 * k)).map (fun k => -F₁.s k)).prod
          - ((t.filter (fun k => m ≤ 2 * k)).map (fun k => -F₂.s k)).prod‖
        * ((2 * (g : ℝ)) ^ Multiset.card (t.filter (fun k => ¬ m ≤ 2 * k))
            * q ^ (-((t.filter (fun k => ¬ m ≤ 2 * k)).sum : ℝ) / 2)) := by
  rw [div_sub_div_same, norm_div]
  refine le_trans (div_le_self (norm_nonneg _) (one_le_norm_zPart htpos)) ?_
  set L := t.filter (fun k => m ≤ 2 * k) with hLdef
  set S := t.filter (fun k => ¬ m ≤ 2 * k) with hSdef
  have hsplit : t = L + S := by rw [hLdef, hSdef]; exact (Multiset.filter_add_not _ _).symm
  have hSmap : S.map (fun k => -F₂.s k) = S.map (fun k => -F₁.s k) := by
    refine Multiset.map_congr rfl (fun k hk => ?_)
    rw [hSdef, Multiset.mem_filter] at hk
    rw [hexact k (htpos k hk.1) (by omega)]
  have hfactor : (t.map (fun k => -F₁.s k)).prod - (t.map (fun k => -F₂.s k)).prod
      = ((L.map (fun k => -F₁.s k)).prod - (L.map (fun k => -F₂.s k)).prod)
        * (S.map (fun k => -F₁.s k)).prod := by
    conv_lhs => rw [hsplit]
    rw [Multiset.map_add, Multiset.prod_add, Multiset.map_add, Multiset.prod_add, hSmap]
    ring
  rw [hfactor, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_prod_map_neg]
  exact F₁.norm_prod_map_s_le hq0 S

-- The §5 induction step bundles the partition-formula reduction, the per-partition combinatorial
-- estimates, and the `rpow` closure; its elaboration needs more than the default heartbeat budget.
set_option maxHeartbeats 1600000 in
/-- **Per-step reconstruction budget** (§5, the induction step Lemma 5.2): for `g < m ≤ 2g`,
    if the small-index power sums are *exact* (`F₁.s_j = F₂.s_j` whenever `2j < m`, i.e.
    `j ≤ ⌈m/2⌉-1`) and the budget `‖F₁.s_j - F₂.s_j‖ ≤ 2 B_j` holds for all `j < m`, then the
    budget holds at `m`.

    The exactness hypothesis `hexact` is **essential** and faithful to the paper: it is what
    forces the only error-bearing factor of the partition formula `sm-formula` to carry an
    index `k₀ ≥ ⌈m/2⌉`, so that *at most one* such large index occurs and the estimate is
    first-order.  Without it, the multi-factor partition terms blow up by `(2g)^M` and the
    bound fails — which is why the earlier pure-budget form was not provable.

    The proof is now **complete except for the two per-partition estimates** (`hperμ`, the
    combinatorial core): everything else is verified — the reduction through the explicit
    partition formula `sm_formula`, the norm reduction to the two partition sums, the partition
    count `≤ p(2g)` (`partitionCount_mono`), and the full `rpow` **closure** to `2 B_m` (the
    delicate constant arithmetic, closing because `8g³p(2g)/D = ½` with room to spare).  The
    remaining `hperμ` bounds each partition term `‖∏(-s)/z_μ‖`-difference: by `hexact` only the
    parts with `2k ≥ m` differ, at most one such (sum to `≥ m`), so `norm_prod_sub_of_rest_eq`
    factors out the single `Δs_{k₀} ≤ 2 B_{k₀}` times the exact small product (the even case
    `m = 2i` additionally has the two-large term `{m/2, m/2}`). -/
theorem reconstruction_step (hg : 2 ≤ g) (hq : Qbound g < q) (F₁ F₂ : FrobeniusData g q)
    (_hLeq : ∀ k, 1 ≤ k → k ≤ g → F₁.L k = F₂.L k) {m : ℕ} (hm1 : g < m) (hm2 : m ≤ 2 * g)
    (hexact : ∀ j, 1 ≤ j → 2 * j < m → F₁.s j = F₂.s j)
    (ihbud : ∀ j, 1 ≤ j → j < m → ‖F₁.s j - F₂.s j‖ ≤ 2 * Bbudget g q j) :
    ‖F₁.s m - F₂.s m‖ ≤ 2 * Bbudget g q m := by
  classical
  have hgr1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast (by omega : 1 ≤ g)
  have hp : 0 < partitionCount (2 * g) := by
    change 0 < Nat.card (Nat.Partition (2 * g))
    have : Nonempty (Nat.Partition (2 * g)) := ⟨default⟩
    exact Nat.card_pos
  have hpr1 : (1 : ℝ) ≤ (partitionCount (2 * g) : ℝ) := by exact_mod_cast hp
  have hcube : (1 : ℝ) ≤ (g : ℝ) ^ 3 := one_le_pow₀ hgr1
  have h16g3 : 16 * (g : ℝ) ^ 3 ≤ Dconst g := by
    unfold Dconst
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 16 * (g : ℝ) ^ 3) (sub_nonneg.mpr hpr1)]
  have hD16 : (16 : ℝ) ≤ Dconst g := by nlinarith [h16g3, hcube]
  have hD0 : (0 : ℝ) < Dconst g := by linarith
  have hD1 : (1 : ℝ) ≤ Dconst g := by linarith
  have hq256 : 256 * (g : ℝ) ^ 2 < q := by
    have step1 : 256 * (g : ℝ) ^ 2 ≤ (Dconst g) ^ 2 := by
      have hh : 256 * (g : ℝ) ^ 6 ≤ (Dconst g) ^ 2 := by
        calc 256 * (g : ℝ) ^ 6 = (16 * (g : ℝ) ^ 3) ^ 2 := by ring
          _ ≤ (Dconst g) ^ 2 := pow_le_pow_left₀ (by positivity) h16g3 2
      linarith [hh, pow_le_pow_right₀ hgr1 (show (2 : ℕ) ≤ 6 by norm_num)]
    have step2 : (Dconst g) ^ 2 ≤ (Dconst g) ^ (2 * g + 2) := pow_le_pow_right₀ hD1 (by omega)
    have hQ : 256 * (g : ℝ) ^ 2 ≤ Qbound g := by unfold Qbound; linarith [step1, step2]
    linarith [hQ, hq]
  have hg2_1 : (1 : ℝ) ≤ (g : ℝ) ^ 2 := one_le_pow₀ hgr1
  have hq0 : (0 : ℝ) < q := by nlinarith [hq256, hg2_1]
  -- the per-partition-sum bounds (the combinatorial core of §5; math verified, isolated):
  -- each partition term's difference reduces — by exactness of the small `s_k` (`hexact`) and the
  -- "at most one large part" structure — to a single `Δs_{k₀} ≤ 2 B_{k₀}` times the (sharp) product
  -- of the exact factors, and there are `≤ partitionCount (2g)` partitions (`partitionCount_mono`).
  set V₂ : ℝ := 4 * (g : ℝ) ^ 2 * q ^ (-(m : ℝ) / 2 - (g : ℝ) / 4) * (Dconst g) ^ ((m : ℝ) - 1 - g)
    with hV₂def
  rw [F₁.sm_formula hq0 hm1 hm2,
    F₂.sm_formula hq0 hm1 hm2]
  set S11 : ℂ := ∑ μ : Nat.Partition (2 * g - m), (μ.parts.map (fun k => -F₁.s k)).prod / zPart μ.parts
    with hS11
  set S12 : ℂ := ∑ μ : Nat.Partition (2 * g - m), (μ.parts.map (fun k => -F₂.s k)).prod / zPart μ.parts
    with hS12
  set S21 : ℂ := ∑ μ ∈ Finset.univ.filter (fun μ : Nat.Partition m => m ∉ μ.parts),
      (μ.parts.map (fun k => -F₁.s k)).prod / zPart μ.parts with hS21
  set S22 : ℂ := ∑ μ ∈ Finset.univ.filter (fun μ : Nat.Partition m => m ∉ μ.parts),
      (μ.parts.map (fun k => -F₂.s k)).prod / zPart μ.parts with hS22
  have hbnd1 : ‖S11 - S12‖ ≤ (partitionCount (2 * g) : ℝ) * (2 * Bbudget g q (2 * g - m)) := by
    have hB2gmnn : (0 : ℝ) ≤ 2 * Bbudget g q (2 * g - m) := by
      unfold Bbudget
      exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by positivity)
        (Real.rpow_nonneg hq0.le _)) (Real.rpow_nonneg hD0.le _))
    -- per-partition estimate (the §5 combinatorial core): at most one large part, sharp factoring
    have h2gD : 2 * (g : ℝ) ≤ Dconst g := by
      nlinarith [h16g3, hgr1, one_le_pow₀ hgr1 (n := 3)]
    have hperμ : ∀ μ : Nat.Partition (2 * g - m),
        ‖(μ.parts.map (fun k => -F₁.s k)).prod / zPart μ.parts
          - (μ.parts.map (fun k => -F₂.s k)).prod / zPart μ.parts‖
          ≤ 2 * Bbudget g q (2 * g - m) := by
      intro μ
      have hμpos : ∀ k ∈ μ.parts, 0 < k := fun k hk => μ.parts_pos hk
      refine le_trans (partTerm_diff_factored F₁ F₂ hq0 hexact μ.parts hμpos) ?_
      set L := μ.parts.filter (fun k => m ≤ 2 * k) with hLdef
      set S := μ.parts.filter (fun k => ¬ m ≤ 2 * k) with hSdef
      have hsplit : μ.parts = L + S := by rw [hLdef, hSdef]; exact (Multiset.filter_add_not _ _).symm
      have hScard : Multiset.card S ≤ S.sum := by
        have h1 : ∀ k ∈ S, 1 ≤ k := by
          intro k hk; rw [hSdef, Multiset.mem_filter] at hk; exact μ.parts_pos hk.1
        simpa using Multiset.card_nsmul_le_sum h1
      -- at most one large part (two would sum to `≥ m > 2g - m`)
      have hLsum : L.sum ≤ 2 * g - m := by
        have h : L.sum ≤ μ.parts.sum := by rw [hsplit, Multiset.sum_add]; exact Nat.le_add_right _ _
        rwa [μ.parts_sum] at h
      have hLcard : Multiset.card L ≤ 1 := by
        by_contra hc
        push_neg at hc
        have hge : ∀ k ∈ L, (m + 1) / 2 ≤ k := by
          intro k hk; rw [hLdef, Multiset.mem_filter] at hk; omega
        have h1 := Multiset.card_nsmul_le_sum hge
        rw [smul_eq_mul] at h1
        have hmul : 2 * ((m + 1) / 2) ≤ Multiset.card L * ((m + 1) / 2) :=
          Nat.mul_le_mul_right _ hc
        have h3 : 2 * ((m + 1) / 2) ≤ 2 * g - m := le_trans hmul (le_trans h1 hLsum)
        omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hLcard with hL0 | hL1
      · -- no large part: the difference is `0`
        rw [Multiset.card_eq_zero.mp hL0]
        simp only [Multiset.map_zero, Multiset.prod_zero, sub_self, norm_zero, zero_mul]
        exact hB2gmnn
      · -- exactly one large part `k₀`
        obtain ⟨k₀, hk₀⟩ := Multiset.card_eq_one.mp hL1
        have hLk0sum : L.sum = k₀ := by rw [hk₀]; simp
        have hsum_eq : k₀ + S.sum = 2 * g - m := by
          have h := μ.parts_sum; rw [hsplit, Multiset.sum_add, hLk0sum] at h; exact h
        have hk₀mem : k₀ ∈ μ.parts := by
          have : k₀ ∈ L := by rw [hk₀]; exact Multiset.mem_singleton_self k₀
          rw [hLdef] at this; exact Multiset.mem_of_mem_filter this
        have hk₀1 : 1 ≤ k₀ := μ.parts_pos hk₀mem
        have hk₀m : k₀ < m := by omega
        have hΔL : ‖(L.map (fun k => -F₁.s k)).prod - (L.map (fun k => -F₂.s k)).prod‖
            ≤ 2 * Bbudget g q k₀ := by
          rw [hk₀, Multiset.map_singleton, Multiset.prod_singleton, Multiset.map_singleton,
            Multiset.prod_singleton, show -F₁.s k₀ - -F₂.s k₀ = -(F₁.s k₀ - F₂.s k₀) by ring, norm_neg]
          exact ihbud k₀ hk₀1 hk₀m
        have hB2k0nn : (0 : ℝ) ≤ 2 * Bbudget g q k₀ := by
          unfold Bbudget
          exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by positivity)
            (Real.rpow_nonneg hq0.le _)) (Real.rpow_nonneg hD0.le _))
        have hcast : (k₀ : ℝ) + (S.sum : ℝ) = ((2 * g - m : ℕ) : ℝ) := by
          rw [← Nat.cast_add, hsum_eq]
        have hstep : (2 * (g : ℝ)) ^ Multiset.card S ≤ (Dconst g) ^ S.sum :=
          le_trans (pow_le_pow_right₀ (by linarith [hgr1]) hScard)
            (pow_le_pow_left₀ (by linarith [hgr1]) h2gD _)
        have heq : 2 * Bbudget g q k₀ * ((Dconst g) ^ S.sum * q ^ (-(S.sum : ℝ) / 2))
            = 2 * Bbudget g q (2 * g - m) := by
          unfold Bbudget
          rw [← Real.rpow_natCast (Dconst g) S.sum,
            show ((2 * g - m : ℕ) : ℝ) - g = ((k₀ : ℝ) - g) + (S.sum : ℝ) by rw [← hcast]; ring,
            show -((2 * g - m : ℕ) : ℝ) / 2 - (g : ℝ) / 4
              = (-(k₀ : ℝ) / 2 - (g : ℝ) / 4) + -(S.sum : ℝ) / 2 by rw [← hcast]; ring,
            Real.rpow_add hD0, Real.rpow_add hq0]
          ring
        calc ‖(L.map (fun k => -F₁.s k)).prod - (L.map (fun k => -F₂.s k)).prod‖
              * ((2 * (g : ℝ)) ^ Multiset.card S * q ^ (-(S.sum : ℝ) / 2))
            ≤ (2 * Bbudget g q k₀) * ((2 * (g : ℝ)) ^ Multiset.card S * q ^ (-(S.sum : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_right hΔL
                (mul_nonneg (by positivity) (Real.rpow_nonneg hq0.le _))
          _ ≤ (2 * Bbudget g q k₀) * ((Dconst g) ^ S.sum * q ^ (-(S.sum : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg hq0.le _)) hB2k0nn
          _ = 2 * Bbudget g q (2 * g - m) := heq
    rw [hS11, hS12, ← Finset.sum_sub_distrib]
    calc ‖∑ μ : Nat.Partition (2 * g - m), ((μ.parts.map (fun k => -F₁.s k)).prod / zPart μ.parts
            - (μ.parts.map (fun k => -F₂.s k)).prod / zPart μ.parts)‖
        ≤ ∑ μ : Nat.Partition (2 * g - m), ‖(μ.parts.map (fun k => -F₁.s k)).prod / zPart μ.parts
            - (μ.parts.map (fun k => -F₂.s k)).prod / zPart μ.parts‖ := norm_sum_le _ _
      _ ≤ ∑ _μ : Nat.Partition (2 * g - m), (2 * Bbudget g q (2 * g - m)) :=
          Finset.sum_le_sum (fun μ _ => hperμ μ)
      _ = (Fintype.card (Nat.Partition (2 * g - m)) : ℝ) * (2 * Bbudget g q (2 * g - m)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (partitionCount (2 * g) : ℝ) * (2 * Bbudget g q (2 * g - m)) := by
          refine mul_le_mul_of_nonneg_right ?_ hB2gmnn
          rw [← Nat.card_eq_fintype_card]
          exact_mod_cast partitionCount_mono (show 2 * g - m ≤ 2 * g by omega)
  have hbnd2 : ‖S21 - S22‖ ≤ (partitionCount (2 * g) : ℝ) * V₂ := by
    have hV₂nn : (0 : ℝ) ≤ V₂ := by
      rw [hV₂def]
      exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hq0.le _))
        (Real.rpow_nonneg hD0.le _)
    have h2gD : 2 * (g : ℝ) ≤ Dconst g := by
      nlinarith [h16g3, hgr1, one_le_pow₀ hgr1 (n := 3)]
    have hperμ : ∀ μ ∈ Finset.univ.filter (fun μ : Nat.Partition m => m ∉ μ.parts),
        ‖(μ.parts.map (fun k => -F₁.s k)).prod / zPart μ.parts
          - (μ.parts.map (fun k => -F₂.s k)).prod / zPart μ.parts‖ ≤ V₂ := by
      intro μ hμf
      rw [Finset.mem_filter] at hμf
      have hμm : m ∉ μ.parts := hμf.2
      have hμpos : ∀ k ∈ μ.parts, 0 < k := fun k hk => μ.parts_pos hk
      refine le_trans (partTerm_diff_factored F₁ F₂ hq0 hexact μ.parts hμpos) ?_
      set L := μ.parts.filter (fun k => m ≤ 2 * k) with hLdef
      set S := μ.parts.filter (fun k => ¬ m ≤ 2 * k) with hSdef
      have hsplit : μ.parts = L + S := by rw [hLdef, hSdef]; exact (Multiset.filter_add_not _ _).symm
      have hScard : Multiset.card S ≤ S.sum := by
        have h1 : ∀ k ∈ S, 1 ≤ k := by
          intro k hk; rw [hSdef, Multiset.mem_filter] at hk; exact μ.parts_pos hk.1
        simpa using Multiset.card_nsmul_le_sum h1
      have hLsum : L.sum ≤ m := by
        have h : L.sum ≤ μ.parts.sum := by rw [hsplit, Multiset.sum_add]; exact Nat.le_add_right _ _
        rwa [μ.parts_sum] at h
      -- at most two large parts (three would sum to `> m`)
      have hLcard : Multiset.card L ≤ 2 := by
        by_contra hc
        push_neg at hc
        have hge : ∀ k ∈ L, (m + 1) / 2 ≤ k := by
          intro k hk; rw [hLdef, Multiset.mem_filter] at hk; omega
        have h1 := Multiset.card_nsmul_le_sum hge
        rw [smul_eq_mul] at h1
        have hmul : 3 * ((m + 1) / 2) ≤ Multiset.card L * ((m + 1) / 2) :=
          Nat.mul_le_mul_right _ hc
        have h3 : 3 * ((m + 1) / 2) ≤ m := le_trans hmul (le_trans h1 hLsum)
        omega
      rcases Nat.lt_or_ge (Multiset.card L) 1 with hc0 | hc1
      · -- no large part: difference is `0`
        rw [Multiset.card_eq_zero.mp (by omega : Multiset.card L = 0)]
        simp only [Multiset.map_zero, Multiset.prod_zero, sub_self, norm_zero, zero_mul]
        exact hV₂nn
      · rcases Nat.lt_or_ge (Multiset.card L) 2 with hc1' | hc2
        · -- exactly one large part `k₀`
          obtain ⟨k₀, hk₀⟩ := Multiset.card_eq_one.mp (by omega : Multiset.card L = 1)
          have hLk0sum : L.sum = k₀ := by rw [hk₀]; simp
          have hsum_eq2 : k₀ + S.sum = m := by
            have h := μ.parts_sum; rw [hsplit, Multiset.sum_add, hLk0sum] at h; exact h
          have hk₀mem : k₀ ∈ μ.parts := by
            have : k₀ ∈ L := by rw [hk₀]; exact Multiset.mem_singleton_self k₀
            rw [hLdef] at this; exact Multiset.mem_of_mem_filter this
          have hk₀1 : 1 ≤ k₀ := μ.parts_pos hk₀mem
          have hk₀m : k₀ < m := lt_of_le_of_ne (by omega) (fun h => hμm (h ▸ hk₀mem))
          have hSsum_pos : 1 ≤ S.sum := by omega
          have hΔL : ‖(L.map (fun k => -F₁.s k)).prod - (L.map (fun k => -F₂.s k)).prod‖
              ≤ 2 * Bbudget g q k₀ := by
            rw [hk₀, Multiset.map_singleton, Multiset.prod_singleton, Multiset.map_singleton,
              Multiset.prod_singleton, show -F₁.s k₀ - -F₂.s k₀ = -(F₁.s k₀ - F₂.s k₀) by ring, norm_neg]
            exact ihbud k₀ hk₀1 hk₀m
          have hB2k0nn : (0 : ℝ) ≤ 2 * Bbudget g q k₀ := by
            unfold Bbudget
            exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by positivity)
              (Real.rpow_nonneg hq0.le _)) (Real.rpow_nonneg hD0.le _))
          have hcast2 : (k₀ : ℝ) + (S.sum : ℝ) = (m : ℝ) := by rw [← Nat.cast_add, hsum_eq2]
          have hpow : (2 * (g : ℝ)) ^ S.sum ≤ 2 * (g : ℝ) * (Dconst g) ^ (S.sum - 1) := by
            have h1 : (2 * (g : ℝ)) ^ S.sum = 2 * (g : ℝ) * (2 * (g : ℝ)) ^ (S.sum - 1) := by
              rw [← pow_succ']; congr 1; omega
            rw [h1]
            exact mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by linarith [hgr1]) h2gD _) (by linarith [hgr1])
          have heq2 : 2 * Bbudget g q k₀
              * (2 * (g : ℝ) * (Dconst g) ^ (S.sum - 1) * q ^ (-(S.sum : ℝ) / 2)) = V₂ := by
            rw [hV₂def]
            unfold Bbudget
            rw [← Real.rpow_natCast (Dconst g) (S.sum - 1),
              show ((S.sum - 1 : ℕ) : ℝ) = (S.sum : ℝ) - 1 by
                rw [Nat.cast_sub hSsum_pos]; push_cast; ring,
              show (m : ℝ) - 1 - g = ((k₀ : ℝ) - g) + ((S.sum : ℝ) - 1) by rw [← hcast2]; ring,
              show -(m : ℝ) / 2 - (g : ℝ) / 4
                = (-(k₀ : ℝ) / 2 - (g : ℝ) / 4) + -(S.sum : ℝ) / 2 by rw [← hcast2]; ring,
              Real.rpow_add hD0, Real.rpow_add hq0]
            ring
          calc ‖(L.map (fun k => -F₁.s k)).prod - (L.map (fun k => -F₂.s k)).prod‖
                * ((2 * (g : ℝ)) ^ Multiset.card S * q ^ (-(S.sum : ℝ) / 2))
              ≤ (2 * Bbudget g q k₀) * ((2 * (g : ℝ)) ^ Multiset.card S * q ^ (-(S.sum : ℝ) / 2)) :=
                mul_le_mul_of_nonneg_right hΔL
                  (mul_nonneg (by positivity) (Real.rpow_nonneg hq0.le _))
            _ ≤ (2 * Bbudget g q k₀) * ((2 * (g : ℝ)) ^ S.sum * q ^ (-(S.sum : ℝ) / 2)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [hgr1]) hScard)
                    (Real.rpow_nonneg hq0.le _)) hB2k0nn
            _ ≤ (2 * Bbudget g q k₀) * (2 * (g : ℝ) * (Dconst g) ^ (S.sum - 1) * q ^ (-(S.sum : ℝ) / 2)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hq0.le _)) hB2k0nn
            _ = V₂ := heq2
        · -- exactly two large parts: forced to `{m/2, m/2}`, the two-large term
          have hcard2 : Multiset.card L = 2 := le_antisymm hLcard hc2
          obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard2
          have hamem : a ∈ μ.parts := by
            have : a ∈ L := by rw [hab]; simp
            rw [hLdef] at this; exact Multiset.mem_of_mem_filter this
          have ha_large : m ≤ 2 * a := by
            have : a ∈ L := by rw [hab]; simp
            rw [hLdef, Multiset.mem_filter] at this; exact this.2
          have hb_large : m ≤ 2 * b := by
            have : b ∈ L := by rw [hab]; simp
            rw [hLdef, Multiset.mem_filter] at this; exact this.2
          have hLsum2 : L.sum = a + b := by rw [hab]; simp
          have hab_m : a + b = m := by omega
          have hab_eq : a = b := by omega
          have hSsum0 : S.sum = 0 := by
            have h := μ.parts_sum; rw [hsplit, Multiset.sum_add, hLsum2] at h; omega
          have hScard0 : Multiset.card S = 0 := by omega
          have ha1 : 1 ≤ a := μ.parts_pos hamem
          have ha_m : a < m := lt_of_le_of_ne (by omega) (fun h => hμm (h ▸ hamem))
          have ha2 : 2 * a = m := by omega
          have ha2cast : 2 * (a : ℝ) = (m : ℝ) := by exact_mod_cast ha2
          have ha2ge : 2 ≤ a := by omega
          have har : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2ge
          have hsum_a : ‖F₁.s a + F₂.s a‖ ≤ 4 * (g : ℝ) * q ^ (-(a : ℝ) / 2) := by
            calc ‖F₁.s a + F₂.s a‖ ≤ ‖F₁.s a‖ + ‖F₂.s a‖ := norm_add_le _ _
              _ ≤ 2 * (g : ℝ) * q ^ (-(a : ℝ) / 2) + 2 * (g : ℝ) * q ^ (-(a : ℝ) / 2) :=
                  add_le_add (F₁.norm_s_le hq0.le a) (F₂.norm_s_le hq0.le a)
              _ = 4 * (g : ℝ) * q ^ (-(a : ℝ) / 2) := by ring
          have hB2ann : (0 : ℝ) ≤ 2 * Bbudget g q a := by
            unfold Bbudget
            exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by positivity)
              (Real.rpow_nonneg hq0.le _)) (Real.rpow_nonneg hD0.le _))
          have hqq : q ^ (-(a : ℝ) / 2 - (g : ℝ) / 4) * q ^ (-(a : ℝ) / 2)
              = q ^ (-(m : ℝ) / 2 - (g : ℝ) / 4) := by
            rw [← Real.rpow_add hq0]; congr 1; linarith [ha2cast]
          have hexp1 : (Dconst g) ^ ((m : ℝ) - 1 - g)
              = (Dconst g) ^ ((a : ℝ) - g) * (Dconst g) ^ ((a : ℝ) - 1) := by
            rw [← Real.rpow_add hD0]; congr 1; linarith [ha2cast]
          have hD2 : (2 : ℝ) ≤ (Dconst g) ^ ((a : ℝ) - 1) := by
            calc (2 : ℝ) ≤ Dconst g := by linarith [hD16]
              _ = (Dconst g) ^ (1 : ℝ) := (Real.rpow_one _).symm
              _ ≤ (Dconst g) ^ ((a : ℝ) - 1) :=
                  Real.rpow_le_rpow_of_exponent_le hD1 (by linarith [har])
          have hfin2 : 2 * Bbudget g q a * (4 * (g : ℝ) * q ^ (-(a : ℝ) / 2)) ≤ V₂ := by
            have hX : (0 : ℝ) ≤ 4 * (g : ℝ) ^ 2 * q ^ (-(m : ℝ) / 2 - (g : ℝ) / 4)
                * (Dconst g) ^ ((a : ℝ) - g) := by positivity
            calc 2 * Bbudget g q a * (4 * (g : ℝ) * q ^ (-(a : ℝ) / 2))
                = (4 * (g : ℝ) ^ 2 * q ^ (-(m : ℝ) / 2 - (g : ℝ) / 4)
                    * (Dconst g) ^ ((a : ℝ) - g)) * 2 := by
                  unfold Bbudget; rw [← hqq]; ring
              _ ≤ (4 * (g : ℝ) ^ 2 * q ^ (-(m : ℝ) / 2 - (g : ℝ) / 4)
                    * (Dconst g) ^ ((a : ℝ) - g)) * (Dconst g) ^ ((a : ℝ) - 1) :=
                  mul_le_mul_of_nonneg_left hD2 hX
              _ = V₂ := by rw [hV₂def, hexp1]; ring
          rw [hScard0, hSsum0, pow_zero, Nat.cast_zero, neg_zero, zero_div, Real.rpow_zero, mul_one]
          rw [hab]
          simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
            Multiset.prod_cons, Multiset.prod_singleton, Multiset.map_zero, Multiset.prod_zero,
            mul_one]
          rw [← hab_eq,
            show -F₁.s a * -F₁.s a - -F₂.s a * -F₂.s a
              = (F₁.s a - F₂.s a) * (F₁.s a + F₂.s a) by ring, norm_mul]
          calc ‖F₁.s a - F₂.s a‖ * ‖F₁.s a + F₂.s a‖
              ≤ (2 * Bbudget g q a) * (4 * (g : ℝ) * q ^ (-(a : ℝ) / 2)) :=
                mul_le_mul (ihbud a ha1 ha_m) hsum_a (norm_nonneg _) hB2ann
            _ ≤ V₂ := hfin2
    rw [hS21, hS22, ← Finset.sum_sub_distrib]
    calc ‖∑ μ ∈ Finset.univ.filter (fun μ : Nat.Partition m => m ∉ μ.parts),
            ((μ.parts.map (fun k => -F₁.s k)).prod / zPart μ.parts
              - (μ.parts.map (fun k => -F₂.s k)).prod / zPart μ.parts)‖
        ≤ ∑ μ ∈ Finset.univ.filter (fun μ : Nat.Partition m => m ∉ μ.parts),
            ‖(μ.parts.map (fun k => -F₁.s k)).prod / zPart μ.parts
              - (μ.parts.map (fun k => -F₂.s k)).prod / zPart μ.parts‖ := norm_sum_le _ _
      _ ≤ ∑ _μ ∈ Finset.univ.filter (fun μ : Nat.Partition m => m ∉ μ.parts), V₂ :=
          Finset.sum_le_sum hperμ
      _ = ((Finset.univ.filter (fun μ : Nat.Partition m => m ∉ μ.parts)).card : ℝ) * V₂ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (partitionCount (2 * g) : ℝ) * V₂ := by
          refine mul_le_mul_of_nonneg_right ?_ hV₂nn
          have hcard : (Finset.univ.filter (fun μ : Nat.Partition m => m ∉ μ.parts)).card
              ≤ partitionCount m := by
            rw [show partitionCount m = Fintype.card (Nat.Partition m) from Nat.card_eq_fintype_card]
            exact le_trans (Finset.card_filter_le _ _) (le_of_eq Finset.card_univ)
          calc ((Finset.univ.filter (fun μ : Nat.Partition m => m ∉ μ.parts)).card : ℝ)
              ≤ (partitionCount m : ℝ) := by exact_mod_cast hcard
            _ ≤ (partitionCount (2 * g) : ℝ) := by
                exact_mod_cast partitionCount_mono (show m ≤ 2 * g by omega)
  -- reduce the goal to those two bounds
  have hqcnorm : ‖(q : ℂ) ^ (-((m - g : ℕ) : ℤ))‖ = (q ^ (m - g))⁻¹ := by
    rw [norm_zpow, Complex.norm_real, Real.norm_of_nonneg hq0.le, zpow_neg, zpow_natCast]
  rw [← mul_sub, norm_mul, Complex.norm_natCast]
  have hinner : ‖(-(q : ℂ) ^ (-((m - g : ℕ) : ℤ)) * S11 + S21)
      - (-(q : ℂ) ^ (-((m - g : ℕ) : ℤ)) * S12 + S22)‖
      ≤ (q ^ (m - g))⁻¹ * ‖S11 - S12‖ + ‖S21 - S22‖ := by
    calc ‖(-(q : ℂ) ^ (-((m - g : ℕ) : ℤ)) * S11 + S21)
            - (-(q : ℂ) ^ (-((m - g : ℕ) : ℤ)) * S12 + S22)‖
        = ‖(-(q : ℂ) ^ (-((m - g : ℕ) : ℤ))) * (S11 - S12) + (S21 - S22)‖ := by
          congr 1; ring
      _ ≤ ‖(-(q : ℂ) ^ (-((m - g : ℕ) : ℤ))) * (S11 - S12)‖ + ‖S21 - S22‖ := norm_add_le _ _
      _ = (q ^ (m - g))⁻¹ * ‖S11 - S12‖ + ‖S21 - S22‖ := by
          rw [norm_mul, norm_neg, hqcnorm]
  -- combine and close
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hqinv_nn : (0 : ℝ) ≤ (q ^ (m - g))⁻¹ := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left
    (le_trans hinner (add_le_add (mul_le_mul_of_nonneg_left hbnd1 hqinv_nn) hbnd2)) hmnn) ?_
  -- the closure inequality (rpow algebra; mirrors `base_case`/`large_range_determines`)
  clear hinner hbnd1 hbnd2 hqcnorm
  have hmle : (m : ℝ) ≤ 2 * (g : ℝ) := by exact_mod_cast (by omega : m ≤ 2 * g)
  have hm1r : (1 : ℝ) ≤ (m : ℝ) - g := by
    have h : (g : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (by omega : g + 1 ≤ m)
    linarith
  have hDeq : Dconst g = 16 * (g : ℝ) ^ 3 * (partitionCount (2 * g) : ℝ) := rfl
  have hgg2 : (g : ℝ) ≤ (g : ℝ) ^ 2 := by simpa using pow_le_pow_right₀ hgr1 (show 1 ≤ 2 by norm_num)
  have hgg3 : (g : ℝ) ≤ (g : ℝ) ^ 3 := by simpa using pow_le_pow_right₀ hgr1 (show 1 ≤ 3 by norm_num)
  -- unified bound: `C · (q^E · D^a) ≤ Bbudget g q m` whenever `C ≤ g · D^{(m-g)-a}`
  have hfrac : ∀ (C a : ℝ), 0 ≤ C → C ≤ (g : ℝ) * (Dconst g) ^ ((m : ℝ) - g - a) →
      C * (q ^ (-(m : ℝ) / 2 - (g : ℝ) / 4) * (Dconst g) ^ a) ≤ Bbudget g q m := by
    intro C a _ hCle
    unfold Bbudget
    rw [show ((m : ℝ) - g) = ((m : ℝ) - g - a) + a by ring, Real.rpow_add hD0]
    have hqE0 : (0 : ℝ) < q ^ (-(m : ℝ) / 2 - (g : ℝ) / 4) := Real.rpow_pos_of_pos hq0 _
    have hDa0 : (0 : ℝ) < (Dconst g) ^ a := Real.rpow_pos_of_pos hD0 _
    calc C * (q ^ (-(m : ℝ) / 2 - (g : ℝ) / 4) * (Dconst g) ^ a)
        ≤ ((g : ℝ) * (Dconst g) ^ ((m : ℝ) - g - a))
            * (q ^ (-(m : ℝ) / 2 - (g : ℝ) / 4) * (Dconst g) ^ a) :=
          mul_le_mul_of_nonneg_right hCle (le_of_lt (mul_pos hqE0 hDa0))
      _ = (g : ℝ) * q ^ (-(m : ℝ) / 2 - (g : ℝ) / 4)
            * ((Dconst g) ^ ((m : ℝ) - g - a) * (Dconst g) ^ a) := by ring
  -- contribution 2: `a = m-1-g`, `C = 4 m p g²`, need `C ≤ g · D¹`
  have hT2 : (m : ℝ) * ((partitionCount (2 * g) : ℝ) * V₂) ≤ Bbudget g q m := by
    rw [hV₂def]
    rw [show (m : ℝ) * ((partitionCount (2 * g) : ℝ) * (4 * (g : ℝ) ^ 2
          * q ^ (-(m : ℝ) / 2 - (g : ℝ) / 4) * (Dconst g) ^ ((m : ℝ) - 1 - g)))
        = (4 * (m : ℝ) * (partitionCount (2 * g) : ℝ) * (g : ℝ) ^ 2)
          * (q ^ (-(m : ℝ) / 2 - (g : ℝ) / 4) * (Dconst g) ^ ((m : ℝ) - 1 - g)) by ring]
    refine hfrac _ _ (by positivity) ?_
    rw [show (m : ℝ) - g - ((m : ℝ) - 1 - g) = 1 by ring, Real.rpow_one, hDeq]
    have h4g2 : (m : ℝ) ≤ 4 * (g : ℝ) ^ 2 := by linarith [hmle, hgg2, hgr1]
    nlinarith [mul_le_mul_of_nonneg_left h4g2
      (by positivity : (0 : ℝ) ≤ 4 * (partitionCount (2 * g) : ℝ) * (g : ℝ) ^ 2)]
  -- contribution 1: `a = -(m-g)`, `C = 2 m p g`, need `C ≤ g · D^{2(m-g)}`
  have hqinv : (q ^ (m - g))⁻¹ = q ^ (-((m : ℝ) - g)) := by
    rw [← Real.rpow_natCast q (m - g), ← Real.rpow_neg hq0.le,
      show ((m - g : ℕ) : ℝ) = (m : ℝ) - g from by rw [Nat.cast_sub (by omega)]]
  have hB2 : Bbudget g q (2 * g - m)
      = (g : ℝ) * q ^ (-(2 * (g : ℝ) - m) / 2 - (g : ℝ) / 4) * (Dconst g) ^ (-((m : ℝ) - g)) := by
    unfold Bbudget
    rw [show ((2 * g - m : ℕ) : ℝ) = 2 * (g : ℝ) - m from by
      rw [Nat.cast_sub (by omega)]; push_cast; ring,
      show ((2 * (g : ℝ) - m) - g) = -((m : ℝ) - g) by ring]
  have hT1 : (m : ℝ)
      * ((q ^ (m - g))⁻¹ * ((partitionCount (2 * g) : ℝ) * (2 * Bbudget g q (2 * g - m))))
        ≤ Bbudget g q m := by
    rw [hqinv, hB2]
    rw [show (m : ℝ) * (q ^ (-((m : ℝ) - g))
          * ((partitionCount (2 * g) : ℝ) * (2 * ((g : ℝ)
            * q ^ (-(2 * (g : ℝ) - m) / 2 - (g : ℝ) / 4) * (Dconst g) ^ (-((m : ℝ) - g))))))
        = (2 * (m : ℝ) * (partitionCount (2 * g) : ℝ) * (g : ℝ))
          * ((q ^ (-((m : ℝ) - g)) * q ^ (-(2 * (g : ℝ) - m) / 2 - (g : ℝ) / 4))
            * (Dconst g) ^ (-((m : ℝ) - g))) by ring]
    rw [← Real.rpow_add hq0,
      show -((m : ℝ) - g) + (-(2 * (g : ℝ) - m) / 2 - (g : ℝ) / 4) = -(m : ℝ) / 2 - (g : ℝ) / 4 by ring]
    refine hfrac _ _ (by positivity) ?_
    rw [show (m : ℝ) - g - (-((m : ℝ) - g)) = 2 * ((m : ℝ) - g) by ring]
    have hDle : (Dconst g) ^ (1 : ℝ) ≤ (Dconst g) ^ (2 * ((m : ℝ) - g)) :=
      Real.rpow_le_rpow_of_exponent_le hD1 (by linarith [hm1r])
    have hstep : 2 * (m : ℝ) * (partitionCount (2 * g) : ℝ) * (g : ℝ)
        ≤ (g : ℝ) * (Dconst g) ^ (1 : ℝ) := by
      rw [Real.rpow_one, hDeq]
      have h8g3 : (m : ℝ) ≤ 8 * (g : ℝ) ^ 3 := by linarith [hmle, hgg3, hgr1]
      nlinarith [mul_le_mul_of_nonneg_left h8g3
        (by positivity : (0 : ℝ) ≤ 2 * (partitionCount (2 * g) : ℝ) * (g : ℝ))]
    calc 2 * (m : ℝ) * (partitionCount (2 * g) : ℝ) * (g : ℝ)
        ≤ (g : ℝ) * (Dconst g) ^ (1 : ℝ) := hstep
      _ ≤ (g : ℝ) * (Dconst g) ^ (2 * ((m : ℝ) - g)) :=
          mul_le_mul_of_nonneg_left hDle (by linarith [hgr1])
  -- combine the two contributions
  rw [show (m : ℝ) * ((q ^ (m - g))⁻¹ * ((partitionCount (2 * g) : ℝ) * (2 * Bbudget g q (2 * g - m)))
        + (partitionCount (2 * g) : ℝ) * V₂)
      = (m : ℝ) * ((q ^ (m - g))⁻¹ * ((partitionCount (2 * g) : ℝ) * (2 * Bbudget g q (2 * g - m))))
        + (m : ℝ) * ((partitionCount (2 * g) : ℝ) * V₂) by ring]
  linarith [hT1, hT2]

/-- **Budget on the power-sum difference** (§5).  Fix a recovery index `i ≤ g` and suppose
    the power sums below `i` are already known *exactly* (`hexact`).  Then for every `g < m ≤ 2i`,
    two `FrobeniusData` agreeing on `L₁,…,L_g` have `‖F₁.sₘ - F₂.sₘ‖ ≤ 2·B_m`.

    Proved by strong induction over `1 ≤ k ≤ 2i`: the **small range** (`2k ≤ g`) gives
    `F₁.s_k = F₂.s_k` exactly (`small_range` + `s_eq_of_close`); the **seed range**
    (`g/2 < k ≤ g`) gives `‖·‖ ≤ 8g q^{-k} ≤ 2 B_k` (`seed` + `base_case`); the
    **reconstruction range** (`g < k ≤ 2i`) is `reconstruction_step`, whose exactness
    hypothesis (`2j < k ⟹ j < i`) is supplied by `hexact`. -/
theorem s_diff_budget (hg : 2 ≤ g) (hq : Qbound g < q) (F₁ F₂ : FrobeniusData g q)
    (hLeq : ∀ k, 1 ≤ k → k ≤ g → F₁.L k = F₂.L k) {i : ℕ} (hi : i ≤ g)
    (hexact : ∀ j, 1 ≤ j → j < i → F₁.s j = F₂.s j)
    {m : ℕ} (hm1 : g < m) (hm2 : m ≤ 2 * i) :
    ‖F₁.s m - F₂.s m‖ ≤ 2 * Bbudget g q m := by
  have hgr1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast (by omega : 1 ≤ g)
  -- `D` facts and `256 g² < q`
  have hp : 0 < partitionCount (2 * g) := by
    change 0 < Nat.card (Nat.Partition (2 * g))
    have : Nonempty (Nat.Partition (2 * g)) := ⟨default⟩
    exact Nat.card_pos
  have hpr1 : (1 : ℝ) ≤ (partitionCount (2 * g) : ℝ) := by exact_mod_cast hp
  have hcube : (1 : ℝ) ≤ (g : ℝ) ^ 3 := one_le_pow₀ hgr1
  have h16g3 : 16 * (g : ℝ) ^ 3 ≤ Dconst g := by
    unfold Dconst
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 16 * (g : ℝ) ^ 3) (sub_nonneg.mpr hpr1)]
  have hD16 : (16 : ℝ) ≤ Dconst g := by nlinarith [h16g3, hcube]
  have hD0 : (0 : ℝ) < Dconst g := by linarith
  have hD1 : (1 : ℝ) ≤ Dconst g := by linarith
  have hq256 : 256 * (g : ℝ) ^ 2 < q := by
    have step1 : 256 * (g : ℝ) ^ 2 ≤ (Dconst g) ^ 2 := by
      have hh : 256 * (g : ℝ) ^ 6 ≤ (Dconst g) ^ 2 := by
        calc 256 * (g : ℝ) ^ 6 = (16 * (g : ℝ) ^ 3) ^ 2 := by ring
          _ ≤ (Dconst g) ^ 2 := pow_le_pow_left₀ (by positivity) h16g3 2
      linarith [hh, pow_le_pow_right₀ hgr1 (show (2 : ℕ) ≤ 6 by norm_num)]
    have step2 : (Dconst g) ^ 2 ≤ (Dconst g) ^ (2 * g + 2) := pow_le_pow_right₀ hD1 (by omega)
    have hQ : 256 * (g : ℝ) ^ 2 ≤ Qbound g := by unfold Qbound; linarith [step1, step2]
    linarith [hQ, hq]
  have hg2_1 : (1 : ℝ) ≤ (g : ℝ) ^ 2 := one_le_pow₀ hgr1
  have hq0 : (0 : ℝ) < q := by nlinarith [hq256, hg2_1]
  have hq1lt : (1 : ℝ) < q := by nlinarith [hq256, hg2_1]
  have hq2 : (2 : ℝ) ≤ q := by nlinarith [hq256, hg2_1]
  have hDq2g : (Dconst g) ^ (2 * g) ≤ q :=
    le_of_lt (lt_of_le_of_lt (pow_le_pow_right₀ hD1 (by omega)) hq)
  -- strong induction over the whole range `1 ≤ k ≤ 2i`
  suffices h : ∀ k, k ≤ 2 * i → 1 ≤ k → ‖F₁.s k - F₂.s k‖ ≤ 2 * Bbudget g q k from
    h m hm2 (by omega)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk2 hk1
    have hBnn : (0 : ℝ) ≤ 2 * Bbudget g q k := by
      unfold Bbudget
      exact mul_nonneg (by norm_num) (mul_nonneg
        (mul_nonneg (by positivity) (Real.rpow_nonneg hq0.le _)) (Real.rpow_nonneg hD0.le _))
    by_cases hsm : 2 * k ≤ g
    · -- small range: `F₁.s k = F₂.s k`
      have hx : F₁.truncMobius k = F₂.truncMobius k := by
        unfold FrobeniusData.truncMobius
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [Finset.mem_Icc] at hj
        have hji1 : 1 ≤ j * k := by have := Nat.mul_pos hj.1 hk1; omega
        have hjig : j * k ≤ g := by
          have h1 := Nat.mul_le_mul hj.2 (le_refl k)
          have h2 := Nat.div_mul_le_self g k
          omega
        rw [hLeq (j * k) hji1 hjig]
      have h1 := F₁.small_range hq256 hk1 hsm
      have h2 := F₂.small_range hq256 hk1 hsm
      rw [hx] at h1
      have heq : F₁.s k = F₂.s k := F₁.s_eq_of_close F₂ hq1lt hk1 h1 h2
      rw [heq, sub_self, norm_zero]; exact hBnn
    · by_cases hkg : k ≤ g
      · -- seed range: `‖·‖ ≤ 8g q^{-k} ≤ 2 B_k`
        have hLk : F₁.L k = F₂.L k := hLeq k hk1 hkg
        have hs1 := F₁.seed hq2 hk1
        have hs2 := F₂.seed hq2 hk1
        have hbc := base_case (g := g) (q := q) hDq2g (by omega : g < 2 * k) hkg
        have heq2 : F₁.s k - F₂.s k = -(F₁.L k - F₁.s k) + (F₂.L k - F₂.s k) := by rw [hLk]; ring
        have hδ : ‖F₁.s k - F₂.s k‖
            ≤ 4 * (g : ℝ) * q ^ (-(k : ℝ)) + 4 * (g : ℝ) * q ^ (-(k : ℝ)) := by
          calc ‖F₁.s k - F₂.s k‖
              = ‖-(F₁.L k - F₁.s k) + (F₂.L k - F₂.s k)‖ := by rw [heq2]
            _ ≤ ‖-(F₁.L k - F₁.s k)‖ + ‖F₂.L k - F₂.s k‖ := norm_add_le _ _
            _ = ‖F₁.L k - F₁.s k‖ + ‖F₂.L k - F₂.s k‖ := by rw [norm_neg]
            _ ≤ 4 * (g : ℝ) * q ^ (-(k : ℝ)) + 4 * (g : ℝ) * q ^ (-(k : ℝ)) := add_le_add hs1 hs2
        linarith [hδ, hbc]
      · -- reconstruction range
        exact reconstruction_step hg hq F₁ F₂ hLeq (by omega) (by omega : k ≤ 2 * g)
          (fun j hj1 h2jk => hexact j hj1 (by omega))
          (fun j hj1 hjk => ih j hjk (by omega) hj1)

/-- **Large-range determination** (§5–6): two `FrobeniusData` agreeing on
    `L₁,…,L_g` have equal `sᵢ` for the large range `g/2 < i ≤ g`.

    This is the technical heart of the paper and is the one remaining `sorry`.  It
    is **not** reducible to a clean pairwise estimate: recovering `sᵢ` needs the
    doubled power sum `s₂ᵢ` (index in `(g,2g]`), whose reconstruction `sEst_eq`
    depends on the still-unknown `s_k` for `i ≤ k < 2i`.  The paper resolves this
    coupling by an induction carrying the error budget `Δs_j ≤ B_j = Bbudget g q j`
    against a *common* reference approximation (the recovery algorithm), with the
    per-step bound supplied by the partition-sum estimate of §5 (`induction_step`).
    A pairwise difference bound `‖F₁.sₘ - F₂.sₘ‖ ≤ 2 Bₘ` is a factor of two too weak
    and already fails at `g = 1` (where `Q(g) = D^{2g+2}` is tight — cf. the paper's
    "`g ≥ 2`" caveat; `g = 1` needs the separate nonlinear argument via
    `s₂ = s₁² - 2 q⁻¹`).  Formalizing it faithfully is the full §5–6 development. -/
theorem large_range_determines (hg : 2 ≤ g) (hq : Qbound g < q) (F₁ F₂ : FrobeniusData g q)
    (hLeq : ∀ k, 1 ≤ k → k ≤ g → F₁.L k = F₂.L k) {i : ℕ} (hi : 1 ≤ i) (hig : i ≤ g)
    (hexact : ∀ j, 1 ≤ j → j < i → F₁.s j = F₂.s j)
    (hlarge : ¬ 2 * i ≤ g) : F₁.s i = F₂.s i := by
  have hg1 : 1 ≤ g := by omega
  have hgr1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg1
  have hgr2 : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
  have hir : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have higr : (i : ℝ) ≤ (g : ℝ) := by exact_mod_cast hig
  -- `D ≥ 16`, and `16 g³ ≤ D`
  have hp : 0 < partitionCount (2 * g) := by
    change 0 < Nat.card (Nat.Partition (2 * g))
    have : Nonempty (Nat.Partition (2 * g)) := ⟨default⟩
    exact Nat.card_pos
  have hpr1 : (1 : ℝ) ≤ (partitionCount (2 * g) : ℝ) := by exact_mod_cast hp
  have hcube : (1 : ℝ) ≤ (g : ℝ) ^ 3 := one_le_pow₀ hgr1
  have h16g3 : 16 * (g : ℝ) ^ 3 ≤ Dconst g := by
    unfold Dconst
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 16 * (g : ℝ) ^ 3) (sub_nonneg.mpr hpr1)]
  have hD16 : (16 : ℝ) ≤ Dconst g := by nlinarith [h16g3, hcube]
  have hD0 : (0 : ℝ) < Dconst g := by linarith
  have hD1 : (1 : ℝ) ≤ Dconst g := by linarith
  -- `256 g² < q` and `q ≥ 4`, `q > 1`
  have hq256 : 256 * (g : ℝ) ^ 2 < q := by
    have step1 : 256 * (g : ℝ) ^ 2 ≤ (Dconst g) ^ 2 := by
      have hh : 256 * (g : ℝ) ^ 6 ≤ (Dconst g) ^ 2 := by
        calc 256 * (g : ℝ) ^ 6 = (16 * (g : ℝ) ^ 3) ^ 2 := by ring
          _ ≤ (Dconst g) ^ 2 := pow_le_pow_left₀ (by positivity) h16g3 2
      linarith [hh, pow_le_pow_right₀ hgr1 (show (2 : ℕ) ≤ 6 by norm_num)]
    have step2 : (Dconst g) ^ 2 ≤ (Dconst g) ^ (2 * g + 2) := pow_le_pow_right₀ hD1 (by omega)
    have hQ : 256 * (g : ℝ) ^ 2 ≤ Qbound g := by unfold Qbound; linarith [step1, step2]
    linarith [hQ, hq]
  have hq0 : (0 : ℝ) < q := by nlinarith [hq256]
  have hq4 : (4 : ℝ) ≤ q := by nlinarith [hq256, one_le_pow₀ hgr1 (n := 2)]
  have hq1 : (1 : ℝ) < q := by linarith
  -- inputs
  have ha1 := F₁.norm_L_sub_two hq4 hi
  have ha2 := F₂.norm_L_sub_two hq4 hi
  have hLi : F₁.L i = F₂.L i := hLeq i hi hig
  have hbud := s_diff_budget hg hq F₁ F₂ hLeq hig hexact (by omega : g < 2 * i)
    (le_refl (2 * i))
  -- combine: `‖F₁.sᵢ - F₂.sᵢ‖ ≤ B_{2i} + 8g q^{-3i/2}`
  have hcomb : ‖F₁.s i - F₂.s i‖ ≤ Bbudget g q (2 * i)
      + 4 * (g : ℝ) * q ^ (-(3 * (i : ℝ)) / 2) + 4 * (g : ℝ) * q ^ (-(3 * (i : ℝ)) / 2) := by
    have heq : F₁.s i - F₂.s i = (F₁.L i - F₂.L i) + (-((F₁.s (2 * i) - F₂.s (2 * i)) / 2))
        + (F₁.s i - F₁.L i + F₁.s (2 * i) / 2) + (-(F₂.s i - F₂.L i + F₂.s (2 * i) / 2)) := by ring
    have hna : ‖F₁.L i - F₂.L i‖ = 0 := by rw [hLi, sub_self, norm_zero]
    have hnb : ‖(-((F₁.s (2 * i) - F₂.s (2 * i)) / 2))‖ ≤ Bbudget g q (2 * i) := by
      rw [norm_neg, norm_div, show ‖(2 : ℂ)‖ = 2 from by simp]; linarith [hbud]
    have hnc : ‖F₁.s i - F₁.L i + F₁.s (2 * i) / 2‖ ≤ 4 * (g : ℝ) * q ^ (-(3 * (i : ℝ)) / 2) := by
      rw [show F₁.s i - F₁.L i + F₁.s (2 * i) / 2
          = -(F₁.L i - F₁.s i - F₁.s (2 * i) / 2) from by ring, norm_neg]
      exact ha1
    have hnd : ‖(-(F₂.s i - F₂.L i + F₂.s (2 * i) / 2))‖
        ≤ 4 * (g : ℝ) * q ^ (-(3 * (i : ℝ)) / 2) := by
      rw [norm_neg, show F₂.s i - F₂.L i + F₂.s (2 * i) / 2
          = -(F₂.L i - F₂.s i - F₂.s (2 * i) / 2) from by ring, norm_neg]
      exact ha2
    rw [heq]
    have htri := norm_add_le ((F₁.L i - F₂.L i) + (-((F₁.s (2 * i) - F₂.s (2 * i)) / 2))
      + (F₁.s i - F₁.L i + F₁.s (2 * i) / 2)) (-(F₂.s i - F₂.L i + F₂.s (2 * i) / 2))
    have htri2 := norm_add_le ((F₁.L i - F₂.L i) + (-((F₁.s (2 * i) - F₂.s (2 * i)) / 2)))
      (F₁.s i - F₁.L i + F₁.s (2 * i) / 2)
    have htri3 := norm_add_le (F₁.L i - F₂.L i) (-((F₁.s (2 * i) - F₂.s (2 * i)) / 2))
    linarith [htri, htri2, htri3, hna, hnb, hnc, hnd]
  -- the constant: `B_{2i} + 8g q^{-3i/2} < q^{-i} = 1/q^i`
  have hbpos : ∀ (e : ℝ), (0 : ℝ) < q ^ e := fun e => Real.rpow_pos_of_pos hq0 e
  -- (a) `8g q^{-3i/2} < ½ q^{-i}`
  have h16g : 16 * (g : ℝ) < q ^ ((i : ℝ) / 2) := by
    have hsqrt : 16 * (g : ℝ) < q ^ ((1 : ℝ) / 2) := by
      have h2 : (q ^ ((1 : ℝ) / 2)) ^ 2 = q := by
        rw [← Real.rpow_natCast (q ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul hq0.le]; norm_num
      nlinarith [hq256, h2, hbpos ((1 : ℝ) / 2)]
    exact lt_of_lt_of_le hsqrt (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
  have ha_bound : 8 * (g : ℝ) * q ^ (-(3 * (i : ℝ)) / 2) < 1 / 2 * q ^ (-(i : ℝ)) := by
    have key : 8 * (g : ℝ) < 1 / 2 * q ^ ((i : ℝ) / 2) := by linarith [h16g]
    calc 8 * (g : ℝ) * q ^ (-(3 * (i : ℝ)) / 2)
        < (1 / 2 * q ^ ((i : ℝ) / 2)) * q ^ (-(3 * (i : ℝ)) / 2) :=
          mul_lt_mul_of_pos_right key (hbpos _)
      _ = 1 / 2 * q ^ (-(i : ℝ)) := by
          rw [mul_assoc, ← Real.rpow_add hq0]; congr 2; ring
  -- (b) `B_{2i} < ½ q^{-i}`
  have h2gD : 2 * (g : ℝ) ≤ Dconst g := by
    have hg2_1 : (1 : ℝ) ≤ (g : ℝ) ^ 2 := one_le_pow₀ hgr1
    nlinarith [h16g3, hg2_1, hgr1,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 16 * (g : ℝ)) (by linarith : (0 : ℝ) ≤ (g : ℝ) ^ 2 - 1)]
  have hconst : 2 * (g : ℝ) * (Dconst g) ^ ((2 * (i : ℝ)) - g) < q ^ ((g : ℝ) / 4) := by
    have hexp1 : ((2 * (i : ℝ)) - g) + 1 ≤ (g : ℝ) * ((g : ℝ) + 1) / 2 := by
      nlinarith [higr, hgr2,
        mul_nonneg (by linarith : (0 : ℝ) ≤ (g : ℝ) + 1) (by linarith : (0 : ℝ) ≤ (g : ℝ) - 2)]
    have hDexp_nonneg : (0 : ℝ) ≤ (Dconst g) ^ ((2 * (i : ℝ)) - g) := Real.rpow_nonneg hD0.le _
    have hstep1 : 2 * (g : ℝ) * (Dconst g) ^ ((2 * (i : ℝ)) - g)
        ≤ (Dconst g) * (Dconst g) ^ ((2 * (i : ℝ)) - g) :=
      mul_le_mul_of_nonneg_right h2gD hDexp_nonneg
    have hstep2 : (Dconst g) * (Dconst g) ^ ((2 * (i : ℝ)) - g)
        = (Dconst g) ^ (((2 * (i : ℝ)) - g) + 1) := by rw [Real.rpow_add hD0, Real.rpow_one]; ring
    have hstep3 : (Dconst g) ^ (((2 * (i : ℝ)) - g) + 1)
        ≤ (Dconst g) ^ ((g : ℝ) * ((g : ℝ) + 1) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hD1 hexp1
    have hqgg : (Dconst g) ^ ((g : ℝ) * ((g : ℝ) + 1) / 2) < q ^ ((g : ℝ) / 4) := by
      have hQq : (Dconst g) ^ (((2 * g + 2 : ℕ)) : ℝ) < q := by rw [Real.rpow_natCast]; exact hq
      have h1 : ((Dconst g) ^ (((2 * g + 2 : ℕ)) : ℝ)) ^ ((g : ℝ) / 4) < q ^ ((g : ℝ) / 4) :=
        Real.rpow_lt_rpow (Real.rpow_nonneg hD0.le _) hQq (by linarith)
      rwa [← Real.rpow_mul hD0.le,
        show (((2 * g + 2 : ℕ)) : ℝ) * ((g : ℝ) / 4) = (g : ℝ) * ((g : ℝ) + 1) / 2
          by push_cast; ring] at h1
    calc 2 * (g : ℝ) * (Dconst g) ^ ((2 * (i : ℝ)) - g)
        ≤ (Dconst g) * (Dconst g) ^ ((2 * (i : ℝ)) - g) := hstep1
      _ = (Dconst g) ^ (((2 * (i : ℝ)) - g) + 1) := hstep2
      _ ≤ (Dconst g) ^ ((g : ℝ) * ((g : ℝ) + 1) / 2) := hstep3
      _ < q ^ ((g : ℝ) / 4) := hqgg
  have hb_bound : Bbudget g q (2 * i) < 1 / 2 * q ^ (-(i : ℝ)) := by
    unfold Bbudget
    rw [show ((2 * i : ℕ) : ℝ) = 2 * (i : ℝ) by push_cast; ring,
      show -(2 * (i : ℝ)) / 2 - (g : ℝ) / 4 = -(i : ℝ) + -((g : ℝ) / 4) by ring, Real.rpow_add hq0,
      show (g : ℝ) * (q ^ (-(i : ℝ)) * q ^ (-((g : ℝ) / 4))) * (Dconst g) ^ (2 * (i : ℝ) - g)
          = q ^ (-(i : ℝ)) * ((g : ℝ) * q ^ (-((g : ℝ) / 4)) * (Dconst g) ^ (2 * (i : ℝ) - g))
          by ring,
      show (1 : ℝ) / 2 * q ^ (-(i : ℝ)) = q ^ (-(i : ℝ)) * (1 / 2) by ring]
    apply mul_lt_mul_of_pos_left _ (hbpos _)
    rw [Real.rpow_neg hq0.le,
      show (g : ℝ) * (q ^ ((g : ℝ) / 4))⁻¹ * (Dconst g) ^ (2 * (i : ℝ) - g)
        = ((g : ℝ) * (Dconst g) ^ (2 * (i : ℝ) - g)) * (q ^ ((g : ℝ) / 4))⁻¹ by ring,
      mul_inv_lt_iff₀ (hbpos _)]
    linarith [hconst]
  -- conclude `< 1/q^i` and round
  have hconv : (1 : ℝ) / (q ^ i : ℝ) = q ^ (-(i : ℝ)) := by
    rw [one_div, ← Real.rpow_natCast q i, ← Real.rpow_neg hq0.le]
  have hfinal : ‖F₁.s i - F₂.s i‖ < 1 / (q ^ i : ℝ) := by
    rw [hconv]; linarith [hcomb, ha_bound, hb_bound]
  exact F₁.s_eq_of_close_diff F₂ hq1 hi hfinal

/-- **Recovery** (§6): there is a reconstruction `recon`, a function of the
    point-count data `L₁,…,L_g` alone, that reproduces every power sum `sᵢ`,
    `1 ≤ i ≤ g`.  Assembled from `small_range` (range `i ≤ g/2`, by the rounding
    principle `s_eq_of_close`) and `large_range_determines` (range `g/2 < i ≤ g`).
    The construction of `recon` itself — by `Classical.choice` over the
    determination property — is proved in full. -/
theorem exists_recovery (hg : 1 ≤ g) (hg2 : 2 ≤ g) (hq : Qbound g < q) :
    ∃ recon : (ℕ → ℂ) → ℕ → ℂ,
      -- `recon` reads the point-count data only at the known indices `1 ≤ k ≤ g`:
      (∀ a b : ℕ → ℂ, (∀ k, 1 ≤ k → k ≤ g → a k = b k) → ∀ i, recon a i = recon b i) ∧
      ∀ F : FrobeniusData g q, ∀ i, 1 ≤ i → i ≤ g → F.s i = recon F.L i := by
  classical
  -- **Determination**: data agreeing on `L₁,…,L_g` have equal `s₁,…,s_g`.
  -- This is the substance of §4–6; the small range is by the rounding principle
  -- applied to the common truncated-Möbius estimate, the large range by the
  -- inductive sharpening (left schematic, see `induction_step`).
  have det : ∀ (F₁ F₂ : FrobeniusData g q), (∀ k, 1 ≤ k → k ≤ g → F₁.L k = F₂.L k) →
      ∀ i, 1 ≤ i → i ≤ g → F₁.s i = F₂.s i := by
    intro F₁ F₂ hLeq
    have hgr1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    -- `q > 256 g²`, comfortably implied by `q > Q(g) = D^{2g+2} ≥ D² ≥ (16g³)²`
    have hq256 : 256 * (g : ℝ) ^ 2 < q := by
      have hp : 0 < partitionCount (2 * g) := by
        change 0 < Nat.card (Nat.Partition (2 * g))
        have : Nonempty (Nat.Partition (2 * g)) := ⟨default⟩
        exact Nat.card_pos
      have hpr1 : (1 : ℝ) ≤ (partitionCount (2 * g) : ℝ) := by exact_mod_cast hp
      have h16g3 : (0 : ℝ) ≤ 16 * (g : ℝ) ^ 3 := by positivity
      have hD16g3 : 16 * (g : ℝ) ^ 3 ≤ Dconst g := by
        unfold Dconst; nlinarith [mul_nonneg h16g3 (sub_nonneg.mpr hpr1)]
      have hg3 : (1 : ℝ) ≤ (g : ℝ) ^ 3 := one_le_pow₀ hgr1
      have hD1 : (1 : ℝ) ≤ Dconst g := by nlinarith [hD16g3, hg3]
      have step1 : 256 * (g : ℝ) ^ 2 ≤ (Dconst g) ^ 2 := by
        have hh : 256 * (g : ℝ) ^ 6 ≤ (Dconst g) ^ 2 := by
          calc 256 * (g : ℝ) ^ 6 = (16 * (g : ℝ) ^ 3) ^ 2 := by ring
            _ ≤ (Dconst g) ^ 2 := pow_le_pow_left₀ h16g3 hD16g3 2
        linarith [hh, pow_le_pow_right₀ hgr1 (show (2 : ℕ) ≤ 6 by norm_num)]
      have step2 : (Dconst g) ^ 2 ≤ (Dconst g) ^ (2 * g + 2) := pow_le_pow_right₀ hD1 (by omega)
      have hQ : 256 * (g : ℝ) ^ 2 ≤ Qbound g := by unfold Qbound; linarith [step1, step2]
      linarith [hQ, hq]
    have hq1lt : 1 < q := by nlinarith [hq256, one_le_pow₀ hgr1 (n := 2)]
    -- Strong induction on `i`: the large range needs the lower `sⱼ` already recovered exactly.
    intro i
    induction i using Nat.strong_induction_on with
    | _ i IH =>
      intro hi1 hig
      by_cases hsmall : 2 * i ≤ g
      · -- small range: round the common truncated-Möbius estimate
        have hx : F₁.truncMobius i = F₂.truncMobius i := by
          unfold FrobeniusData.truncMobius
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [Finset.mem_Icc] at hj
          have hji1 : 1 ≤ j * i := by have := Nat.mul_pos hj.1 hi1; omega
          have hjig : j * i ≤ g := by
            have h1 := Nat.mul_le_mul hj.2 (le_refl i)
            have h2 := Nat.div_mul_le_self g i
            omega
          rw [hLeq (j * i) hji1 hjig]
        have h1 := F₁.small_range hq256 hi1 hsmall
        have h2 := F₂.small_range hq256 hi1 hsmall
        rw [hx] at h1
        exact F₁.s_eq_of_close F₂ hq1lt hi1 h1 h2
      · -- large range `g/2 < i ≤ g`: the §5–6 inductive sharpening, with the lower
        -- power sums supplied exactly by the strong induction hypothesis.
        have hexact : ∀ j, 1 ≤ j → j < i → F₁.s j = F₂.s j :=
          fun j hj1 hji => IH j hji hj1 (by omega)
        exact large_range_determines hg2 hq F₁ F₂ hLeq hi1 hig hexact hsmall
  -- Build `recon` from `det` by choosing any data realizing the given counts.
  refine ⟨fun a i => if hi : 1 ≤ i ∧ i ≤ g then
      (if h : ∃ F : FrobeniusData g q, ∀ k, 1 ≤ k → k ≤ g → F.L k = a k
        then (Classical.choose h).s i else 0) else 0, ?_, ?_⟩
  · -- locality: `recon a` reads `a` only on `[1,g]`
    intro a b hab i
    by_cases hi : 1 ≤ i ∧ i ≤ g
    · simp only [dif_pos hi]
      by_cases h : ∃ F : FrobeniusData g q, ∀ k, 1 ≤ k → k ≤ g → F.L k = a k
      · have h' : ∃ F : FrobeniusData g q, ∀ k, 1 ≤ k → k ≤ g → F.L k = b k := by
          obtain ⟨F, hF⟩ := h
          exact ⟨F, fun k hk1 hkg => (hF k hk1 hkg).trans (hab k hk1 hkg)⟩
        rw [dif_pos h, dif_pos h']
        exact det _ _ (fun k hk1 hkg =>
          ((Classical.choose_spec h k hk1 hkg).trans (hab k hk1 hkg)).trans
            (Classical.choose_spec h' k hk1 hkg).symm) i hi.1 hi.2
      · have h' : ¬ ∃ F : FrobeniusData g q, ∀ k, 1 ≤ k → k ≤ g → F.L k = b k := by
          rintro ⟨F, hF⟩
          exact h ⟨F, fun k hk1 hkg => (hF k hk1 hkg).trans (hab k hk1 hkg).symm⟩
        rw [dif_neg h, dif_neg h']
    · simp only [dif_neg hi]
  · -- correctness: `recon` reproduces the power sums
    intro F i hi1 hig
    have hi : 1 ≤ i ∧ i ≤ g := ⟨hi1, hig⟩
    have h : ∃ F' : FrobeniusData g q, ∀ k, 1 ≤ k → k ≤ g → F'.L k = F.L k := ⟨F, fun _ _ _ => rfl⟩
    simp only [dif_pos hi, dif_pos h]
    exact (det (Classical.choose h) F (Classical.choose_spec h) i hi1 hig).symm

end FrobeniusData

/-! ## Theorem 1.1 -/

open FrobeniusData in
/-- **Theorem 1.1.**  If `q > Q(g) = (16 g³ p(2g))^{2g+2}`, then the `g` point
    counts `c₁,…,c_g` (equivalently, by `counts_to_sums`, the data `L₁,…,L_g`)
    determine the `L`-polynomial `f_A`: any two abelian varieties of dimension `g`
    over `F_q` with the same `L₁,…,L_g` have the same elementary symmetric
    functions `e₀,…,e_{2g}` of the reciprocal Frobenius eigenvalues, i.e. the same
    `f_A` (hence the same zeta function and, by Tate, the same isogeny class).

    This is proved in full from the recovery statement `exists_recovery` together
    with Newton's identities and the functional equation. -/
theorem pointCounts_determine_zeta {g : ℕ} (hg : 1 ≤ g) (hg2 : 2 ≤ g) {q : ℝ} (hq : Qbound g < q)
    (F F' : FrobeniusData g q) (hL : ∀ i, 1 ≤ i → i ≤ g → F.L i = F'.L i) :
    ∀ n, n ≤ 2 * g → F.e n = F'.e n := by
  have hq0 : (0 : ℝ) < q := by
    have hD0 : (0 : ℝ) ≤ Dconst g := by unfold Dconst; positivity
    have hQ : (0 : ℝ) ≤ Qbound g := by unfold Qbound; exact pow_nonneg hD0 _
    linarith
  -- Step 1: the `g` point counts recover `s₁,…,s_g` (the same for both).
  obtain ⟨recon, hloc, hrec⟩ := exists_recovery hg hg2 hq
  have hs_low : ∀ i, 1 ≤ i → i ≤ g → F.s i = F'.s i := by
    intro i hi hig
    rw [hrec F i hi hig, hrec F' i hi hig, hloc F.L F'.L hL i]
  -- Step 2: equal power sums `s₁,…,s_g` give equal `e₀,…,e_g` (Newton), and the
  -- functional equation propagates equality to `e_{g+1},…,e_{2g}`.
  have he_low : ∀ m, m ≤ g → F.e m = F'.e m := by
    intro m hmg
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp [FrobeniusData.e]
    · exact e_eq_of_s_eq F F' (le_trans hmg (by omega))
        (fun i hi hin => hs_low i hi (le_trans hin hmg))
  intro n hn
  rcases Nat.lt_or_ge g n with hgn | hng
  · -- `g < n ≤ 2g`: write `n = g + k`, `1 ≤ k ≤ g`, use the functional equation.
    obtain ⟨k, hk⟩ : ∃ k, n = g + k := ⟨n - g, by omega⟩
    have hk1 : 1 ≤ k := by omega
    have hkg : k ≤ g := by omega
    have hFE := functional_eq F hq0 hk1 hkg
    have hFE' := functional_eq F' hq0 hk1 hkg
    rw [hk, hFE, hFE', he_low (g - k) (by omega)]
  · -- `n ≤ g`: Newton's identities.
    exact he_low n hng

end PointCountZeta
