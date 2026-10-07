module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

/-!
# Eigenphases and counting (Definition 5.18 and Section 9)

This file formalizes the scalar and combinatorial parts of Section 9 of the paper.

* `argNeg z` is the negative argument `Arg₋ z ∈ (-2π, 0)` of a unimodular `z ≠ 1`
  (Definition 5.18).
* Lemma 9.2 (scalar part): `|z - 1| ≤ -Arg₋ z`, and on the lower semicircle
  `|Arg₋ z| ≤ (π/2) |z - 1|` (the bound used in Lemma 9.1).
* Lemma 9.2 (summed form): for any summable family of eigenvalues, `-Φ₋ ≥ |z_j - 1|` for each
  member, hence `M(E) ≥ E|Ω|/(4π) + ‖U_E - I‖/(2π)` whenever `‖U_E - I‖` is attained by an
  eigenvalue.
* Lemma 9.3 (last step): a continuous integer-valued function on an interval is constant.
* Lemma 9.6: the induction across the Neumann eigenvalues, stated for an abstract
  integer-valued function `M` that equals `1` at small energies, is locally constant away from
  a discrete set `S` and jumps by at most `m(μ)` at `μ ∈ S`; then
  `M(E) ≤ 1 + ∑_{μ ∈ S, μ < E} m(μ)`.
* Theorem 9.7 (last step): an inequality `f ≤ N` valid off a discrete set passes to every
  energy when `f` is left-continuous and `N` is locally constant from the left.

The spectral inputs (trace-class eigenvalue sums, the Fredholm determinant, the Cayley upper
bound of Proposition 7.11 and Lemma 8.8) are not formalized; they appear here as hypotheses.
-/

@[expose] public section

open Set Real

noncomputable section

namespace PolyaNeumann

/-- The negative argument `Arg₋ z`: for `|z| = 1`, `z ≠ 1`, the unique `t ∈ (-2π, 0)` with
`e^{it} = z`. -/
def argNeg (z : ℂ) : ℝ := if Complex.arg z < 0 then Complex.arg z else Complex.arg z - 2 * π

/-- `Arg₋ z ∈ (-2π, 0)` for `z ≠ 1` on the unit circle. -/
theorem argNeg_mem_Ioo {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) : argNeg z ∈ Ioo (-2 * π) 0 := by
  have hlo := Complex.neg_pi_lt_arg z
  have hhi := Complex.arg_le_pi z
  have h0 : Complex.arg z ≠ 0 := by
    intro h
    apply h1
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz, h] at this
    simpa using this.symm
  unfold argNeg
  split_ifs with h
  · exact ⟨by linarith [Real.pi_pos], h⟩
  · have : 0 < Complex.arg z := lt_of_le_of_ne (not_lt.mp h) (Ne.symm h0)
    exact ⟨by linarith, by linarith⟩

/-- `e^{i Arg₋ z} = z` on the unit circle. -/
theorem exp_argNeg {z : ℂ} (hz : ‖z‖ = 1) : Complex.exp (argNeg z * Complex.I) = z := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  rw [hz, Complex.ofReal_one, one_mul] at h
  unfold argNeg
  split_ifs
  · exact h
  · rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, h]
    push_cast
    rw [Complex.exp_two_pi_mul_I, div_one]

/-- **Lemma 9.2 (scalar inequality).**  `|z - 1| ≤ -Arg₋ z` on the unit circle. -/
theorem norm_sub_one_le_neg_argNeg {z : ℂ} (hz : ‖z‖ = 1) : ‖z - 1‖ ≤ -argNeg z := by
  have hneg : argNeg z ≤ 0 := by
    unfold argNeg
    split_ifs with h
    · exact h.le
    · linarith [Complex.arg_le_pi z, Real.pi_pos]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := argNeg z)
  rw [mul_comm, exp_argNeg hz, Real.norm_eq_abs, abs_of_nonpos hneg] at this
  exact this

/-- **Lemma 9.1 (lower semicircle bound).**  If `|z| = 1`, `z ≠ 1` and `Im z ≤ 0` then
`|Arg₋ z| ≤ (π/2) |z - 1|`. -/
theorem abs_argNeg_le_of_im_nonpos {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) (him : z.im ≤ 0) :
    |argNeg z| ≤ π / 2 * ‖z - 1‖ := by
  -- first, `Arg₋ z ∈ [-π, 0]`
  have hmem : argNeg z ∈ Icc (-π) 0 := by
    have hlo := Complex.neg_pi_lt_arg z
    have hhi := Complex.arg_le_pi z
    have hI := argNeg_mem_Ioo hz h1
    rcases him.lt_or_eq with h | h
    · have ha : Complex.arg z < 0 := Complex.arg_neg_iff.mpr h
      unfold argNeg
      rw [if_pos ha]
      exact ⟨hlo.le, ha.le⟩
    · have hre : z.re < 0 := by
        by_contra hre
        push_neg at hre
        apply h1
        have h0 : Complex.arg z = 0 := Complex.arg_eq_zero_iff.mpr ⟨hre, h⟩
        have := Complex.norm_mul_exp_arg_mul_I z
        rw [hz, h0] at this
        simpa using this.symm
      have hpi : Complex.arg z = π := Complex.arg_eq_pi_iff.mpr ⟨hre, h⟩
      unfold argNeg
      rw [if_neg (by rw [hpi]; exact not_lt.mpr Real.pi_pos.le), hpi]
      exact ⟨by linarith, by linarith [Real.pi_pos]⟩
  set t := argNeg z with ht
  have hexp : ‖z - 1‖ = ‖Complex.exp (Complex.I * t) - 1‖ := by
    rw [mul_comm, ht, exp_argNeg hz]
  rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_of_nonpos hmem.2]
  have hs : 2 / π * (-t / 2) ≤ Real.sin (-t / 2) :=
    Real.mul_le_sin (by linarith [hmem.2]) (by linarith [hmem.1])
  have hsin : Real.sin (t / 2) = -Real.sin (-t / 2) := by rw [neg_div, Real.sin_neg, neg_neg]
  have hnn : (0 : ℝ) ≤ 2 / π * (-t / 2) :=
    mul_nonneg (by positivity) (by linarith [hmem.2])
  rw [hsin, abs_mul, abs_neg, abs_two, abs_of_nonneg (hnn.trans hs)]
  have hpi := Real.pi_pos
  have : -t ≤ π / 2 * (2 * Real.sin (-t / 2)) := by
    have h2 : 2 / π * (-t / 2) * π = -t := by field_simp
    nlinarith
  linarith

/-- **Lemma 9.2 (phase remainder, abstract form).**  For a family `z` of unimodular numbers
`≠ 1` (the nonunit eigenvalues of `U_E`, with multiplicity) whose negative arguments are
summable, `-Φ₋ = -∑ Arg₋ z_i ≥ |z_j - 1|` for every `j`. -/
theorem norm_sub_one_le_neg_tsum_argNeg {ι : Type*} {z : ι → ℂ} (hz : ∀ i, ‖z i‖ = 1)
    (h1 : ∀ i, z i ≠ 1) (hs : Summable fun i => argNeg (z i)) (j : ι) :
    ‖z j - 1‖ ≤ -∑' i, argNeg (z i) := by
  have hnn : ∀ i, 0 ≤ -argNeg (z i) := fun i => by
    linarith [(argNeg_mem_Ioo (hz i) (h1 i)).2]
  rw [← tsum_neg]
  exact (norm_sub_one_le_neg_argNeg (hz j)).trans
    (hs.neg.le_tsum j fun i _ => hnn i)

/-- **Lemma 9.2 (second inequality).**  With `Φ₋ = ∑ Arg₋ z_i` and
`M = (E|Ω|/2 - Φ₋)/(2π)`, if the norm `‖U_E - I‖ = r` is attained as `|z_j - 1|`, then
`M ≥ E|Ω|/(4π) + r/(2π)`.  (If the family is empty, take `r = 0`.) -/
theorem phase_integer_ge {ι : Type*} {z : ι → ℂ} (hz : ∀ i, ‖z i‖ = 1) (h1 : ∀ i, z i ≠ 1)
    (hs : Summable fun i => argNeg (z i)) (E area r : ℝ)
    (hr : r = 0 ∨ ∃ j, ‖z j - 1‖ = r) :
    E * area / (4 * π) + r / (2 * π) ≤ (E * area / 2 - ∑' i, argNeg (z i)) / (2 * π) := by
  have key : r ≤ -∑' i, argNeg (z i) := by
    rcases hr with rfl | ⟨j, rfl⟩
    · rw [← tsum_neg]
      exact tsum_nonneg fun i => by linarith [(argNeg_mem_Ioo (hz i) (h1 i)).2]
    · exact norm_sub_one_le_neg_tsum_argNeg hz h1 hs j
  have hpi := Real.pi_pos
  rw [show E * area / (4 * π) + r / (2 * π) = (E * area / 2 + r) / (2 * π) by
    field_simp; ring]
  gcongr
  linarith

/-- **Lemma 9.3 (last step).**  A continuous integer-valued function on an interval is
constant. -/
theorem eq_of_continuousOn_int {J : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hc : ContinuousOn J I) (hZ : ∀ E ∈ I, ∃ n : ℤ, J E = n) {a b : ℝ} (ha : a ∈ I)
    (hb : b ∈ I) : J a = J b := by
  have hsub : uIcc a b ⊆ I := hI.uIcc_subset ha hb
  have hivt := intermediate_value_uIcc (hc.mono hsub)
  obtain ⟨n, hn⟩ := hZ a ha
  obtain ⟨k, hk⟩ := hZ b hb
  by_contra hne
  have hnk : n ≠ k := fun h => hne (by rw [hn, hk, h])
  -- a half-integer value strictly between `J a` and `J b` is attained, a contradiction
  have hmid : ∃ q : ℤ, ((q : ℝ) + 1 / 2) ∈ uIcc (J a) (J b) := by
    rw [hn, hk]
    rcases lt_or_gt_of_ne hnk with h | h
    · have h' : (n : ℝ) + 1 ≤ k := by exact_mod_cast h
      exact ⟨n, mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)⟩
    · have h' : (k : ℝ) + 1 ≤ n := by exact_mod_cast h
      exact ⟨k, mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩)⟩
  obtain ⟨q, hq⟩ := hmid
  obtain ⟨c, hc', hcv⟩ := hivt hq
  obtain ⟨l, hl⟩ := hZ c (hsub hc')
  rw [hl] at hcv
  have h2 : (2 * l : ℝ) = 2 * q + 1 := by linarith
  have h2' : 2 * l = 2 * q + 1 := by exact_mod_cast h2
  omega

/-- **Lemma 9.6 (comparison with the strict count), abstract form.**
Let `S` be a set of energies (the positive Neumann eigenvalues), with only finitely many points
in `(0, E)` for each `E`, and `m : ℝ → ℕ` (their multiplicities).  Let `M : ℝ → ℤ` satisfy
* `M = 1` at all small positive energies off `S` (Lemma 8.8);
* `M` is constant across every interval `[E₁, E₂] ⊆ (0, ∞)` avoiding `S` (Lemma 9.4);
* at each `μ ∈ S`, the value just above exceeds the value just below by at most `m μ`
  (Lemma 9.5).
Then `M(E) ≤ 1 + ∑_{μ ∈ S, μ < E} m(μ)` for every `E > 0` off `S`. -/
theorem le_one_add_sum_of_jumps {S : Set ℝ}
    (hSfin : ∀ E, (S ∩ Ioo 0 E).Finite) (m : ℝ → ℕ) (M : ℝ → ℤ)
    (hsmall : ∃ δ > 0, ∀ E ∈ Ioo 0 δ, E ∉ S → M E = 1)
    (hconst : ∀ E₁ E₂, 0 < E₁ → E₁ ≤ E₂ → Disjoint (Icc E₁ E₂) S → M E₁ = M E₂)
    (hjump : ∀ μ ∈ S, ∃ ε > 0, ∀ E₁ ∈ Ioo (μ - ε) μ, ∀ E₂ ∈ Ioo μ (μ + ε), E₁ ∉ S → E₂ ∉ S →
      M E₂ ≤ M E₁ + m μ)
    {E : ℝ} (hE : 0 < E) (hES : E ∉ S) :
    M E ≤ 1 + ∑ μ ∈ (hSfin E).toFinset, (m μ : ℤ) := by
  obtain ⟨δ, hδ, hsm⟩ := hsmall
  suffices H : ∀ n : ℕ, ∀ E, 0 < E → E ∉ S → (hSfin E).toFinset.card = n →
      M E ≤ 1 + ∑ μ ∈ (hSfin E).toFinset, (m μ : ℤ) from H _ E hE hES rfl
  intro n
  induction n with
  | zero =>
    intro E hE hES hc
    rw [Finset.card_eq_zero] at hc
    rw [hc, Finset.sum_empty, add_zero]
    have hno : ∀ x ∈ Ioo 0 E, x ∉ S := fun x hx hxS => by
      have : x ∈ (hSfin E).toFinset := (Set.Finite.mem_toFinset _).mpr ⟨hxS, hx⟩
      simp [hc] at this
    set E0 := min (δ / 2) (E / 2) with hE0
    have hE0p : 0 < E0 := lt_min (by linarith) (by linarith)
    have hE0δ : E0 < δ := (min_le_left _ _).trans_lt (by linarith)
    have hE0E : E0 < E := (min_le_right _ _).trans_lt (by linarith)
    have h1 := hsm E0 ⟨hE0p, hE0δ⟩ (hno E0 ⟨hE0p, hE0E⟩)
    rw [← hconst E0 E hE0p hE0E.le (Set.disjoint_left.mpr fun x hx hxS => by
      rcases eq_or_lt_of_le hx.2 with h | h
      · exact hES (h ▸ hxS)
      · exact hno x ⟨hE0p.trans_le hx.1, h⟩ hxS), h1]
  | succ n ih =>
    intro E hE hES hc
    set F := (hSfin E).toFinset with hFdef
    have hmemF : ∀ x, x ∈ F ↔ x ∈ S ∧ x ∈ Ioo 0 E := fun x => Set.Finite.mem_toFinset _
    have hne : F.Nonempty := Finset.card_pos.mp (by rw [hc]; exact Nat.succ_pos n)
    set μ := F.max' hne with hμdef
    have hμF : μ ∈ F := F.max'_mem hne
    obtain ⟨hμS, hμ0, hμE⟩ := (hmemF μ).mp hμF
    have hle : ∀ x ∈ F, x ≤ μ := fun x hx => F.le_max' x hx
    obtain ⟨ε, hε, hj⟩ := hjump μ hμS
    set G := F.erase μ with hGdef
    set a := (insert 0 G).max' (Finset.insert_nonempty _ _) with hadef
    have ha0 : 0 ≤ a := (insert 0 G).le_max' 0 (Finset.mem_insert_self _ _)
    have hGa : ∀ x ∈ G, x ≤ a := fun x hx =>
      (insert 0 G).le_max' x (Finset.mem_insert_of_mem hx)
    have haμ : a < μ := by
      have hm := (insert 0 G).max'_mem (Finset.insert_nonempty _ _)
      rw [← hadef] at hm
      rcases Finset.mem_insert.mp hm with h | h
      · rw [h]; exact hμ0
      · exact lt_of_le_of_ne (hle a (Finset.mem_of_mem_erase h)) (Finset.ne_of_mem_erase h)
    -- the energy `E₁` just below `μ`
    set E1 := max ((a + μ) / 2) (μ - ε / 2) with hE1
    have hE1μ : E1 < μ := max_lt (by linarith) (by linarith)
    have hE1a : a < E1 := (by linarith : a < (a + μ) / 2).trans_le (le_max_left _ _)
    have hE1ε : μ - ε < E1 := (by linarith : μ - ε < μ - ε / 2).trans_le (le_max_right _ _)
    have hE1p : 0 < E1 := ha0.trans_lt hE1a
    have hE1S : E1 ∉ S := fun hS => by
      have hF : E1 ∈ F := (hmemF E1).mpr ⟨hS, hE1p, hE1μ.trans hμE⟩
      have hG : E1 ∈ G := Finset.mem_erase.mpr ⟨hE1μ.ne, hF⟩
      linarith [hGa E1 hG]
    have hFE1 : (hSfin E1).toFinset = G := by
      ext x
      rw [Set.Finite.mem_toFinset, Finset.mem_erase, hmemF]
      constructor
      · rintro ⟨hxS, hx0, hx1⟩
        exact ⟨(hx1.trans hE1μ).ne, hxS, hx0, hx1.trans (hE1μ.trans hμE)⟩
      · rintro ⟨hxμ, hxS, hx0, hxE⟩
        have hxG : x ∈ G := Finset.mem_erase.mpr ⟨hxμ, (hmemF x).mpr ⟨hxS, hx0, hxE⟩⟩
        exact ⟨hxS, hx0, (hGa x hxG).trans_lt hE1a⟩
    have hcard : (hSfin E1).toFinset.card = n := by
      rw [hFE1, hGdef, Finset.card_erase_of_mem hμF, hc]
      rfl
    have hih := ih E1 hE1p hE1S hcard
    rw [hFE1] at hih
    -- the energy `E₂` just above `μ`
    set E2 := min (μ + ε / 2) ((μ + E) / 2) with hE2
    have hE2μ : μ < E2 := lt_min (by linarith) (by linarith)
    have hE2ε : E2 < μ + ε := (min_le_left _ _).trans_lt (by linarith)
    have hE2E : E2 < E := (min_le_right _ _).trans_lt (by linarith)
    have hE2S : E2 ∉ S := fun hS => by
      have hF : E2 ∈ F := (hmemF E2).mpr ⟨hS, hμ0.trans hE2μ, hE2E⟩
      linarith [hle E2 hF]
    have hjmp := hj E1 ⟨hE1ε, hE1μ⟩ E2 ⟨hE2μ, hE2ε⟩ hE1S hE2S
    have hc2 : M E2 = M E := hconst E2 E (hμ0.trans hE2μ) hE2E.le
      (Set.disjoint_left.mpr fun x hx hxS => by
        rcases eq_or_lt_of_le hx.2 with h | h
        · exact hES (h ▸ hxS)
        · have hF : x ∈ F := (hmemF x).mpr ⟨hxS, (hμ0.trans hE2μ).trans_le hx.1, h⟩
          linarith [hle x hF, hx.1])
    have hsum : ∑ x ∈ F, (m x : ℤ) = (∑ x ∈ G, (m x : ℤ)) + m μ :=
      (Finset.sum_erase_add F _ hμF).symm
    rw [hsum, ← hc2]
    linarith

/-- **Theorem 9.7 (passage to resonant energies), abstract form.**  If `f(E) ≤ N(E)` at all
positive energies off a set `S` with finitely many points in each `(0, E)`, `f` is continuous
from the left and `N` is constant immediately to the left of each point, then `f ≤ N` at every
positive energy.  (In the paper `f(E) = E|Ω|/(4π) + ‖U_E - I‖/(2π)` and `N = N_N`, which counts
eigenvalues strictly below `E`.) -/
theorem le_of_le_off_of_leftLimit {S : Set ℝ} (hSfin : ∀ E, (S ∩ Ioo 0 E).Finite)
    {f N : ℝ → ℝ} (hnr : ∀ E, 0 < E → E ∉ S → f E ≤ N E)
    (hf : ∀ μ, 0 < μ → ContinuousWithinAt f (Iio μ) μ)
    (hN : ∀ μ, 0 < μ → ∀ᶠ E in nhdsWithin μ (Iio μ), N E = N μ) {μ : ℝ} (hμ : 0 < μ) :
    f μ ≤ N μ := by
  have h1 : ∀ᶠ E in nhdsWithin μ (Iio μ), E ∈ Ioo 0 μ := Ioo_mem_nhdsLT hμ
  have h2 : ∀ᶠ E in nhdsWithin μ (Iio μ), ∀ t ∈ S ∩ Ioo 0 μ, t < E :=
    (hSfin μ).eventually_all.mpr fun t ht =>
      Filter.mem_of_superset (Ioo_mem_nhdsLT ht.2.2) fun E hE => hE.1
  have hev : ∀ᶠ E in nhdsWithin μ (Iio μ), f E ≤ N μ := by
    filter_upwards [h1, h2, hN μ hμ] with E hE hEt hNE
    have hES : E ∉ S := fun hS => lt_irrefl E (hEt E ⟨hS, hE⟩)
    rw [← hNE]
    exact hnr E hE.1 hES
  exact le_of_tendsto (hf μ hμ) hev

/-- On a principal phase `θ ∈ (-π, π)`, the negative argument of `e^{iθ}` is `θ` if `θ < 0`
and `θ - 2π` otherwise. -/
theorem argNeg_exp_of_mem {θ : ℝ} (h1 : -π < θ) (h2 : θ < π) :
    argNeg (Complex.exp (θ * Complex.I)) = if θ < 0 then θ else θ - 2 * π := by
  have harg : Complex.arg (Complex.exp (θ * Complex.I)) = θ := by
    rw [Complex.exp_mul_I]
    exact Complex.arg_cos_add_sin_mul_I ⟨h1, h2.le⟩
  unfold argNeg
  rw [harg]

/-- **Lemmas 8.7–8.8 (initial value of the phase count), summation step.** Let `θ_j` be a
summable family of principal eigenphases in `(-π, π)`, none equal to `0` (no fixed vector),
with at most one positive member (the index bound of Lemma 8.7) and with
`∑ θ_j = s > 0` (in the paper `s = E|Ω|/2`). Then exactly one phase is positive, the
negative-branch phases `Arg₋ e^{iθ_j}` are summable, and
`(s - Φ₋) / (2π) = 1` where `Φ₋ = ∑ Arg₋ e^{iθ_j}`. -/
theorem initial_phase_count {ι : Type*} {θ : ι → ℝ} (hθ : Summable θ)
    (hlo : ∀ i, -π < θ i) (hhi : ∀ i, θ i < π) (h0 : ∀ i, θ i ≠ 0)
    (hone : ∀ i j, 0 < θ i → 0 < θ j → i = j) {s : ℝ} (hs : ∑' i, θ i = s) (hspos : 0 < s) :
    (∃ j, 0 < θ j) ∧ Summable (fun i => argNeg (Complex.exp (θ i * Complex.I))) ∧
      (s - ∑' i, argNeg (Complex.exp (θ i * Complex.I))) / (2 * π) = 1 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, 0 < θ j := by
    by_contra hneg
    push_neg at hneg
    have : ∑' i, θ i ≤ 0 := tsum_nonpos hneg
    linarith
  have hf : (fun i => argNeg (Complex.exp (θ i * Complex.I))) =
      fun i => θ i - (Pi.single j (2 * π) : ι → ℝ) i := by
    funext i
    rw [argNeg_exp_of_mem (hlo i) (hhi i)]
    by_cases hij : i = j
    · subst hij
      simp [not_lt.2 hj.le]
    · have : θ i < 0 := lt_of_le_of_ne (not_lt.1 fun h => hij (hone i j h hj)) (h0 i)
      simp [this, hij]
  have hsing : HasSum (Pi.single j (2 * π) : ι → ℝ) (2 * π) := hasSum_pi_single j (2 * π)
  rw [hf]
  refine ⟨⟨j, hj⟩, hθ.sub hsing.summable, ?_⟩
  rw [(hθ.hasSum.sub hsing).tsum_eq, hs]
  field_simp
  ring

end PolyaNeumann

end
