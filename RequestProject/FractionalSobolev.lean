module

public import RequestProject.FourierLipschitz

/-!
# Fractional Sobolev regularity from difference estimates (Lemma 6.6, fractional part)

The proof of Lemma 6.6 obtains the fractional gain `H^{1+δ}`, `0 < δ < 1/2`, from an `L²`
estimate on differences: a derivative which is Lipschitz away from finitely many jumps has
`‖v(· + h) - v‖²_{L²} ≤ C |h|`, and the difference-quotient seminorm is then finite for
`δ < 1/2`. This file formalizes this step on the circle `ℝ / 2πℤ`, in Fourier form.

* `summable_rpow_mul_of_block_bound`: if the dyadic blocks of a nonnegative sequence satisfy
  `∑_{N ≤ |n| ≤ 2N} aₙ ≤ C N^{-β}`, then `∑ₙ |n|^{2s} aₙ < ∞` for `2s < β`.
* `block_bound_of_diff_bound`: a bound `∑ₙ |e^{inh} - 1|^{2k} aₙ ≤ C h^β` for small `h > 0`
  gives such dyadic block bounds.
* `summable_rpow_mul_fourierCoeff_of_diff_bound`, `summable_rpow_mul_fourierCoeff_of_second_diff`:
  for a continuous `2π`-periodic `φ`, `∫₀^{2π} |φ(θ+h) - φ(θ)|² ≤ C h^β` gives
  `∑ₙ |n|^{2s} |φ̂(n)|² < ∞` for `2s < β`; the same holds with the second difference
  `φ(θ+2h) - 2φ(θ+h) + φ(θ)` in place of the first.
* `second_diff_bound_of_lipschitz_deriv`: if `φ` is Lipschitz on `ℝ`, and on the cut
  interval `[0, 2π]` it is differentiable with Lipschitz derivative (the derivative may jump at
  the cut), then `∫₀^{2π} |φ(θ+2h) - 2φ(θ+h) + φ(θ)|² ≤ C h³`.
* `summable_fourierCoeff_three_halves`: hence `∑ₙ |n|^{2+2δ} |φ̂(n)|² < ∞` for every
  `δ < 1/2`, i.e. `φ ∈ H^{1+δ}(𝕋)`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real Filter MeasureTheory
open scoped InnerProductSpace

/-- **Dyadic summation, quantitative form.** If a nonnegative sequence on `ℤ` has dyadic block
sums `∑_{N ≤ |n| ≤ 2N} aₙ ≤ C N^{-β}` for every `N ≥ 1` and `0 ≤ 2s < β`, then every finite
partial sum of `∑ₙ |n|^{2s} aₙ` is at most `0^{2s} a₀ + |C| 2^{2s} / (1 - 2^{2s-β})`. -/
theorem sum_rpow_mul_le_of_block_bound {a : ℤ → ℝ} (ha : ∀ n, 0 ≤ a n) {C β s : ℝ}
    (hs : 0 ≤ s) (hsβ : 2 * s < β)
    (hblock : ∀ N : ℕ, 1 ≤ N → ∀ u : Finset ℤ, (∀ n ∈ u, (N : ℝ) ≤ |(n : ℝ)| ∧
      |(n : ℝ)| ≤ 2 * N) → ∑ n ∈ u, a n ≤ C * (N : ℝ) ^ (-β)) (u : Finset ℤ) :
    ∑ n ∈ u, |(n : ℝ)| ^ (2 * s) * a n ≤
      (0 : ℝ) ^ (2 * s) * a 0 + |C| * 2 ^ (2 * s) * (1 - (2 : ℝ) ^ (2 * s - β))⁻¹ := by
  classical
  set f : ℤ → ℝ := fun n => |(n : ℝ)| ^ (2 * s) * a n with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => mul_nonneg (by positivity) (ha n)
  set r : ℝ := (2 : ℝ) ^ (2 * s - β) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  set b : ℕ → ℝ := fun j => |C| * (2 : ℝ) ^ (2 * s) * r ^ j with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => by positivity
  have hb : Summable b := (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hpow : ∀ (j : ℕ) (x : ℝ), ((2 : ℝ) ^ j) ^ x = ((2 : ℝ) ^ x) ^ j := by
    intro j x
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  set g : ℤ → ℕ := fun n => Nat.log 2 n.natAbs with hg
  -- the block estimate on a fiber
  have hfiber : ∀ (j : ℕ) (v : Finset ℤ), (∀ n ∈ v, n ≠ 0 ∧ g n = j) →
      ∑ n ∈ v, f n ≤ b j := by
    intro j v hv
    have hrange : ∀ n ∈ v, ((2 : ℝ) ^ j) ≤ |(n : ℝ)| ∧ |(n : ℝ)| ≤ 2 * 2 ^ j := by
      intro n hn
      obtain ⟨hn0, hgn⟩ := hv n hn
      have habs : |(n : ℝ)| = (n.natAbs : ℝ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      have h1 : 2 ^ j ≤ n.natAbs := hgn ▸ Nat.pow_log_le_self 2 (Int.natAbs_ne_zero.2 hn0)
      have h2 : n.natAbs < 2 ^ (j + 1) := hgn ▸ Nat.lt_pow_succ_log_self one_lt_two _
      rw [habs]
      constructor
      · exact_mod_cast h1
      · have : (n.natAbs : ℝ) < 2 ^ (j + 1) := by exact_mod_cast h2
        rw [pow_succ] at this
        linarith
    have hblk := hblock (2 ^ j) (Nat.one_le_two_pow) v (by
      intro n hn; push_cast; exact hrange n hn)
    push_cast at hblk
    have hsa : 0 ≤ ∑ n ∈ v, a n := Finset.sum_nonneg fun n _ => ha n
    calc ∑ n ∈ v, f n ≤ ∑ n ∈ v, (2 * 2 ^ j : ℝ) ^ (2 * s) * a n := by
          refine Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_right ?_ (ha n)
          exact Real.rpow_le_rpow (abs_nonneg _) (hrange n hn).2 (by linarith)
      _ = (2 * 2 ^ j : ℝ) ^ (2 * s) * ∑ n ∈ v, a n := by rw [Finset.mul_sum]
      _ ≤ (2 * 2 ^ j : ℝ) ^ (2 * s) * (|C| * ((2 : ℝ) ^ j) ^ (-β)) := by
          refine mul_le_mul_of_nonneg_left (hblk.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ = b j := by
          rw [Real.mul_rpow (by norm_num) (by positivity), hpow, hpow, hbdef, hr]
          simp only
          rw [show (2 : ℝ) ^ (2 * s - β) = 2 ^ (2 * s) * 2 ^ (-β) by
            rw [sub_eq_add_neg, Real.rpow_add two_pos], mul_pow]
          ring
  have htsum : ∑' j, b j = |C| * 2 ^ (2 * s) * (1 - (2 : ℝ) ^ (2 * s - β))⁻¹ := by
    rw [hbdef, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  rw [← htsum, ← Finset.sum_filter_add_sum_filter_not u (fun n => n = 0)]
  gcongr
  · calc ∑ n ∈ u with n = 0, f n ≤ ∑ n ∈ ({0} : Finset ℤ), f n := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => hf0 n
          rw [Finset.mem_filter] at hn
          simp [hn.2]
      _ = (0 : ℝ) ^ (2 * s) * a 0 := by
          simp only [Finset.sum_singleton, hf, Int.cast_zero, abs_zero]
  · rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := (u.filter fun n => ¬n = 0).image g)
      (fun n hn => Finset.mem_image_of_mem g hn)]
    calc ∑ j ∈ (u.filter fun n => ¬n = 0).image g,
          ∑ n ∈ (u.filter fun n => ¬n = 0) with g n = j, f n
        ≤ ∑ j ∈ (u.filter fun n => ¬n = 0).image g, b j := by
          refine Finset.sum_le_sum fun j _ => hfiber j _ fun n hn => ?_
          simp only [Finset.mem_filter] at hn
          exact ⟨hn.1.2, hn.2⟩
      _ ≤ ∑' j, b j := hb.sum_le_tsum _ fun j _ => hb0 j

/-- **Dyadic summation.** If a nonnegative sequence on `ℤ` has dyadic block sums
`∑_{N ≤ |n| ≤ 2N} aₙ ≤ C N^{-β}` for every `N ≥ 1`, then `∑ₙ |n|^{2s} aₙ` converges whenever
`0 ≤ 2s < β`. -/
theorem summable_rpow_mul_of_block_bound {a : ℤ → ℝ} (ha : ∀ n, 0 ≤ a n) {C β s : ℝ}
    (hs : 0 ≤ s) (hsβ : 2 * s < β)
    (hblock : ∀ N : ℕ, 1 ≤ N → ∀ u : Finset ℤ, (∀ n ∈ u, (N : ℝ) ≤ |(n : ℝ)| ∧
      |(n : ℝ)| ≤ 2 * N) → ∑ n ∈ u, a n ≤ C * (N : ℝ) ^ (-β)) :
    Summable fun n : ℤ => |(n : ℝ)| ^ (2 * s) * a n :=
  summable_of_sum_le (fun n => mul_nonneg (by positivity) (ha n))
    (sum_rpow_mul_le_of_block_bound ha hs hsβ hblock)

/-- **Dyadic block bounds from a difference estimate.** If `aₙ ≥ 0` is summable and
`∑ₙ |e^{inh} - 1|^{2k} aₙ ≤ C h^β` for all `0 < h ≤ π/2`, then
`∑_{N ≤ |n| ≤ 2N} aₙ ≤ C (π/2)^β N^{-β}`. -/
theorem block_bound_of_diff_bound {a : ℤ → ℝ} (ha : ∀ n, 0 ≤ a n) (hsum : Summable a)
    (k : ℕ) {C β : ℝ}
    (hdiff : ∀ h : ℝ, 0 < h → h ≤ π / 2 →
      ∑' n : ℤ, ‖Complex.exp (n * h * Complex.I) - 1‖ ^ (2 * k) * a n ≤ C * h ^ β)
    (N : ℕ) (hN : 1 ≤ N) (u : Finset ℤ)
    (hu : ∀ n ∈ u, (N : ℝ) ≤ |(n : ℝ)| ∧ |(n : ℝ)| ≤ 2 * N) :
    ∑ n ∈ u, a n ≤ (C * (π / 2) ^ β) * (N : ℝ) ^ (-β) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set h : ℝ := π / (2 * N) with hh
  have hhpos : 0 < h := by positivity
  have hhle : h ≤ π / 2 := by
    rw [hh, div_le_div_iff₀ (by positivity) two_pos]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [pi_pos]
  set w : ℤ → ℝ := fun n => ‖Complex.exp (n * h * Complex.I) - 1‖ ^ (2 * k) * a n with hw
  have hnorm2 : ∀ n : ℤ, ‖Complex.exp (n * h * Complex.I) - 1‖ ≤ 2 := by
    intro n
    refine (norm_sub_le _ _).trans ?_
    rw [show (n : ℂ) * h * Complex.I = ((n * h : ℝ) : ℂ) * Complex.I from (by push_cast; ring),
      Complex.norm_exp_ofReal_mul_I]
    norm_num
  have hwsum : Summable w := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (ha n)) (fun n => ?_)
      (hsum.mul_left (2 ^ (2 * k)))
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hnorm2 n) _) (ha n)
  have hpt : ∀ n ∈ u, a n ≤ w n := by
    intro n hn
    obtain ⟨h1, h2⟩ := hu n hn
    have habs : |(n : ℝ) * h| ≤ π := by
      rw [abs_mul, abs_of_pos hhpos, hh]
      calc |(n : ℝ)| * (π / (2 * N)) ≤ 2 * N * (π / (2 * N)) := by gcongr
        _ = π := by field_simp
    have hlow : π / 2 ≤ |(n : ℝ) * h| := by
      rw [abs_mul, abs_of_pos hhpos, hh]
      calc π / 2 = N * (π / (2 * N)) := by field_simp
        _ ≤ |(n : ℝ)| * (π / (2 * N)) := by gcongr
    have hk := sq_le_norm_exp_sub_one_sq habs
    have heq : ((n * h : ℝ) : ℂ) * Complex.I = (n : ℂ) * h * Complex.I := by push_cast; ring
    rw [heq] at hk
    have hone : 1 ≤ ‖Complex.exp (n * h * Complex.I) - 1‖ ^ 2 := by
      have hsq : (π / 2) ^ 2 ≤ ((n : ℝ) * h) ^ 2 := by
        rw [← sq_abs ((n : ℝ) * h)]
        exact pow_le_pow_left₀ (by positivity) hlow 2
      have hpi : 0 < π := pi_pos
      have : 4 / π ^ 2 * (π / 2) ^ 2 = 1 := by field_simp; ring
      nlinarith [div_pos (by norm_num : (0:ℝ) < 4) (pow_pos hpi 2)]
    have : 1 ≤ ‖Complex.exp (n * h * Complex.I) - 1‖ ^ (2 * k) := by
      rw [pow_mul]; exact one_le_pow₀ hone
    simpa [hw] using mul_le_mul_of_nonneg_right this (ha n)
  calc ∑ n ∈ u, a n ≤ ∑ n ∈ u, w n := Finset.sum_le_sum hpt
    _ ≤ ∑' n, w n := hwsum.sum_le_tsum _ fun n _ => mul_nonneg (by positivity) (ha n)
    _ ≤ C * h ^ β := hdiff h hhpos hhle
    _ = (C * (π / 2) ^ β) * (N : ℝ) ^ (-β) := by
      rw [hh, show π / (2 * N) = (π / 2) * (N : ℝ)⁻¹ by field_simp,
        Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hNpos.le,
        Real.rpow_neg hNpos.le]
      ring

/-- Fourier coefficients of the `k`-th forward difference `Δ_h^k φ`. -/
lemma fourierCoeffOn_diff {φ : ℝ → ℂ} (hφ : Continuous φ) (hper : Function.Periodic φ (2 * π))
    (h : ℝ) (n : ℤ) :
    fourierCoeffOn two_pi_pos (fun θ => φ (θ + h) - φ θ) n =
      (Complex.exp (n * h * Complex.I) - 1) * fourierCoeffOn two_pi_pos φ n := by
  have h1 := fourierCoeffOn_sub_of_continuous (f := fun θ => φ (θ + h)) (g := φ)
    (hφ.comp ((continuous_id.add continuous_const : Continuous fun x => x + h))) hφ n
  have h2 := fourierCoeffOn_comp_add hper h n
  rw [h1, h2]
  ring

/-- Parseval for the first difference. -/
lemma tsum_diff_eq_integral {φ : ℝ → ℂ} (hφ : Continuous φ) (hper : Function.Periodic φ (2 * π))
    (h : ℝ) :
    ∑' n : ℤ, ‖Complex.exp (n * h * Complex.I) - 1‖ ^ (2 * 1) *
        ‖fourierCoeffOn two_pi_pos φ n‖ ^ 2 =
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖φ (θ + h) - φ θ‖ ^ 2 := by
  have hc : Continuous fun θ => φ (θ + h) - φ θ := (hφ.comp ((continuous_id.add continuous_const : Continuous fun x => x + h))).sub hφ
  rw [← (hasSum_sq_fourierCoeffOn_of_continuous hc).tsum_eq]
  congr 1
  funext n
  rw [fourierCoeffOn_diff hφ hper, norm_mul, mul_pow, mul_one]

/-- Parseval for the second difference. -/
lemma tsum_second_diff_eq_integral {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hper : Function.Periodic φ (2 * π)) (h : ℝ) :
    ∑' n : ℤ, ‖Complex.exp (n * h * Complex.I) - 1‖ ^ (2 * 2) *
        ‖fourierCoeffOn two_pi_pos φ n‖ ^ 2 =
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖φ (θ + 2 * h) - 2 * φ (θ + h) + φ θ‖ ^ 2 := by
  set ψ : ℝ → ℂ := fun θ => φ (θ + h) - φ θ with hψ
  have hψc : Continuous ψ := (hφ.comp ((continuous_id.add continuous_const : Continuous fun x => x + h))).sub hφ
  have hψp : Function.Periodic ψ (2 * π) := fun θ => by
    simp only [hψ, show θ + 2 * π + h = θ + h + 2 * π by ring, hper (θ + h), hper θ]
  have heq : ∀ θ, φ (θ + 2 * h) - 2 * φ (θ + h) + φ θ = ψ (θ + h) - ψ θ := by
    intro θ
    simp only [hψ, show θ + h + h = θ + 2 * h by ring]
    ring
  simp_rw [heq]
  rw [← tsum_diff_eq_integral hψc hψp h]
  congr 1
  funext n
  rw [fourierCoeffOn_diff hφ hper, norm_mul]
  ring

/-- **Fractional regularity from the first difference.** For a continuous `2π`-periodic `φ`
with `∫₀^{2π} |φ(θ+h) - φ(θ)|² ≤ C h^β` for `0 < h ≤ π/2`, the Fourier coefficients satisfy
`∑ₙ |n|^{2s} |φ̂(n)|² < ∞` for `0 ≤ 2s < β`. -/
theorem summable_rpow_mul_fourierCoeff_of_diff_bound {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hper : Function.Periodic φ (2 * π)) {C β s : ℝ} (hs : 0 ≤ s) (hsβ : 2 * s < β)
    (hdiff : ∀ h : ℝ, 0 < h → h ≤ π / 2 →
      ∫ θ in (0 : ℝ)..(2 * π), ‖φ (θ + h) - φ θ‖ ^ 2 ≤ C * h ^ β) :
    Summable fun n : ℤ => |(n : ℝ)| ^ (2 * s) * ‖fourierCoeffOn two_pi_pos φ n‖ ^ 2 := by
  refine summable_rpow_mul_of_block_bound (fun n => by positivity) hs hsβ fun N hN u hu =>
    block_bound_of_diff_bound (C := (2 * π)⁻¹ * C) (fun n => by positivity)
      (hasSum_sq_fourierCoeffOn_of_continuous hφ).summable 1 (fun h h0 h1 => ?_) N hN u hu
  rw [tsum_diff_eq_integral hφ hper h, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hdiff h h0 h1) (by positivity)

/-- **Fractional regularity from the second difference.** For a continuous `2π`-periodic `φ`
with `∫₀^{2π} |φ(θ+2h) - 2φ(θ+h) + φ(θ)|² ≤ C h^β` for `0 < h ≤ π/2`, the Fourier coefficients
satisfy `∑ₙ |n|^{2s} |φ̂(n)|² < ∞` for `0 ≤ 2s < β`. -/
theorem summable_rpow_mul_fourierCoeff_of_second_diff {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hper : Function.Periodic φ (2 * π)) {C β s : ℝ} (hs : 0 ≤ s) (hsβ : 2 * s < β)
    (hdiff : ∀ h : ℝ, 0 < h → h ≤ π / 2 →
      ∫ θ in (0 : ℝ)..(2 * π), ‖φ (θ + 2 * h) - 2 * φ (θ + h) + φ θ‖ ^ 2 ≤ C * h ^ β) :
    Summable fun n : ℤ => |(n : ℝ)| ^ (2 * s) * ‖fourierCoeffOn two_pi_pos φ n‖ ^ 2 := by
  refine summable_rpow_mul_of_block_bound (fun n => by positivity) hs hsβ fun N hN u hu =>
    block_bound_of_diff_bound (C := (2 * π)⁻¹ * C) (fun n => by positivity)
      (hasSum_sq_fourierCoeffOn_of_continuous hφ).summable 2 (fun h h0 h1 => ?_) N hN u hu
  rw [tsum_second_diff_eq_integral hφ hper h, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hdiff h h0 h1) (by positivity)

/-- **Second-difference estimate for a derivative with one jump.** Let `φ` be `K`-Lipschitz
on `ℝ` (in the application, the periodic extension of a function on `[0, 2π]`), and on
`[0, 2π]` differentiable (within the interval) with an `M`-Lipschitz derivative `φ'`;
the one-sided derivatives at `0` and `2π` need not agree. Then for
`0 < h ≤ π/2`, `∫₀^{2π} |φ(θ+2h) - 2φ(θ+h) + φ(θ)|² ≤ (π² M² + 8 K²) h³`. -/
theorem second_diff_bound_of_lipschitz_deriv {φ φ' : ℝ → ℂ} {K M : ℝ}
    (hK : ∀ x y, ‖φ x - φ y‖ ≤ K * |x - y|)
    (hderiv : ∀ x ∈ Set.Icc 0 (2 * π), HasDerivWithinAt φ (φ' x) (Set.Icc 0 (2 * π)) x)
    (hM : ∀ x ∈ Set.Icc 0 (2 * π), ∀ y ∈ Set.Icc 0 (2 * π), ‖φ' x - φ' y‖ ≤ M * |x - y|)
    {h : ℝ} (hh : 0 < h) (hh' : h ≤ π / 2) :
    ∫ θ in (0 : ℝ)..(2 * π), ‖φ (θ + 2 * h) - 2 * φ (θ + h) + φ θ‖ ^ 2 ≤
      (π ^ 2 * M ^ 2 + 8 * K ^ 2) * h ^ (3 : ℝ) := by
  have hφc : Continuous φ := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun y => norm_nonneg _) (fun y => hK y x) ?_
    have : Tendsto (fun y : ℝ => K * |y - x|) (nhds x) (nhds (K * |x - x|)) :=
      (continuous_const.mul ((continuous_id.sub continuous_const).abs)).tendsto x
    simpa using this
  set F : ℝ → ℝ := fun θ => ‖φ (θ + 2 * h) - 2 * φ (θ + h) + φ θ‖ ^ 2 with hF
  have hFc : Continuous F := by
    refine (((hφc.comp (continuous_id.add continuous_const)).sub
      (continuous_const.mul (hφc.comp (continuous_id.add continuous_const)))).add hφc).norm.pow 2
  have hpi : 0 < π := pi_pos
  set a : ℝ := 2 * π - 2 * h with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have ha2 : a ≤ 2 * π := by rw [ha]; linarith
  -- interior estimate
  have hgood : ∀ θ ∈ Set.Icc 0 a, F θ ≤ (M * h ^ 2) ^ 2 := by
    intro θ hθ
    obtain ⟨hθ0, hθa⟩ := hθ
    set g : ℝ → ℂ := fun u => φ (θ + h + u) - φ (θ + u) with hgdef
    have hmaps1 : Set.MapsTo (fun u : ℝ => θ + h + u) (Set.Icc 0 h) (Set.Icc 0 (2 * π)) := by
      intro u hu; obtain ⟨hu0, hu1⟩ := hu; constructor <;> linarith
    have hmaps2 : Set.MapsTo (fun u : ℝ => θ + u) (Set.Icc 0 h) (Set.Icc 0 (2 * π)) := by
      intro u hu; obtain ⟨hu0, hu1⟩ := hu; constructor <;> linarith
    have hgd : ∀ u ∈ Set.Icc 0 h, HasDerivWithinAt g
        (φ' (θ + h + u) - φ' (θ + u)) (Set.Icc 0 h) u := by
      intro u hu
      have h1 : HasDerivWithinAt (fun u : ℝ => θ + h + u) 1 (Set.Icc 0 h) u :=
        (hasDerivAt_id u).const_add (θ + h) |>.hasDerivWithinAt
      have h2 : HasDerivWithinAt (fun u : ℝ => θ + u) 1 (Set.Icc 0 h) u :=
        (hasDerivAt_id u).const_add θ |>.hasDerivWithinAt
      have e1 := (hderiv _ (hmaps1 hu)).scomp u h1 hmaps1
      have e2 := (hderiv _ (hmaps2 hu)).scomp u h2 hmaps2
      simp only [one_smul] at e1 e2
      exact e1.sub e2
    have hbd : ∀ u ∈ Set.Ico 0 h, ‖φ' (θ + h + u) - φ' (θ + u)‖ ≤ M * h := by
      intro u hu
      have := hM _ (hmaps1 (Set.Ico_subset_Icc_self hu)) _ (hmaps2 (Set.Ico_subset_Icc_self hu))
      rwa [show θ + h + u - (θ + u) = h by ring, abs_of_pos hh] at this
    have key := norm_image_sub_le_of_norm_deriv_le_segment' hgd hbd h ⟨hh.le, le_rfl⟩
    have hval : g h - g 0 = φ (θ + 2 * h) - 2 * φ (θ + h) + φ θ := by
      simp only [hgdef, add_zero, show θ + h + h = θ + 2 * h by ring]
      ring
    rw [hval, sub_zero] at key
    exact pow_le_pow_left₀ (norm_nonneg _) (by nlinarith) 2
  -- estimate near the cut
  have hbad : ∀ θ, F θ ≤ (2 * K * h) ^ 2 := by
    intro θ
    have e1 := hK (θ + 2 * h) (θ + h)
    have e2 := hK (θ + h) θ
    rw [show θ + 2 * h - (θ + h) = h by ring, abs_of_pos hh] at e1
    rw [show θ + h - θ = h by ring, abs_of_pos hh] at e2
    have : ‖φ (θ + 2 * h) - 2 * φ (θ + h) + φ θ‖ ≤ 2 * K * h := by
      calc ‖φ (θ + 2 * h) - 2 * φ (θ + h) + φ θ‖
          = ‖(φ (θ + 2 * h) - φ (θ + h)) - (φ (θ + h) - φ θ)‖ := by congr 1; ring
        _ ≤ ‖φ (θ + 2 * h) - φ (θ + h)‖ + ‖φ (θ + h) - φ θ‖ := norm_sub_le _ _
        _ ≤ 2 * K * h := by linarith
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hI1 : ∫ θ in (0 : ℝ)..a, F θ ≤ a * (M * h ^ 2) ^ 2 := by
    have := intervalIntegral.integral_mono_on (μ := volume) ha0 (hFc.intervalIntegrable _ _)
      intervalIntegrable_const hgood
    simpa [intervalIntegral.integral_const] using this
  have hI2 : ∫ θ in a..(2 * π), F θ ≤ (2 * π - a) * (2 * K * h) ^ 2 := by
    have := intervalIntegral.integral_mono_on (μ := volume) ha2 (hFc.intervalIntegrable _ _)
      intervalIntegrable_const fun θ _ => hbad θ
    simpa [intervalIntegral.integral_const] using this
  rw [← intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable 0 a)
    (hFc.intervalIntegrable a (2 * π))]
  have h3 : h ^ (3 : ℝ) = h ^ 3 := by exact_mod_cast Real.rpow_natCast h 3
  rw [h3]
  have hA : a * (M * h ^ 2) ^ 2 ≤ π ^ 2 * M ^ 2 * h ^ 3 := by
    have e : a * (M * h ^ 2) ^ 2 = a * h * (M ^ 2 * h ^ 3) := by ring
    have e' : π ^ 2 * M ^ 2 * h ^ 3 = π ^ 2 * (M ^ 2 * h ^ 3) := by ring
    rw [e, e']
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : a * h ≤ 2 * π * (π / 2) :=
      mul_le_mul ha2 hh' hh.le (by positivity)
    nlinarith
  have hB : (2 * π - a) * (2 * K * h) ^ 2 = 8 * K ^ 2 * h ^ 3 := by rw [ha]; ring
  nlinarith

/-- **`H^{1+δ}` regularity for a derivative with one jump** (the one-dimensional form of the
fractional gain in Lemma 6.6). Under the hypotheses of `second_diff_bound_of_lipschitz_deriv`,
`∑ₙ |n|^{2+2δ} |φ̂(n)|² < ∞` for every `0 ≤ δ < 1/2`. -/
theorem summable_fourierCoeff_three_halves {φ φ' : ℝ → ℂ} {K M : ℝ}
    (hper : Function.Periodic φ (2 * π)) (hK : ∀ x y, ‖φ x - φ y‖ ≤ K * |x - y|)
    (hderiv : ∀ x ∈ Set.Icc 0 (2 * π), HasDerivWithinAt φ (φ' x) (Set.Icc 0 (2 * π)) x)
    (hM : ∀ x ∈ Set.Icc 0 (2 * π), ∀ y ∈ Set.Icc 0 (2 * π), ‖φ' x - φ' y‖ ≤ M * |x - y|)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) :
    Summable fun n : ℤ => |(n : ℝ)| ^ (2 + 2 * δ) * ‖fourierCoeffOn two_pi_pos φ n‖ ^ 2 := by
  have hφ : Continuous φ := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hK0 : 0 ≤ K := by
      have := hK 1 0
      simp only [sub_zero, abs_one, mul_one] at this
      exact (norm_nonneg _).trans this
    refine squeeze_zero (fun y => norm_nonneg _) (fun y => hK y x) ?_
    have : Tendsto (fun y : ℝ => K * |y - x|) (nhds x) (nhds (K * |x - x|)) :=
      (continuous_const.mul ((continuous_id.sub continuous_const).abs)).tendsto x
    simpa using this
  have h := summable_rpow_mul_fourierCoeff_of_second_diff hφ hper (s := 1 + δ) (β := 3)
    (by linarith) (by linarith) fun h h0 h1 =>
      second_diff_bound_of_lipschitz_deriv hK hderiv hM h0 h1
  simpa only [show 2 * (1 + δ) = 2 + 2 * δ by ring] using h

end PolyaNeumann
