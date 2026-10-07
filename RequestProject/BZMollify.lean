module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import RequestProject.BZMono

/-!
# Smoothing a transversal Lipschitz function (towards External theorem BZ)

Convolving a `2`-Lipschitz function `d` with a normalized bump of radius `δ` gives a smooth
`2`-Lipschitz function `ρ` with `|ρ - d| ≤ 2δ`, which is still transversal to a Lipschitz field
`X` (at the slightly smaller rate `κ - 2 L_X δ`) on the points whose `δ`-ball lies in the region
of transversality of `d` (`exists_smooth_transversal`).
-/

@[expose] public section

open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff Convolution

noncomputable section

namespace PolyaNeumann

section bump

variable (η : ContDiffBump (0 : ℂ))

lemma integrable_normed_mul {A : ℂ → ℝ} (hA : Continuous A) :
    Integrable (fun t => η.normed volume t * A t) volume :=
  (η.continuous_normed.mul hA).integrable_of_hasCompactSupport
    (η.hasCompactSupport_normed.mul_right)

lemma integral_normed_mul_le {A B : ℂ → ℝ} (hA : Continuous A) (hB : Continuous B)
    (h : ∀ t : ℂ, ‖t‖ < η.rOut → A t ≤ B t) :
    ∫ t, η.normed volume t * A t ≤ ∫ t, η.normed volume t * B t := by
  refine integral_mono (integrable_normed_mul η hA) (integrable_normed_mul η hB) fun t => ?_
  by_cases ht : ‖t‖ < η.rOut
  · exact mul_le_mul_of_nonneg_left (h t ht) (η.nonneg_normed t)
  · have : η.normed volume t = 0 := by
      rw [← Function.notMem_support, η.support_normed_eq, mem_ball, dist_zero_right]
      exact ht
    simp [this]

lemma integral_normed_mul_add_const {A : ℂ → ℝ} (hA : Continuous A) (c : ℝ) :
    ∫ t, η.normed volume t * (A t + c) = (∫ t, η.normed volume t * A t) + c := by
  have h1 : ∫ t, η.normed volume t * c = c := by
    rw [integral_mul_const, η.integral_normed, one_mul]
  simp_rw [mul_add]
  rw [integral_add (f := fun t => η.normed volume t * A t)
    (g := fun t => η.normed volume t * c) (integrable_normed_mul η hA)
    ((η.continuous_normed.mul continuous_const).integrable_of_hasCompactSupport
      η.hasCompactSupport_normed.mul_right), h1]

end bump

/-- Mollification of a Lipschitz transversal function. -/
theorem exists_smooth_transversal {d : ℂ → ℝ} (hd : LipschitzWith 2 d) {X : ℂ → ℂ}
    {LX : ℝ≥0} (hX : LipschitzWith LX X) {U : Set ℂ} {τ κ : ℝ}
    (hQ : IsTransversalOn d X U τ κ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℂ → ℝ, ContDiff ℝ ∞ ρ ∧ LipschitzWith 2 ρ ∧ (∀ x, |ρ x - d x| ≤ 2 * δ) ∧
      IsTransversalOn ρ X {z | ∀ t : ℂ, ‖t‖ < δ → z - t ∈ U} τ (κ - 2 * LX * δ) := by
  set η : ContDiffBump (0 : ℂ) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have hηr : η.rOut = δ := rfl
  have hdc := hd.continuous
  set ρ : ℂ → ℝ := fun x => ∫ t, η.normed volume t * d (x - t)
  have hρeq : ρ = η.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] d := by
    funext x; simp [ρ, convolution_def]
  have hcont : ∀ x : ℂ, Continuous fun t : ℂ => d (x - t) := fun x => by fun_prop
  refine ⟨ρ, ?_, ?_, ?_, ?_⟩
  · rw [hρeq]
    exact η.hasCompactSupport_normed.contDiff_convolution_left _ η.contDiff_normed
      (hdc.locallyIntegrable)
  · have hle : ∀ x y, ρ x ≤ ρ y + 2 * dist x y := fun x y => by
      have := integral_normed_mul_le η (A := fun t => d (x - t))
        (B := fun t => d (y - t) + 2 * dist x y) (hcont x) ((hcont y).add continuous_const)
        (fun t _ => by
          have h1 := hd.dist_le_mul (x - t) (y - t)
          rw [Real.dist_eq, dist_sub_right] at h1
          have := (le_abs_self _).trans h1
          push_cast at this ⊢
          linarith)
      rwa [integral_normed_mul_add_const η (hcont y)] at this
    refine LipschitzWith.of_le_add_mul 2 fun x y => ?_
    push_cast; exact hle x y
  · intro x
    have hup := integral_normed_mul_le η (hcont x) (continuous_const (y := d x + 2 * δ))
      (fun t ht => by
        have h1 := hd.dist_le_mul (x - t) x
        rw [Real.dist_eq, dist_eq_norm, show x - t - x = -t by ring, norm_neg] at h1
        have := (le_abs_self _).trans h1
        push_cast at this
        rw [hηr] at ht
        nlinarith)
    have hlo := integral_normed_mul_le η (continuous_const (y := d x - 2 * δ)) (hcont x)
      (fun t ht => by
        have h1 := hd.dist_le_mul (x - t) x
        rw [Real.dist_eq, dist_eq_norm, show x - t - x = -t by ring, norm_neg] at h1
        have := (neg_abs_le _).trans' (neg_le_neg h1)
        push_cast at this
        rw [hηr] at ht
        nlinarith)
    have e1 : ∫ t, η.normed volume t * (d x + 2 * δ) = d x + 2 * δ := by
      rw [integral_mul_const, η.integral_normed, one_mul]
    have e2 : ∫ t, η.normed volume t * (d x - 2 * δ) = d x - 2 * δ := by
      rw [integral_mul_const, η.integral_normed, one_mul]
    rw [e1] at hup; rw [e2] at hlo
    rw [abs_le]; constructor <;> simp only [ρ] <;> linarith
  · intro z hz s hs0 hsτ
    have := integral_normed_mul_le η (A := fun t => d (z - t) + (κ - 2 * LX * δ) * s)
      (B := fun t => d (z + s * X z - t)) ((hcont z).add continuous_const) (hcont (z + s * X z))
      (fun t ht => by
        rw [hηr] at ht
        have hU := hz t ht
        have h1 := hQ (z - t) hU s hs0 hsτ
        have h2 := hd.dist_le_mul (z + s * X z - t) (z - t + s * X (z - t))
        rw [Real.dist_eq, dist_eq_norm,
          show z + s * X z - t - (z - t + s * X (z - t)) = s * (X z - X (z - t)) by ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0] at h2
        have h3 : ‖X z - X (z - t)‖ ≤ LX * δ := by
          rw [← dist_eq_norm]
          refine (hX.dist_le_mul _ _).trans ?_
          rw [dist_eq_norm, show z - (z - t) = t by ring]
          exact mul_le_mul_of_nonneg_left ht.le LX.2
        have h4 := (neg_abs_le _).trans' (neg_le_neg h2)
        have h5 : s * ‖X z - X (z - t)‖ ≤ s * (LX * δ) := mul_le_mul_of_nonneg_left h3 hs0
        push_cast at h4 ⊢
        nlinarith)
    rw [integral_normed_mul_add_const η (hcont z)] at this
    simp only [ρ]
    convert this using 2

end PolyaNeumann

end
