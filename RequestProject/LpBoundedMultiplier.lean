module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.Tactic

/-! Multiplication by an actual essentially bounded coefficient in L². -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Filter

section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (a : α → ℂ) (ha : AEStronglyMeasurable a μ) {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖a x‖ ≤ C)

include ha hbound in
theorem memLp_bounded_mul (v : Lp ℂ 2 μ) : MemLp (fun x => a x * v x) 2 μ := by
  apply (Lp.memLp v).of_le_mul (c := C) (ha.mul (Lp.aestronglyMeasurable v))
  filter_upwards [hbound] with x hx
  change ‖a x * v x‖ ≤ C * ‖v x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

def lpBoundedMulLin : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun v := (memLp_bounded_mul a ha hbound v).toLp (fun x => a x * v x)
  map_add' v w := by
    apply Lp.ext
    filter_upwards [(memLp_bounded_mul a ha hbound (v + w)).coeFn_toLp,
      (memLp_bounded_mul a ha hbound v).coeFn_toLp,
      (memLp_bounded_mul a ha hbound w).coeFn_toLp,
      Lp.coeFn_add v w,
      Lp.coeFn_add ((memLp_bounded_mul a ha hbound v).toLp _)
        ((memLp_bounded_mul a ha hbound w).toLp _)] with x hsum hv hw hvw hout
    change ((memLp_bounded_mul a ha hbound (v + w)).toLp _) x = _
    rw [hsum, hvw, hout]
    simp only [Pi.add_apply]
    rw [hv, hw, mul_add]
  map_smul' c v := by
    apply Lp.ext
    filter_upwards [(memLp_bounded_mul a ha hbound (c • v)).coeFn_toLp,
      (memLp_bounded_mul a ha hbound v).coeFn_toLp,
      Lp.coeFn_smul c v,
      Lp.coeFn_smul c ((memLp_bounded_mul a ha hbound v).toLp _)]
      with x hcv hv hin hout
    change ((memLp_bounded_mul a ha hbound (c • v)).toLp _) x =
      (c • (memLp_bounded_mul a ha hbound v).toLp (fun x => a x * v x)) x
    rw [hcv, hin, hout]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hv]
    ring

theorem lpBoundedMulLin_ae (v : Lp ℂ 2 μ) :
    (lpBoundedMulLin a ha hbound v : α → ℂ) =ᵐ[μ] fun x => a x * v x :=
  (memLp_bounded_mul a ha hbound v).coeFn_toLp

theorem norm_lpBoundedMulLin_le (v : Lp ℂ 2 μ) :
    ‖lpBoundedMulLin a ha hbound v‖ ≤ C * ‖v‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [lpBoundedMulLin_ae a ha hbound v, hbound] with x hx hb
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

def lpBoundedMultiplier : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (lpBoundedMulLin a ha hbound).mkContinuous C (norm_lpBoundedMulLin_le a ha hbound)

theorem lpBoundedMultiplier_ae (v : Lp ℂ 2 μ) :
    (lpBoundedMultiplier a ha hbound v : α → ℂ) =ᵐ[μ] fun x => a x * v x :=
  lpBoundedMulLin_ae a ha hbound v

end

end PolyaNeumann

end
