module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Linarith
public import RequestProject.Defs

/-!
# Smooth disk tests from maps defined near the closed disk

A function smooth on a disk of radius greater than one has a global
compactly supported smooth representative agreeing with it near the closed
unit disk. This avoids requiring a conformal coordinate map to be smooth
on the entire plane when constructing the actual disk H¹ representative.
No extension of a conformal map as a homeomorphism is asserted here.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set Filter Metric
open scoped Topology

/-- Both cutoff radii lie strictly between one and the given radius. -/
def smoothDiskCutoffBump (R : ℝ) (hR : 1 < R) : ContDiffBump (0 : ℂ) :=
  ⟨(R + 1) / 2, (3 * R + 1) / 4, by linarith, by linarith⟩

def smoothDiskCutoff (R : ℝ) (hR : 1 < R) (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (smoothDiskCutoffBump R hR z : ℂ) * φ z

theorem smoothDiskCutoffBump_tsupport_subset (R : ℝ) (hR : 1 < R) :
    tsupport (smoothDiskCutoffBump R hR) ⊆ ball (0 : ℂ) R := by
  rw [ContDiffBump.tsupport_eq]
  exact closedBall_subset_ball (show (3 * R + 1) / 4 < R by linarith)

/-- Smoothness is needed only where the cutoff can be nonzero. -/
theorem contDiff_smoothDiskCutoff {R : ℝ} (hR : 1 < R) {φ : ℂ → ℂ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ (ball (0 : ℂ) R)) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothDiskCutoff R hR φ) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ ball (0 : ℂ) R
  · exact (Complex.ofRealCLM.contDiff.comp
      (smoothDiskCutoffBump R hR).contDiff).contDiffAt.mul
        (hφ.contDiffAt (isOpen_ball.mem_nhds hz))
  · have hz' : z ∉ tsupport (smoothDiskCutoffBump R hR) :=
      fun h => hz (smoothDiskCutoffBump_tsupport_subset R hR h)
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz'] with w hw
    simp only [smoothDiskCutoff, hw, Pi.zero_apply, Complex.ofReal_zero, zero_mul]

theorem smoothDiskCutoff_testFunction {R : ℝ} (hR : 1 < R) {φ : ℂ → ℂ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ (ball (0 : ℂ) R)) :
    TestFunction univ (smoothDiskCutoff R hR φ) := by
  refine ⟨contDiff_smoothDiskCutoff hR hφ, ?_, subset_univ _⟩
  exact ((smoothDiskCutoffBump R hR).hasCompactSupport.comp_left
    (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right

theorem smoothDiskCutoff_eventuallyEq {R : ℝ} (hR : 1 < R) (φ : ℂ → ℂ)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) ((R + 1) / 2)) :
    smoothDiskCutoff R hR φ =ᶠ[𝓝 z] φ := by
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  simp only [smoothDiskCutoff,
    (smoothDiskCutoffBump R hR).one_of_mem_closedBall (ball_subset_closedBall hw),
    Complex.ofReal_one, one_mul]

theorem smoothDiskCutoff_eq_closedDisk {R : ℝ} (hR : 1 < R) (φ : ℂ → ℂ)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    smoothDiskCutoff R hR φ z = φ z := by
  exact (smoothDiskCutoff_eventuallyEq hR φ
    (closedBall_subset_ball (show (1 : ℝ) < (R + 1) / 2 by linarith) hz)).self_of_nhds

theorem fderiv_smoothDiskCutoff_eq {R : ℝ} (hR : 1 < R) (φ : ℂ → ℂ)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    fderiv ℝ (smoothDiskCutoff R hR φ) z = fderiv ℝ φ z :=
  (smoothDiskCutoff_eventuallyEq hR φ
    (closedBall_subset_ball (show (1 : ℝ) < (R + 1) / 2 by linarith) hz)).fderiv_eq

end PolyaNeumann

end
