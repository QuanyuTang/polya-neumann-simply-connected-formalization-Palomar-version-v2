module

public import RequestProject.LocalDirichletNormalBootstrap
public import RequestProject.LocalDirichletGenuineChart
public import RequestProject.LocalDirichletRectangularSobolev
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Actual derivatives of the Dirichlet boundary restrictions

Continuous representatives supplied by the genuine rectangular L² estimate
are linked by the true horizontal FTC. The positive-height identities pass
to the bottom by dominated convergence on a finite interval. Consequently
the bottom values have the actual successive derivatives; no boundary jet
identity is included as an original-map assumption.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric Filter Complex MeasureTheory
open scoped Topology ContDiff

theorem dirichlet_closed_halfBox_horizontal_mem {a b x y : ℝ}
    (hx : x ∈ Icc (-a) a) (hy : y ∈ Icc (0 : ℝ) b) :
    rectangularComplexCoord (x, y) ∈ smoothDirichletClosedHalfBox a b := by
  simpa only [rectangularComplexCoord, smoothDirichletClosedHalfBox, mem_setOf_eq,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add,
    Complex.add_im, Complex.mul_im, mul_one] using
    (show |x| ≤ a ∧ 0 ≤ y ∧ y ≤ b from ⟨abs_le.mpr hx, hy⟩)

/-- The actual full-approach continuous limit along vertical points.
This uses continuity of the constructed representative on the closed
rectangle, rather than asserting a trace limit. -/
theorem dirichlet_closed_halfBox_vertical_limit {a b : ℝ} (hb : 0 < b)
    {U : ℂ → ℂ} (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b))
    {x : ℝ} (hx : |x| ≤ a) :
    Tendsto (fun y : ℝ => U (rectangularComplexCoord (x, y))) (𝓝[>] (0 : ℝ))
      (𝓝 (U (x : ℂ))) := by
  have hx0 : (x : ℂ) ∈ smoothDirichletClosedHalfBox a b := by
    simpa only [rectangularComplexCoord, Complex.ofReal_zero, zero_mul, add_zero] using
      dirichlet_closed_halfBox_horizontal_mem (abs_le.mp hx)
        (show (0 : ℝ) ∈ Icc (0 : ℝ) b from ⟨le_rfl, hb.le⟩)
  have ht : Tendsto (fun y : ℝ => rectangularComplexCoord (x, y))
      (𝓝[>] (0 : ℝ)) (𝓝 (x : ℂ)) := by
    have hc : Continuous (fun y : ℝ => rectangularComplexCoord (x, y)) :=
      continuous_rectangularComplexCoord.comp
        ((continuous_const : Continuous (fun _ : ℝ => x)).prodMk continuous_id)
    simpa only [rectangularComplexCoord, Complex.ofReal_zero, zero_mul, add_zero] using
      (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hm : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ),
      rectangularComplexCoord (x, y) ∈ smoothDirichletClosedHalfBox a b := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with y hy hyb
    exact dirichlet_closed_halfBox_horizontal_mem (abs_le.mp hx) ⟨hy.le, hyb.le⟩
  exact (hU.continuousWithinAt hx0).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨ht, hm⟩)

/-- Actual horizontal FTC at the bottom, first in the increasing
orientation. The integral limit is justified by a genuine compact bound
for the continuous derivative representative. -/
theorem dirichlet_boundary_horizontal_ftc_of_le {a b : ℝ} (hb : 0 < b)
    {U Q : ℂ → ℂ}
    (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b))
    (hQ : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hd : ∀ x ∈ Ioo (-a) a, ∀ y ∈ Ioo (0 : ℝ) b,
      HasDerivAt (fun s : ℝ => U (rectangularComplexCoord (s, y)))
        (Q (rectangularComplexCoord (x, y))) x)
    {s t : ℝ} (hs : s ∈ Ioo (-a) a) (ht : t ∈ Ioo (-a) a) (hst : s ≤ t) :
    (∫ x in s..t, Q (x : ℂ)) = U (t : ℂ) - U (s : ℂ) := by
  let μ := volume.restrict (Ioc s t)
  have hI : Icc s t ⊆ Ioo (-a) a := fun x hx =>
    ⟨hs.1.trans_le hx.1, hx.2.trans_lt ht.2⟩
  have hrow (V : ℂ → ℂ) (hV : ContinuousOn V (smoothDirichletClosedHalfBox a b))
      (y : ℝ) (hy : y ∈ Icc (0 : ℝ) b) :
      ContinuousOn (fun x : ℝ => V (rectangularComplexCoord (x, y))) (Icc s t) := by
    have hc : Continuous (fun x : ℝ => rectangularComplexCoord (x, y)) :=
      continuous_rectangularComplexCoord.comp
        (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => y)))
    apply hV.comp hc.continuousOn
    intro x hx
    exact dirichlet_closed_halfBox_horizontal_mem
      ⟨(hI hx).1.le, (hI hx).2.le⟩ hy
  obtain ⟨B, hB⟩ := (isCompact_smoothDirichletClosedHalfBox a b).exists_bound_of_continuousOn
    hQ
  have hmeas : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun x : ℝ => Q (rectangularComplexCoord (x, y))) μ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with y hy hyb
    exact ((hrow Q hQ y ⟨hy.le, hyb.le⟩).aestronglyMeasurable measurableSet_Icc).mono_measure
      (Measure.restrict_mono_set volume Ioc_subset_Icc_self)
  have hbound : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂μ,
      ‖Q (rectangularComplexCoord (x, y))‖ ≤ B := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with y hy hyb
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hB _ (dirichlet_closed_halfBox_horizontal_mem
      ⟨(hI ⟨hx.1.le, hx.2⟩).1.le, (hI ⟨hx.1.le, hx.2⟩).2.le⟩ ⟨hy.le, hyb.le⟩)
  have hlim : ∀ᵐ x ∂μ, Tendsto
      (fun y : ℝ => Q (rectangularComplexCoord (x, y))) (𝓝[>] (0 : ℝ)) (𝓝 (Q (x : ℂ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact dirichlet_closed_halfBox_vertical_limit hb hQ
      (abs_le.mpr ⟨(hI ⟨hx.1.le, hx.2⟩).1.le, (hI ⟨hx.1.le, hx.2⟩).2.le⟩)
  have hint : Tendsto (fun y : ℝ => ∫ x in s..t, Q (rectangularComplexCoord (x, y)))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in s..t, Q (x : ℂ))) := by
    simpa only [intervalIntegral.integral_of_le hst] using
      (tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => B)
        hmeas hbound (integrable_const B) hlim)
  have hvalues : Tendsto (fun y : ℝ => U (rectangularComplexCoord (t, y)) -
      U (rectangularComplexCoord (s, y))) (𝓝[>] (0 : ℝ))
      (𝓝 (U (t : ℂ) - U (s : ℂ))) :=
    (dirichlet_closed_halfBox_vertical_limit hb hU (abs_lt.mpr ht).le).sub
      (dirichlet_closed_halfBox_vertical_limit hb hU (abs_lt.mpr hs).le)
  have heq : (fun y : ℝ => ∫ x in s..t, Q (rectangularComplexCoord (x, y)))
      =ᶠ[𝓝[>] (0 : ℝ)] (fun y => U (rectangularComplexCoord (t, y)) -
        U (rectangularComplexCoord (s, y))) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with y hy hyb
    have hyy : y ∈ Icc (0 : ℝ) b := ⟨hy.le, hyb.le⟩
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst (hrow U hU y hyy)
      (fun x hx => hd x (hI ⟨hx.1.le, hx.2.le⟩) y ⟨hy, hyb⟩)
      ((hrow Q hQ y hyy).intervalIntegrable_of_Icc hst)
  exact tendsto_nhds_unique_of_eventuallyEq hint hvalues heq

/-- The bottom FTC retains the true oriented interval integral. -/
theorem dirichlet_boundary_horizontal_ftc {a b : ℝ} (hb : 0 < b)
    {U Q : ℂ → ℂ}
    (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b))
    (hQ : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hd : ∀ x ∈ Ioo (-a) a, ∀ y ∈ Ioo (0 : ℝ) b,
      HasDerivAt (fun s : ℝ => U (rectangularComplexCoord (s, y)))
        (Q (rectangularComplexCoord (x, y))) x)
    {s t : ℝ} (hs : s ∈ Ioo (-a) a) (ht : t ∈ Ioo (-a) a) :
    (∫ x in s..t, Q (x : ℂ)) = U (t : ℂ) - U (s : ℂ) := by
  by_cases hst : s ≤ t
  · exact dirichlet_boundary_horizontal_ftc_of_le hb hU hQ hd hs ht hst
  · rw [intervalIntegral.integral_symm,
      dirichlet_boundary_horizontal_ftc_of_le hb hU hQ hd ht hs (le_of_not_ge hst), neg_sub]

/-- A genuine clamped coordinate makes the continuous bottom derivative
globally continuous, so ordinary FTC-1 can be used without any regularity
assumption outside the actual rectangle. -/
def dirichletBoundaryClamp (a x : ℝ) : ℝ := max (-a) (min a x)

theorem dirichletBoundaryClamp_mem {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    dirichletBoundaryClamp a x ∈ Icc (-a) a :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem dirichletBoundaryClamp_eq {a x : ℝ} (hx : x ∈ Icc (-a) a) :
    dirichletBoundaryClamp a x = x := by
  simp only [dirichletBoundaryClamp, min_eq_right hx.2, max_eq_right hx.1]

theorem continuous_dirichletBoundaryClamp (a : ℝ) : Continuous (dirichletBoundaryClamp a) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem continuous_dirichlet_clamped_boundary {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {Q : ℂ → ℂ} (hQ : ContinuousOn Q (smoothDirichletClosedHalfBox a b)) :
    Continuous (fun x : ℝ => Q ((dirichletBoundaryClamp a x : ℝ) : ℂ)) := by
  apply continuousOn_univ.mp
  apply hQ.comp (Complex.continuous_ofReal.comp (continuous_dirichletBoundaryClamp a)).continuousOn
  intro x _
  simpa only [rectangularComplexCoord, Complex.ofReal_zero, zero_mul, add_zero,
    Function.comp_apply] using
    dirichlet_closed_halfBox_horizontal_mem (dirichletBoundaryClamp_mem ha x)
      (show (0 : ℝ) ∈ Icc (0 : ℝ) b from ⟨le_rfl, hb⟩)

/-- Boundary differentiation is a conclusion of actual interior
derivatives plus the proved bottom FTC. -/
theorem dirichlet_boundary_horizontal_hasDerivAt {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {U Q : ℂ → ℂ}
    (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b))
    (hQ : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hd : ∀ x ∈ Ioo (-a) a, ∀ y ∈ Ioo (0 : ℝ) b,
      HasDerivAt (fun s : ℝ => U (rectangularComplexCoord (s, y)))
        (Q (rectangularComplexCoord (x, y))) x)
    {x : ℝ} (hx : x ∈ Ioo (-a) a) :
    HasDerivAt (fun s : ℝ => U (s : ℂ)) (Q (x : ℂ)) x := by
  let q : ℝ → ℂ := fun s => Q ((dirichletBoundaryClamp a s : ℝ) : ℂ)
  have hqc : Continuous q := continuous_dirichlet_clamped_boundary ha.le hb.le hQ
  let P : ℝ → ℂ := fun s => U (0 : ℂ) + ∫ t in (0 : ℝ)..s, q t
  have hP : HasDerivAt P (q x) x :=
    (intervalIntegral.integral_hasDerivAt_right (hqc.intervalIntegrable 0 x)
      hqc.aestronglyMeasurable.stronglyMeasurableAtFilter hqc.continuousAt).const_add (U 0)
  have heq : (fun s : ℝ => U (s : ℂ)) =ᶠ[𝓝 x] P := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs
    have hinterval : uIcc (0 : ℝ) s ⊆ Icc (-a) a :=
      uIcc_subset_Icc (show (0 : ℝ) ∈ Icc (-a) a from ⟨by linarith, ha.le⟩)
        ⟨hs.1.le, hs.2.le⟩
    have hi : (∫ t in (0 : ℝ)..s, q t) = ∫ t in (0 : ℝ)..s, Q (t : ℂ) :=
      intervalIntegral.integral_congr (fun t ht => by
        dsimp only [q]
        rw [dirichletBoundaryClamp_eq (hinterval ht)])
    have hftc := dirichlet_boundary_horizontal_ftc hb hU hQ hd
      (show (0 : ℝ) ∈ Ioo (-a) a from ⟨by linarith, ha⟩) hs
    dsimp only [P]
    rw [hi, hftc]
    simp only [Complex.ofReal_zero]
    abel
  have hxq : q x = Q (x : ℂ) := by
    dsimp only [q]
    rw [dirichletBoundaryClamp_eq ⟨hx.1.le, hx.2.le⟩]
  rw [hxq] at hP
  exact hP.congr_of_eventuallyEq heq

/-- Continuous representatives of the actual interior function and its
horizontal derivative inherit the actual positive-height derivatives.
Their bottom derivative is then supplied by the proved limiting FTC. -/
theorem dirichlet_boundary_extension_hasDerivAt {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {u U Q : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b))
    (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b))
    (hUu : EqOn U u (smoothDirichletHalfBox a b))
    (hQ : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hQu : EqOn Q (dirD u 1) (smoothDirichletHalfBox a b))
    {x : ℝ} (hx : x ∈ Ioo (-a) a) :
    HasDerivAt (fun s : ℝ => U (s : ℂ)) (Q (x : ℂ)) x := by
  apply dirichlet_boundary_horizontal_hasDerivAt ha hb hU hQ _ hx
  intro t ht y hy
  have hd := rectangular_halfBox_horizontal_hasDerivAt hs ht hy
  have heq : (fun s : ℝ => U (rectangularComplexCoord (s, y)))
      =ᶠ[𝓝 t] (fun s => u (rectangularComplexCoord (s, y))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs'
    exact hUu (rectangularComplexCoord_mem_halfBox
      (show (s, y) ∈ Ioo (-a) a ×ˢ Ioo (0 : ℝ) b from ⟨hs', hy⟩))
  rw [hQu (rectangularComplexCoord_mem_halfBox
    (show (t, y) ∈ Ioo (-a) a ×ˢ Ioo (0 : ℝ) b from ⟨ht, hy⟩))]
  exact hd.congr_of_eventuallyEq heq

theorem continuousOn_dirichlet_boundary_restriction {a b : ℝ} (hb : 0 ≤ b)
    {U : ℂ → ℂ} (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b)) :
    ContinuousOn (fun x : ℝ => U (x : ℂ)) (Ioo (-a) a) := by
  apply hU.comp Complex.continuous_ofReal.continuousOn
  intro x hx
  simpa only [rectangularComplexCoord, Complex.ofReal_zero, zero_mul, add_zero] using
    dirichlet_closed_halfBox_horizontal_mem ⟨hx.1.le, hx.2.le⟩
      (show (0 : ℝ) ∈ Icc (0 : ℝ) b from ⟨le_rfl, hb⟩)

/-- The bottom zero value really forces the bottom horizontal
derivative to vanish. It is derived from the actual limiting FTC,
rather than used as a boundary condition on the derivative. -/
theorem dirichlet_zero_boundary_horizontal_extension {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {u Q : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b))
    (hc : ContinuousOn u (smoothDirichletClosedHalfBox a b))
    (hz : ∀ x ∈ Ioo (-a) a, u (x : ℂ) = 0)
    (hQ : ContinuousOn Q (smoothDirichletClosedHalfBox a b))
    (hQu : EqOn Q (dirD u 1) (smoothDirichletHalfBox a b))
    {x : ℝ} (hx : x ∈ Ioo (-a) a) : Q (x : ℂ) = 0 := by
  have hd := dirichlet_boundary_extension_hasDerivAt ha hb hs hc
    (fun _ _ => rfl) hQ hQu hx
  have heq : (fun s : ℝ => u (s : ℂ)) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with s hs'
    exact hz s hs'
  exact hd.unique ((hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq heq)

/-- The finite chain uses actual `HasDerivAt` identities. In particular
successive continuous fields are not silently declared to be jets. -/
theorem dirichlet_boundary_derivative_chain_contDiffOn {s : Set ℝ} (hs : IsOpen s)
    (n : ℕ) (v : ℕ → ℝ → ℂ)
    (hc : ∀ j ≤ n, ContinuousOn (v j) s)
    (hd : ∀ j < n, ∀ x ∈ s, HasDerivAt (v j) (v (j + 1) x) x) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (v 0) s := by
  induction n generalizing v with
  | zero => exact contDiffOn_zero.mpr (hc 0 (by omega))
  | succ n ih =>
      have hnext : ContDiffOn ℝ (n : WithTop ℕ∞) (v 1) s := by
        exact ih (fun j => v (j + 1))
          (fun j hj => hc (j + 1) (by omega))
          (fun j hj x hx => hd (j + 1) (by omega) x hx)
      have hder : EqOn (deriv (v 0)) (v 1) s :=
        fun x hx => (hd 0 (by omega) x hx).deriv
      have hsucc : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) (v 0) s := by
        apply (contDiffOn_succ_iff_deriv_of_isOpen hs).mpr
        refine ⟨fun x hx => (hd 0 (by omega) x hx).differentiableAt.differentiableWithinAt,
          ?_, hnext.congr hder⟩
        intro hn
        simp at hn
      simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hsucc

/-- Each actual mixed field has a continuous closed-rectangle
representative once the true finite mixed L² cone contains its two
first derivatives and its mixed derivative. -/
theorem dirichlet_mixed_exists_continuous_extension {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b)) (N p q : ℕ)
    (hm : ∀ j k : ℕ, j + k ≤ N → MemLp (dirichletMixedDerivative j k u) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    (horder : p + q + 2 ≤ N) :
    ∃ U : ℂ → ℂ, ContinuousOn U (smoothDirichletClosedHalfBox a b) ∧
      EqOn U (dirichletMixedDerivative p q u) (smoothDirichletHalfBox a b) := by
  have hW := isOpen_smoothDirichletHalfBox a b
  have hy (j k : ℕ) (hjk : j + k + 1 ≤ N) :
      MemLp (dirD (dirichletMixedDerivative j k u) Complex.I) 2
        (volume.restrict (smoothDirichletHalfBox a b)) := by
    apply (hm j (k + 1) (by omega)).ae_eq
    filter_upwards [ae_restrict_mem hW.measurableSet] with z hz
    exact (dirD_dirichletMixedDerivative_I_eqOn hW hs j k hz).symm
  have hx : MemLp (dirD (dirichletMixedDerivative p q u) 1) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
    rw [dirD_dirichletMixedDerivative_one]
    exact hm (p + 1) q (by omega)
  have hxy : MemLp (dirD (dirD (dirichletMixedDerivative p q u) 1) Complex.I) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
    rw [dirD_dirichletMixedDerivative_one]
    exact hy (p + 1) q (by omega)
  obtain ⟨U, hUc, hUu, _⟩ := dirichlet_halfBox_exists_continuous_extension ha hb
    (dirichletMixedDerivative_contDiffOn hW hs p q)
    (hm p q (by omega)) hx (hy p q (by omega)) hxy
  exact ⟨U, hUc, hUu⟩

/-- Actual finite mixed energy yields a genuine finite boundary jet
chain, and hence finite boundary smoothness of the chosen representative.
There are no prescribed derivative values on the bottom. -/
theorem dirichlet_mixed_exists_boundary_contDiffOn {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b)) (N p q n : ℕ)
    (hm : ∀ j k : ℕ, j + k ≤ N → MemLp (dirichletMixedDerivative j k u) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    (horder : p + q + n + 2 ≤ N) :
    ∃ V : ℕ → ℂ → ℂ,
      (∀ j ≤ n, ContinuousOn (V j) (smoothDirichletClosedHalfBox a b) ∧
        EqOn (V j) (dirichletMixedDerivative (p + j) q u) (smoothDirichletHalfBox a b)) ∧
      (∀ j < n, ∀ x ∈ Ioo (-a) a,
        HasDerivAt (fun s : ℝ => V j (s : ℂ)) (V (j + 1) (x : ℂ)) x) ∧
      ContDiffOn ℝ (n : WithTop ℕ∞) (fun x : ℝ => V 0 (x : ℂ)) (Ioo (-a) a) := by
  have hex : ∀ j : ℕ, ∃ U : ℂ → ℂ, j ≤ n →
      ContinuousOn U (smoothDirichletClosedHalfBox a b) ∧
        EqOn U (dirichletMixedDerivative (p + j) q u) (smoothDirichletHalfBox a b) := by
    intro j
    by_cases hj : j ≤ n
    · obtain ⟨U, hUc, hUu⟩ := dirichlet_mixed_exists_continuous_extension
        ha hb hs N (p + j) q hm (by omega)
      exact ⟨U, fun _ => ⟨hUc, hUu⟩⟩
    · exact ⟨0, fun hj' => False.elim (hj hj')⟩
  choose V hV using hex
  have hd : ∀ j < n, ∀ x ∈ Ioo (-a) a,
      HasDerivAt (fun s : ℝ => V j (s : ℂ)) (V (j + 1) (x : ℂ)) x := by
    intro j hj x hx
    have hVu : EqOn (V (j + 1)) (dirD (dirichletMixedDerivative (p + j) q u) 1)
        (smoothDirichletHalfBox a b) := by
      rw [dirD_dirichletMixedDerivative_one]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (hV (j + 1) (by omega)).2
    exact dirichlet_boundary_extension_hasDerivAt ha hb
      (dirichletMixedDerivative_contDiffOn (isOpen_smoothDirichletHalfBox a b) hs (p + j) q)
      (hV j (by omega)).1 (hV j (by omega)).2
      (hV (j + 1) (by omega)).1 hVu hx
  refine ⟨V, hV, hd, ?_⟩
  exact dirichlet_boundary_derivative_chain_contDiffOn isOpen_Ioo n
    (fun j x => V j (x : ℂ))
    (fun j hj => continuousOn_dirichlet_boundary_restriction hb.le (hV j hj).1) hd

/-- The boundary values of two continuous representatives of the same
actual interior function agree wherever their bottom intervals overlap.
This is what permits the genuine energy rectangle to depend on the order. -/
theorem dirichlet_boundary_extensions_eq {a b A B : ℝ} (hb : 0 < b) (hB : 0 < B)
    {u U V : ℂ → ℂ}
    (hU : ContinuousOn U (smoothDirichletClosedHalfBox a b))
    (hUu : EqOn U u (smoothDirichletHalfBox a b))
    (hV : ContinuousOn V (smoothDirichletClosedHalfBox A B))
    (hVu : EqOn V u (smoothDirichletHalfBox A B))
    {x : ℝ} (hx : x ∈ Ioo (-a) a) (hxA : x ∈ Ioo (-A) A) :
    U (x : ℂ) = V (x : ℂ) := by
  have htU := dirichlet_closed_halfBox_vertical_limit hb hU (abs_lt.mpr hx).le
  have htV := dirichlet_closed_halfBox_vertical_limit hB hV (abs_lt.mpr hxA).le
  have heq : (fun y : ℝ => U (rectangularComplexCoord (x, y)))
      =ᶠ[𝓝[>] (0 : ℝ)] (fun y => V (rectangularComplexCoord (x, y))) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds hB).filter_mono nhdsWithin_le_nhds] with y hy hyb hyB
    rw [hUu (rectangularComplexCoord_mem_halfBox
      (show (x, y) ∈ Ioo (-a) a ×ˢ Ioo (0 : ℝ) b from ⟨hx, hy, hyb⟩)),
      hVu (rectangularComplexCoord_mem_halfBox
        (show (x, y) ∈ Ioo (-A) A ×ˢ Ioo (0 : ℝ) B from ⟨hxA, hy, hyB⟩))]
  exact tendsto_nhds_unique_of_eventuallyEq htU htV heq

/-- Finite mixed-energy cones on successively smaller actual rectangles
give smoothness at the center of one fixed continuous representative.
The proof explicitly compares every new representative with the first;
it never asserts that all derivative orders share one energy rectangle. -/
theorem dirichlet_mixed_boundary_contDiffAt_of_finite_energy {A b a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) {u U : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (p q : ℕ)
    (hhigh : ∀ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ∀ j k : ℕ, j + k ≤ N → MemLp (dirichletMixedDerivative j k u) 2
        (volume.restrict (smoothDirichletHalfBox ρ ρ)))
    (hU : ContinuousOn U (smoothDirichletClosedHalfBox a β))
    (hUu : EqOn U (dirichletMixedDerivative p q u) (smoothDirichletHalfBox a β)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => U (x : ℂ)) 0 := by
  apply contDiffAt_infty.mpr
  intro n
  obtain ⟨ρ, hρ, hρA, hρb, hm⟩ := hhigh (p + q + n + 2)
  have hWU : smoothDirichletHalfBox ρ ρ ⊆ smoothDirichletHalfBox A b := by
    intro z hz
    exact ⟨hz.1.trans (by linarith), hz.2.1, hz.2.2.trans hρb⟩
  obtain ⟨V, hV, _, hVc⟩ := dirichlet_mixed_exists_boundary_contDiffOn
    hρ hρ (hs.mono hWU) (p + q + n + 2) p q n hm (le_refl _)
  have hV₀ : EqOn (V 0) (dirichletMixedDerivative p q u)
      (smoothDirichletHalfBox ρ ρ) := by
    simpa only [Nat.add_zero] using (hV 0 (by omega)).2
  have heq : (fun x : ℝ => U (x : ℂ)) =ᶠ[𝓝 (0 : ℝ)]
      (fun x => V 0 (x : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show (0 : ℝ) ∈ Ioo (-a) a from ⟨by linarith, ha⟩),
      isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-ρ) ρ from ⟨by linarith, hρ⟩)]
      with x hx hxρ
    exact dirichlet_boundary_extensions_eq hβ hρ hU hUu
      (hV 0 (by omega)).1 hV₀ hx hxρ
  exact (hVc.contDiffAt (isOpen_Ioo.mem_nhds
    (show (0 : ℝ) ∈ Ioo (-ρ) ρ from ⟨by linarith, hρ⟩))).congr_of_eventuallyEq heq

/-- The selected continuous representative itself is constructed from
the finite energy cone, before any boundary smoothness is deduced. -/
theorem exists_dirichlet_mixed_boundary_contDiffAt {A b : ℝ}
    {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hhigh : ∀ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ∀ j k : ℕ, j + k ≤ N → MemLp (dirichletMixedDerivative j k u) 2
        (volume.restrict (smoothDirichletHalfBox ρ ρ))) (p q : ℕ) :
    ∃ (ρ : ℝ) (U : ℂ → ℂ), 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ContinuousOn U (smoothDirichletClosedHalfBox ρ ρ) ∧
      EqOn U (dirichletMixedDerivative p q u) (smoothDirichletHalfBox ρ ρ) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => U (x : ℂ)) 0 := by
  obtain ⟨ρ, hρ, hρA, hρb, hm⟩ := hhigh (p + q + 2)
  have hWU : smoothDirichletHalfBox ρ ρ ⊆ smoothDirichletHalfBox A b := by
    intro z hz
    exact ⟨hz.1.trans (by linarith), hz.2.1, hz.2.2.trans hρb⟩
  obtain ⟨U, hUc, hUu⟩ := dirichlet_mixed_exists_continuous_extension
    hρ hρ (hs.mono hWU) (p + q + 2) p q hm (le_refl _)
  exact ⟨ρ, U, hρ, hρA, hρb, hUc, hUu,
    dirichlet_mixed_boundary_contDiffAt_of_finite_energy
      hρ hρ hs p q hhigh hUc hUu⟩

/-- Both first derivatives can be represented on the same real
rectangle. Their all-order bottom smoothness is still obtained from
order-dependent smaller energy rectangles, rather than from a fixed
rectangle carrying an assumed all-order estimate. -/
theorem exists_dirichlet_gradient_smooth_boundary_fields {A b : ℝ}
    {u : ℂ → ℂ}
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hhigh : ∀ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ∀ j k : ℕ, j + k ≤ N → MemLp (dirichletMixedDerivative j k u) 2
        (volume.restrict (smoothDirichletHalfBox ρ ρ))) :
    ∃ (ρ : ℝ) (X Y : ℂ → ℂ), 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ContinuousOn X (smoothDirichletClosedHalfBox ρ ρ) ∧
      ContinuousOn Y (smoothDirichletClosedHalfBox ρ ρ) ∧
      EqOn X (dirD u 1) (smoothDirichletHalfBox ρ ρ) ∧
      EqOn Y (dirD u Complex.I) (smoothDirichletHalfBox ρ ρ) ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => X (x : ℂ)) 0 ∧
      ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Y (x : ℂ)) 0 := by
  obtain ⟨ρ, hρ, hρA, hρb, hm⟩ := hhigh 3
  have hWU : smoothDirichletHalfBox ρ ρ ⊆ smoothDirichletHalfBox A b := by
    intro z hz
    exact ⟨hz.1.trans (by linarith), hz.2.1, hz.2.2.trans hρb⟩
  obtain ⟨X, hXc, hXu⟩ := dirichlet_mixed_exists_continuous_extension
    hρ hρ (hs.mono hWU) 3 1 0 hm (by omega)
  obtain ⟨Y, hYc, hYu⟩ := dirichlet_mixed_exists_continuous_extension
    hρ hρ (hs.mono hWU) 3 0 1 hm (by omega)
  have hXs := dirichlet_mixed_boundary_contDiffAt_of_finite_energy
    hρ hρ hs 1 0 hhigh hXc hXu
  have hYs := dirichlet_mixed_boundary_contDiffAt_of_finite_energy
    hρ hρ hs 0 1 hhigh hYc hYu
  exact ⟨ρ, X, Y, hρ, hρA, hρb, hXc, hYc, hXu, hYu, hXs, hYs⟩

/-- Every actual mixed derivative of the original pulled-back harmonic
remainder has a smooth bottom restriction at the chart center. The
datum and the graph chart are selected only once from the original
smooth-domain hypotheses; the genuine smaller rectangle may depend
on the field and on the finite order used to prove smoothness. -/
theorem exists_riemannMapping_flattened_smooth_boundary_fields {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (d : smoothTraceTests) (c : ℂ) (hc : c ≠ 0)
      (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (K : NNReal) (A b : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < A ∧ 0 < b ∧
      (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
       let u := riemannMappingDirichletRemainder F d ∘ Ψ
       let U := smoothDirichletHalfBox A b
       MapsTo Ψ U Ω ∧ ContinuousOn u (smoothDirichletClosedHalfBox A b) ∧
       ContDiffOn ℝ (⊤ : ℕ∞) u U ∧
       (∀ x : ℝ, |x| < A → u (x : ℂ) = 0) ∧
       ∀ j q : ℕ, ∃ (ρ : ℝ) (V : ℂ → ℂ),
         0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
         ContinuousOn V (smoothDirichletClosedHalfBox ρ ρ) ∧
         EqOn V (dirichletMixedDerivative j q u) (smoothDirichletHalfBox ρ ρ) ∧
         ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => V (x : ℂ)) 0) := by
  obtain ⟨d, c, hc, f, hf, K, A, b, hc₁, hLip, hf₀, hA, hb₀,
    hmap, hu, hs, hz, _, _, hhigh⟩ :=
    exists_riemannMapping_flattened_all_mixed_orders hb hS hsc F hF hinj himage hp
  refine ⟨d, c, hc, f, hf, K, A, b, hc₁, hLip, hf₀, hA, hb₀,
    hmap, hu, hs, hz, ?_⟩
  intro j q
  exact exists_dirichlet_mixed_boundary_contDiffAt hs hhigh j q

/-- The common first-gradient pair needed by the genuine inverse-map
boundary ODE is obtained directly from the original smooth-domain
data and the proved finite-order energy/recovery chain. -/
theorem exists_riemannMapping_flattened_gradient_smooth_boundary_fields {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (d : smoothTraceTests) (c : ℂ) (hc : c ≠ 0)
      (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (K : NNReal) (A b ρ : ℝ)
      (X Y : ℂ → ℂ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < A ∧ 0 < b ∧
      0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
       let u := riemannMappingDirichletRemainder F d ∘ Ψ
       let U := smoothDirichletHalfBox A b
       MapsTo Ψ U Ω ∧ ContinuousOn u (smoothDirichletClosedHalfBox A b) ∧
       ContDiffOn ℝ (⊤ : ℕ∞) u U ∧
       (∀ x : ℝ, |x| < A → u (x : ℂ) = 0) ∧
       ContinuousOn X (smoothDirichletClosedHalfBox ρ ρ) ∧
       ContinuousOn Y (smoothDirichletClosedHalfBox ρ ρ) ∧
       EqOn X (dirD u 1) (smoothDirichletHalfBox ρ ρ) ∧
       EqOn Y (dirD u Complex.I) (smoothDirichletHalfBox ρ ρ) ∧
       ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => X (x : ℂ)) 0 ∧
       ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Y (x : ℂ)) 0) := by
  obtain ⟨d, c, hc, f, hf, K, A, b, hc₁, hLip, hf₀, hA, hb₀,
    hmap, hu, hs, hz, _, _, hhigh⟩ :=
    exists_riemannMapping_flattened_all_mixed_orders hb hS hsc F hF hinj himage hp
  obtain ⟨ρ, X, Y, hρ, hρA, hρb, hXc, hYc, hXu, hYu, hXs, hYs⟩ :=
    exists_dirichlet_gradient_smooth_boundary_fields hs hhigh
  exact ⟨d, c, hc, f, hf, K, A, b, ρ, X, Y, hc₁, hLip, hf₀, hA, hb₀,
    hρ, hρA, hρb, hmap, hu, hs, hz, hXc, hYc, hXu, hYu, hXs, hYs⟩

/-- The actual domain correspondence of the chosen smooth graph is
retained along with the constructed smooth boundary-gradient pair.
Thus downstream boundary inverse-map arguments can prove frontier
membership from the same genuine chart, without changing witnesses. -/
theorem exists_riemannMapping_genuine_gradient_smooth_boundary_fields {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (d : smoothTraceTests) (c : ℂ) (hc : c ≠ 0)
      (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (K : NNReal) (A b ρ : ℝ)
      (X Y : ℂ → ℂ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < A ∧ 0 < b ∧
      0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
       let u := riemannMappingDirichletRemainder F d ∘ Ψ
       let U := smoothDirichletHalfBox A b
       (∀ z : ℂ, |z.re| < A → |z.im| < b → (Ψ z ∈ Ω ↔ 0 < z.im)) ∧
       MapsTo Ψ (smoothDirichletClosedHalfBox A b) (closure Ω) ∧
       MapsTo Ψ U Ω ∧ ContinuousOn u (smoothDirichletClosedHalfBox A b) ∧
       ContDiffOn ℝ (⊤ : ℕ∞) u U ∧
       (∀ x : ℝ, |x| < A → u (x : ℂ) = 0) ∧
       ContinuousOn X (smoothDirichletClosedHalfBox ρ ρ) ∧
       ContinuousOn Y (smoothDirichletClosedHalfBox ρ ρ) ∧
       EqOn X (dirD u 1) (smoothDirichletHalfBox ρ ρ) ∧
       EqOn Y (dirD u Complex.I) (smoothDirichletHalfBox ρ ρ) ∧
       ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => X (x : ℂ)) 0 ∧
       ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => Y (x : ℂ)) 0) := by
  obtain ⟨d, c, hc, f, hf, K, A, b, hc₁, hLip, hf₀, hA, hb₀,
    hchart, hclosed, hmap, hu, hs, hz, _, _, hhigh⟩ :=
    exists_riemannMapping_flattened_genuine_chart_all_mixed_orders
      hb hS hsc F hF hinj himage hp
  obtain ⟨ρ, X, Y, hρ, hρA, hρb, hXc, hYc, hXu, hYu, hXs, hYs⟩ :=
    exists_dirichlet_gradient_smooth_boundary_fields hs hhigh
  exact ⟨d, c, hc, f, hf, K, A, b, ρ, X, Y, hc₁, hLip, hf₀, hA, hb₀,
    hρ, hρA, hρb, hchart, hclosed, hmap, hu, hs, hz, hXc, hYc, hXu, hYu, hXs, hYs⟩

end PolyaNeumann

end
