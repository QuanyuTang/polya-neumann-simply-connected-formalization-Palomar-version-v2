module

public import RequestProject.LocalDirichletNormalRecovery
public import RequestProject.LocalDirichletHigherDifferences
public import RequestProject.LocalDirichletTangentialBootstrap

/-!
Actual finite-order normal recovery in a smooth graph half rectangle.
The forcing convention is `div(A ∇u) = -G`. Every recovered derivative
is an ordinary directional derivative of the actual smooth interior
function. The only solution regularity inputs are tangential L² data;
normal derivatives are obtained from the equation. A finite-order
statement permits the genuine tangential energy theorem to shrink the
rectangle with the order. No derivative is evaluated on the flat boundary.
This module is part of the verified dependency chain.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PolyaNeumann

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff

theorem dirichletBootstrap_differentiableAt {U : Set ℂ} (hU : IsOpen U)
    {v : ℂ → ℂ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) {z : ℂ} (hz : z ∈ U) :
    DifferentiableAt ℝ v z :=
  (hv.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)

theorem dirichletBootstrap_contDiff_const_mul {v : ℂ → ℂ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (c : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => c * v z) := contDiff_const.mul hv

theorem dirichletBootstrap_contDiffOn_const_mul {U : Set ℂ} {v : ℂ → ℂ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) (c : ℂ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => c * v z) U := contDiffOn_const.mul hv

/-- Iteration of the actual real directional derivative. -/
def dirichletCoordinateDerivative (w : ℂ) : ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | 0, u => u
  | k + 1, u => dirD (dirichletCoordinateDerivative w k u) w

@[simp] theorem dirichletCoordinateDerivative_zero (w : ℂ) (u : ℂ → ℂ) :
    dirichletCoordinateDerivative w 0 u = u := rfl

@[simp] theorem dirichletCoordinateDerivative_succ (w : ℂ) (k : ℕ) (u : ℂ → ℂ) :
    dirichletCoordinateDerivative w (k + 1) u =
      dirD (dirichletCoordinateDerivative w k u) w := rfl

theorem dirichletCoordinateDerivative_one_eq_tangential (k : ℕ) (u : ℂ → ℂ) :
    dirichletCoordinateDerivative 1 k u = dirichletTangentialDerivative k u := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [dirichletCoordinateDerivative_succ, dirichletTangentialDerivative_succ, ih]

theorem dirichletCoordinateDerivative_succ_right (w : ℂ) (k : ℕ) (u : ℂ → ℂ) :
    dirichletCoordinateDerivative w k (dirD u w) =
      dirichletCoordinateDerivative w (k + 1) u := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [dirichletCoordinateDerivative_succ, ih]
      rfl

theorem dirichletCoordinateDerivative_iterate (w : ℂ) (k l : ℕ) (u : ℂ → ℂ) :
    dirichletCoordinateDerivative w k (dirichletCoordinateDerivative w l u) =
      dirichletCoordinateDerivative w (k + l) u := by
  induction k with
  | zero => simp only [dirichletCoordinateDerivative_zero, Nat.zero_add]
  | succ k ih =>
      rw [dirichletCoordinateDerivative_succ, ih]
      simp only [Nat.succ_add, dirichletCoordinateDerivative_succ]

theorem dirichletCoordinateDerivative_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (w : ℂ) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirichletCoordinateDerivative w k u) U := by
  induction k with
  | zero => exact hu
  | succ k ih => exact dirichlet_contDiffOn_dirD hU ih w

theorem dirichletCoordinateDerivative_contDiff {u : ℂ → ℂ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (w : ℂ) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (dirichletCoordinateDerivative w k u) := by
  induction k with
  | zero => exact hu
  | succ k ih => exact dirichlet_dirD_contDiff ih w

theorem dirichletCoordinateDerivative_eventuallyEq {u v : ℂ → ℂ} {z : ℂ}
    (heq : u =ᶠ[𝓝 z] v) (w : ℂ) (k : ℕ) :
    dirichletCoordinateDerivative w k u =ᶠ[𝓝 z] dirichletCoordinateDerivative w k v := by
  induction k with
  | zero => exact heq
  | succ k ih =>
      exact (ih.fderiv (𝕜 := ℝ)).fun_comp (fun A : ℂ →L[ℝ] ℂ => A w)

theorem dirichletCoordinateDerivative_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u v : ℂ → ℂ} (heq : EqOn u v U) (w : ℂ) (k : ℕ) :
    EqOn (dirichletCoordinateDerivative w k u) (dirichletCoordinateDerivative w k v) U := by
  intro z hz
  have hg : u =ᶠ[𝓝 z] v := Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hz, heq⟩
  exact (dirichletCoordinateDerivative_eventuallyEq hg w k).self_of_nhds

theorem dirichlet_bootstrap_dirD_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u v : ℂ → ℂ} (heq : EqOn u v U) (w : ℂ) : EqOn (dirD u w) (dirD v w) U :=
  dirichletCoordinateDerivative_eqOn hU heq w 1

theorem dirichlet_bootstrap_dirD_const_mul {u : ℂ → ℂ} {z : ℂ}
    (hu : DifferentiableAt ℝ u z) (c w : ℂ) :
    dirD (fun x => c * u x) w z = c * dirD u w z := by
  change fderiv ℝ (fun x => c * u x) z w = _
  rw [fderiv_const_mul hu c]
  rfl

theorem dirichletCoordinateDerivative_add_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u v : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) (w : ℂ) (k : ℕ) :
    EqOn (dirichletCoordinateDerivative w k (fun z => u z + v z))
      (fun z => dirichletCoordinateDerivative w k u z +
        dirichletCoordinateDerivative w k v z) U := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      rw [dirichletCoordinateDerivative_succ,
        dirichlet_bootstrap_dirD_eqOn hU ih w hz]
      exact dirichlet_normal_dirD_add
        (dirichletBootstrap_differentiableAt hU
          (dirichletCoordinateDerivative_contDiffOn hU hu w k) hz)
        (dirichletBootstrap_differentiableAt hU
          (dirichletCoordinateDerivative_contDiffOn hU hv w k) hz) w

theorem dirichletCoordinateDerivative_sub_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u v : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) (w : ℂ) (k : ℕ) :
    EqOn (dirichletCoordinateDerivative w k (fun z => u z - v z))
      (fun z => dirichletCoordinateDerivative w k u z -
        dirichletCoordinateDerivative w k v z) U := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      rw [dirichletCoordinateDerivative_succ,
        dirichlet_bootstrap_dirD_eqOn hU ih w hz]
      exact dirichlet_normal_dirD_sub
        (dirichletBootstrap_differentiableAt hU
          (dirichletCoordinateDerivative_contDiffOn hU hu w k) hz)
        (dirichletBootstrap_differentiableAt hU
          (dirichletCoordinateDerivative_contDiffOn hU hv w k) hz) w

theorem dirichletCoordinateDerivative_const_mul_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (c w : ℂ) (k : ℕ) :
    EqOn (dirichletCoordinateDerivative w k (fun z => c * u z))
      (fun z => c * dirichletCoordinateDerivative w k u z) U := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      rw [dirichletCoordinateDerivative_succ,
        dirichlet_bootstrap_dirD_eqOn hU ih w hz]
      exact dirichlet_bootstrap_dirD_const_mul
        (dirichletBootstrap_differentiableAt hU
          (dirichletCoordinateDerivative_contDiffOn hU hu w k) hz) c w

/-- A coefficient whose derivative in w is zero passes through every
actual w-derivative. No assertion about derivatives at the boundary is used. -/
theorem dirichletCoordinateDerivative_mul_eqOn_of_dirD_zero {U : Set ℂ}
    (hU : IsOpen U) {a u : ℂ → ℂ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a U)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (w : ℂ)
    (hzero : ∀ z ∈ U, dirD a w z = 0) (k : ℕ) :
    EqOn (dirichletCoordinateDerivative w k (fun z => a z * u z))
      (fun z => a z * dirichletCoordinateDerivative w k u z) U := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      rw [dirichletCoordinateDerivative_succ,
        dirichlet_bootstrap_dirD_eqOn hU ih w hz,
        dirichlet_normal_dirD_mul
          (dirichletBootstrap_differentiableAt hU ha hz)
          (dirichletBootstrap_differentiableAt hU
            (dirichletCoordinateDerivative_contDiffOn hU hu w k) hz) w, hzero z hz]
      simp only [zero_mul, zero_add, dirichletCoordinateDerivative_succ]

/-- Coordinate commutation follows from the actual smooth interior germ. -/
theorem dirichletCoordinateDerivative_dirD_comm_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (v w : ℂ) (k : ℕ) :
    EqOn (dirichletCoordinateDerivative v k (dirD u w))
      (dirD (dirichletCoordinateDerivative v k u) w) U := by
  induction k with
  | zero => intro z hz; rfl
  | succ k ih =>
      intro z hz
      rw [dirichletCoordinateDerivative_succ,
        dirichlet_bootstrap_dirD_eqOn hU ih v hz]
      exact dirichlet_normal_dirD_comm hU
        (dirichletCoordinateDerivative_contDiffOn hU hu v k) hz w v

theorem dirichletCoordinateDerivative_comm_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (v w : ℂ) (p q : ℕ) :
    EqOn (dirichletCoordinateDerivative v p (dirichletCoordinateDerivative w q u))
      (dirichletCoordinateDerivative w q (dirichletCoordinateDerivative v p u)) U := by
  induction q with
  | zero => intro z hz; rfl
  | succ q ih =>
      intro z hz
      rw [dirichletCoordinateDerivative_succ,
        dirichletCoordinateDerivative_dirD_comm_eqOn hU
          (dirichletCoordinateDerivative_contDiffOn hU hu w q) v w p hz,
        dirichlet_bootstrap_dirD_eqOn hU ih w hz]
      rfl

/-- q actual derivatives in the flattened normal direction. -/
def dirichletNormalDerivative (q : ℕ) (u : ℂ → ℂ) : ℂ → ℂ :=
  dirichletCoordinateDerivative Complex.I q u

/-- The p tangential and q normal actual partial derivative. -/
def dirichletMixedDerivative (p q : ℕ) (u : ℂ → ℂ) : ℂ → ℂ :=
  dirichletTangentialDerivative p (dirichletNormalDerivative q u)

theorem dirichletMixedDerivative_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (p q : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirichletMixedDerivative p q u) U := by
  rw [dirichletMixedDerivative, ← dirichletCoordinateDerivative_one_eq_tangential]
  exact dirichletCoordinateDerivative_contDiffOn hU
    (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I q) 1 p

theorem dirichletMixedDerivative_contDiff {u : ℂ → ℂ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (p q : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (dirichletMixedDerivative p q u) := by
  rw [dirichletMixedDerivative, ← dirichletCoordinateDerivative_one_eq_tangential]
  exact dirichletCoordinateDerivative_contDiff
    (dirichletCoordinateDerivative_contDiff hu Complex.I q) 1 p

theorem dirichletMixedDerivative_eq_normal_tangential {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (p q : ℕ) :
    EqOn (dirichletMixedDerivative p q u)
      (dirichletNormalDerivative q (dirichletTangentialDerivative p u)) U := by
  simpa only [dirichletMixedDerivative, dirichletNormalDerivative,
    dirichletCoordinateDerivative_one_eq_tangential] using
      dirichletCoordinateDerivative_comm_eqOn hU hu 1 Complex.I p q

theorem dirD_dirichletMixedDerivative_one (p q : ℕ) (u : ℂ → ℂ) :
    dirD (dirichletMixedDerivative p q u) 1 = dirichletMixedDerivative (p + 1) q u := rfl

theorem dirD_dirichletMixedDerivative_I_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (p q : ℕ) :
    EqOn (dirD (dirichletMixedDerivative p q u) Complex.I)
      (dirichletMixedDerivative p (q + 1) u) U := by
  intro z hz
  simpa only [dirichletMixedDerivative, dirichletNormalDerivative,
    dirichletCoordinateDerivative_succ, dirichletCoordinateDerivative_one_eq_tangential] using
      (dirichletCoordinateDerivative_dirD_comm_eqOn hU
        (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I q) 1 Complex.I p hz).symm

/-! The coefficient bounds below are genuine compact bounds on the actual
closed rectangle. Only the smooth coefficient, not the solution, is bounded. -/

theorem dirichletBootstrap_smooth_mul_memLp {a b : ℝ} {c v : ℂ → ℂ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hv : MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (fun z => c z * v z) 2 (volume.restrict (smoothDirichletHalfBox a b)) := by
  obtain ⟨M, hM⟩ := (isCompact_smoothDirichletClosedHalfBox a b).exists_bound_of_continuousOn
    hc.continuous.continuousOn
  apply hv.of_le_mul (c := M) (hc.continuous.aestronglyMeasurable.mul hv.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
    with z hz
  change ‖c z * v z‖ ≤ M * ‖v z‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (hM z ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩) (norm_nonneg _)

/-- Recursive Leibniz recovery in L². Each recursive call uses strictly
fewer tangential derivatives of the actual input. The coefficient and all
its tangential derivatives have the compact bounds just proved. -/
theorem dirichletBootstrap_tangential_mul_memLp {a b : ℝ} {c v : ℂ → ℂ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b)) (p : ℕ)
    (hLp : ∀ j ≤ p, MemLp (dirichletTangentialDerivative j v) 2
      (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (dirichletTangentialDerivative p (fun z => c z * v z)) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  induction p generalizing c v with
  | zero => exact dirichletBootstrap_smooth_mul_memLp hc (hLp 0 le_rfl)
  | succ p ih =>
      let U := smoothDirichletHalfBox a b
      have hU : IsOpen U := isOpen_smoothDirichletHalfBox a b
      have hdv := dirichlet_contDiffOn_dirD hU hv 1
      have hdc := dirichlet_dirD_contDiff hc 1
      have h₀ := ih hdc hv (fun j hj => hLp j (by omega))
      have h₁ := ih hc hdv (fun j hj => by
        rw [dirichletTangentialDerivative_succ_right]
        exact hLp (j + 1) (by omega))
      have hsplit : EqOn (dirD (fun z => c z * v z) 1)
          (fun z => dirD c 1 z * v z + c z * dirD v 1 z) U := by
        intro z hz
        exact dirichlet_normal_dirD_mul (hc.differentiable (by simp) z)
          (dirichletBootstrap_differentiableAt hU hv hz) 1
      have hiter := dirichletCoordinateDerivative_eqOn hU hsplit 1 p
      have hadd := dirichletCoordinateDerivative_add_eqOn hU
        (hdc.contDiffOn.mul hv) (hc.contDiffOn.mul hdv) 1 p
      have heq : (dirichletTangentialDerivative (p + 1) (fun z => c z * v z))
          =ᵐ[volume.restrict U]
            (fun z => dirichletTangentialDerivative p (fun w => dirD c 1 w * v w) z +
              dirichletTangentialDerivative p (fun w => c w * dirD v 1 w) z) := by
        filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
        rw [← dirichletTangentialDerivative_succ_right]
        simpa only [dirichletCoordinateDerivative_one_eq_tangential] using
          (hiter hz).trans (hadd hz)
      exact (h₀.add h₁).ae_eq heq.symm

theorem dirichletBootstrap_tangential_add_memLp {U : Set ℂ} (hU : IsOpen U)
    {v w : ℂ → ℂ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U)
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w U) (p : ℕ)
    (hvLp : MemLp (dirichletTangentialDerivative p v) 2 (volume.restrict U))
    (hwLp : MemLp (dirichletTangentialDerivative p w) 2 (volume.restrict U)) :
    MemLp (dirichletTangentialDerivative p (fun z => v z + w z)) 2 (volume.restrict U) := by
  apply (hvLp.add hwLp).ae_eq
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  simpa only [dirichletCoordinateDerivative_one_eq_tangential, Pi.add_apply] using
    (dirichletCoordinateDerivative_add_eqOn hU hv hw 1 p hz).symm

theorem dirichletBootstrap_tangential_sub_memLp {U : Set ℂ} (hU : IsOpen U)
    {v w : ℂ → ℂ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U)
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w U) (p : ℕ)
    (hvLp : MemLp (dirichletTangentialDerivative p v) 2 (volume.restrict U))
    (hwLp : MemLp (dirichletTangentialDerivative p w) 2 (volume.restrict U)) :
    MemLp (dirichletTangentialDerivative p (fun z => v z - w z)) 2 (volume.restrict U) := by
  apply (hvLp.sub hwLp).ae_eq
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  simpa only [dirichletCoordinateDerivative_one_eq_tangential, Pi.sub_apply] using
    (dirichletCoordinateDerivative_sub_eqOn hU hv hw 1 p hz).symm

/-! Coefficients depend only on the actual horizontal coordinate. -/

theorem dirichletBootstrap_realCoefficient_dirD_I {r : ℝ → ℝ}
    (hr : ContDiff ℝ (⊤ : ℕ∞) r) (z : ℂ) :
    dirD (fun w : ℂ => (r w.re : ℂ)) Complex.I z = 0 := by
  have hd := (hr.differentiable (by simp)) z.re
  have hs := Complex.ofRealCLM.hasFDerivAt.comp z
    (hd.hasDerivAt.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt)
  change fderiv ℝ (Complex.ofRealCLM ∘ r ∘ Complex.re) z Complex.I = 0
  rw [hs.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    Complex.reCLM_apply, Complex.I_re, smul_zero, map_zero]

theorem dirichletGraphCurvature_contDiff {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (dirichletGraphCurvature f) := by
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  exact Complex.ofRealCLM.contDiff.comp
    (((contDiff_infty_iff_deriv.mp hd).2).comp Complex.reCLM.contDiff)

theorem dirD_dirichletGraphCurvature_I {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : ℂ) :
    dirD (dirichletGraphCurvature f) Complex.I z = 0 := by
  exact dirichletBootstrap_realCoefficient_dirD_I
    ((contDiff_infty_iff_deriv.mp ((contDiff_infty_iff_deriv.mp hf).2)).2) z

theorem dirichletNormalCoefficientInverse_contDiff {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (dirichletNormalCoefficientInverse f) := by
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  have hr : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (1 + (deriv f x) ^ 2)⁻¹) :=
    (contDiff_const.add (hd.pow 2)).inv (fun x => by positivity)
  exact Complex.ofRealCLM.contDiff.comp (hr.comp Complex.reCLM.contDiff)

theorem dirD_dirichletNormalCoefficientInverse_I {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : ℂ) :
    dirD (dirichletNormalCoefficientInverse f) Complex.I z = 0 := by
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  have hr : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (1 + (deriv f x) ^ 2)⁻¹) :=
    (contDiff_const.add (hd.pow 2)).inv (fun x => by positivity)
  exact dirichletBootstrap_realCoefficient_dirD_I hr z

theorem dirD_two_mul_dirichletGraphSlope_I {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : ℂ) :
    dirD (fun w => (2 : ℂ) * dirichletGraphSlope f w) Complex.I z = 0 := by
  rw [dirichlet_bootstrap_dirD_const_mul
    ((dirichletGraphSlope_contDiff hf).differentiable (by simp) z),
    dirD_dirichletGraphSlope_I hf z, mul_zero]

theorem dirichletNormalDerivative_mixed_eqOn {U : Set ℂ} (hU : IsOpen U)
    {u : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (q p r : ℕ) :
    EqOn (dirichletNormalDerivative q (dirichletMixedDerivative p r u))
      (dirichletMixedDerivative p (q + r) u) U := by
  intro z hz
  have hc := dirichletCoordinateDerivative_comm_eqOn hU
    (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I r) 1 Complex.I p q hz
  simpa only [dirichletNormalDerivative, dirichletMixedDerivative,
    dirichletCoordinateDerivative_one_eq_tangential,
    dirichletCoordinateDerivative_iterate] using hc.symm

/-- The actual recovered numerator after q normal differentiations. -/
def dirichletNormalRecoveryExpression (f : ℝ → ℝ) (q : ℕ) (u G : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((-1 : ℂ) * dirichletNormalDerivative q G z +
    dirichletGraphCurvature f z * dirichletNormalDerivative (q + 1) u z) +
    ((2 : ℂ) * dirichletGraphSlope f z) * dirichletMixedDerivative 1 (q + 1) u z -
    dirichletMixedDerivative 2 q u z

theorem dirichletNormalRecoveryExpression_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u G : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U) (q : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (dirichletNormalRecoveryExpression f q u G) U := by
  have h₀ := dirichletBootstrap_contDiffOn_const_mul
    (dirichletCoordinateDerivative_contDiffOn hU hG Complex.I q) (-1)
  have h₁ := (dirichletGraphCurvature_contDiff hf).contDiffOn.mul
    (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I (q + 1))
  have h₂ := (dirichletBootstrap_contDiff_const_mul
    (dirichletGraphSlope_contDiff hf) 2).contDiffOn.mul
    (dirichletMixedDerivative_contDiffOn hU hu 1 (q + 1))
  exact ((h₀.add h₁).add h₂).sub (dirichletMixedDerivative_contDiffOn hU hu 2 q)

theorem dirichletNormalRecoveryExpression_zero_normal_eqOn {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u G : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U) (q : ℕ) :
    EqOn (dirichletNormalDerivative q (dirichletNormalRecoveryExpression f 0 u G))
      (dirichletNormalRecoveryExpression f q u G) U := by
  let t₀ : ℂ → ℂ := fun z => (-1 : ℂ) * G z
  let t₁ : ℂ → ℂ := fun z => dirichletGraphCurvature f z * dirichletNormalDerivative 1 u z
  let t₂ : ℂ → ℂ := fun z => ((2 : ℂ) * dirichletGraphSlope f z) *
    dirichletMixedDerivative 1 1 u z
  let t₃ := dirichletMixedDerivative 2 0 u
  have h₀ : ContDiffOn ℝ (⊤ : ℕ∞) t₀ U := dirichletBootstrap_contDiffOn_const_mul hG (-1)
  have h₁ : ContDiffOn ℝ (⊤ : ℕ∞) t₁ U :=
    (dirichletGraphCurvature_contDiff hf).contDiffOn.mul
      (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I 1)
  have h₂ : ContDiffOn ℝ (⊤ : ℕ∞) t₂ U :=
    (dirichletBootstrap_contDiff_const_mul (dirichletGraphSlope_contDiff hf) 2).contDiffOn.mul
      (dirichletMixedDerivative_contDiffOn hU hu 1 1)
  have h₃ : ContDiffOn ℝ (⊤ : ℕ∞) t₃ U := dirichletMixedDerivative_contDiffOn hU hu 2 0
  intro z hz
  change dirichletCoordinateDerivative Complex.I q
    (fun w => (t₀ w + t₁ w) + t₂ w - t₃ w) z = _
  rw [dirichletCoordinateDerivative_sub_eqOn hU ((h₀.add h₁).add h₂) h₃ Complex.I q hz]
  change dirichletCoordinateDerivative Complex.I q
      (fun w => (t₀ w + t₁ w) + t₂ w) z -
    dirichletCoordinateDerivative Complex.I q t₃ z = _
  rw [dirichletCoordinateDerivative_add_eqOn hU (h₀.add h₁) h₂ Complex.I q hz]
  change (dirichletCoordinateDerivative Complex.I q (fun w => t₀ w + t₁ w) z +
      dirichletCoordinateDerivative Complex.I q t₂ z) -
    dirichletCoordinateDerivative Complex.I q t₃ z = _
  rw [dirichletCoordinateDerivative_add_eqOn hU h₀ h₁ Complex.I q hz]
  change (dirichletCoordinateDerivative Complex.I q t₀ z +
      dirichletCoordinateDerivative Complex.I q t₁ z) +
    dirichletCoordinateDerivative Complex.I q t₂ z -
    dirichletCoordinateDerivative Complex.I q t₃ z = _
  have ht₀ := dirichletCoordinateDerivative_const_mul_eqOn hU hG (-1) Complex.I q hz
  have ht₁ := dirichletCoordinateDerivative_mul_eqOn_of_dirD_zero hU
    (dirichletGraphCurvature_contDiff hf).contDiffOn
    (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I 1) Complex.I
    (fun w _ => dirD_dirichletGraphCurvature_I hf w) q hz
  have ht₂ := dirichletCoordinateDerivative_mul_eqOn_of_dirD_zero hU
    (dirichletBootstrap_contDiff_const_mul (dirichletGraphSlope_contDiff hf) 2).contDiffOn
    (dirichletMixedDerivative_contDiffOn hU hu 1 1) Complex.I
    (fun w _ => dirD_two_mul_dirichletGraphSlope_I hf w) q hz
  change dirichletCoordinateDerivative Complex.I q t₀ z = _ at ht₀
  change dirichletCoordinateDerivative Complex.I q t₁ z = _ at ht₁
  change dirichletCoordinateDerivative Complex.I q t₂ z = _ at ht₂
  rw [ht₀, ht₁, ht₂]
  have hn₁ : dirichletCoordinateDerivative Complex.I q (dirichletNormalDerivative 1 u) =
      dirichletNormalDerivative (q + 1) u :=
    dirichletCoordinateDerivative_iterate Complex.I q 1 u
  have hmix₁ := dirichletNormalDerivative_mixed_eqOn hU hu q 1 1 hz
  have hmix₂ := dirichletNormalDerivative_mixed_eqOn hU hu q 2 0 hz
  change dirichletCoordinateDerivative Complex.I q (dirichletMixedDerivative 1 1 u) z = _
    at hmix₁
  change dirichletCoordinateDerivative Complex.I q t₃ z = _ at hmix₂
  change -1 * dirichletCoordinateDerivative Complex.I q G z +
    dirichletGraphCurvature f z *
      dirichletCoordinateDerivative Complex.I q (dirichletNormalDerivative 1 u) z +
    2 * dirichletGraphSlope f z *
      dirichletCoordinateDerivative Complex.I q (dirichletMixedDerivative 1 1 u) z -
    dirichletCoordinateDerivative Complex.I q t₃ z = _
  rw [hn₁, hmix₁, hmix₂]
  simp only [Nat.add_zero, dirichletNormalRecoveryExpression, dirichletNormalDerivative]

/-- Every higher normal formula is derived by differentiating the actual
second-order equation. All Y derivatives of the graph coefficients vanish. -/
theorem dirichlet_normal_higher_derivative_recovery {U : Set ℂ} (hU : IsOpen U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {u G : ℂ → ℂ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (hstrong : ∀ z ∈ U, dirichletFlattenedDivergence f u z = -G z) (q : ℕ) :
    EqOn (dirichletNormalDerivative (q + 2) u)
      (fun z => dirichletNormalCoefficientInverse f z *
        dirichletNormalRecoveryExpression f q u G z) U := by
  have hbase : EqOn (dirichletNormalDerivative 2 u)
      (fun z => dirichletNormalCoefficientInverse f z *
        dirichletNormalRecoveryExpression f 0 u G z) U := by
    intro z hz
    have hr := dirichlet_normal_derivative_recovery hU hf hu hstrong hz
    rw [dirichlet_normal_dirD_comm hU hu hz 1 Complex.I] at hr
    simpa only [dirichletNormalRecoveryExpression, dirichletMixedDerivative,
      dirichletNormalDerivative, dirichletCoordinateDerivative, dirichletTangentialDerivative,
      neg_one_mul, mul_assoc] using hr
  have hq := dirichletCoordinateDerivative_eqOn hU hbase Complex.I q
  have hmul := dirichletCoordinateDerivative_mul_eqOn_of_dirD_zero hU
    (dirichletNormalCoefficientInverse_contDiff hf).contDiffOn
    (dirichletNormalRecoveryExpression_contDiffOn hU hf hu hG 0) Complex.I
    (fun z _ => dirD_dirichletNormalCoefficientInverse_I hf z) q
  intro z hz
  have hleft : dirichletCoordinateDerivative Complex.I q (dirichletNormalDerivative 2 u) =
      dirichletNormalDerivative (q + 2) u :=
    dirichletCoordinateDerivative_iterate Complex.I q 2 u
  rw [← hleft]
  exact (hq hz).trans ((hmul hz).trans (congrArg
    (fun v : ℂ => dirichletNormalCoefficientInverse f z * v)
      (dirichletNormalRecoveryExpression_zero_normal_eqOn hU hf hu hG q hz)))

/-! L² closure on the actual half rectangle. -/

theorem dirichletTangentialDerivative_mixed (j p q : ℕ) (u : ℂ → ℂ) :
    dirichletTangentialDerivative j (dirichletMixedDerivative p q u) =
      dirichletMixedDerivative (j + p) q u := by
  simpa only [dirichletCoordinateDerivative_one_eq_tangential, dirichletMixedDerivative] using
    dirichletCoordinateDerivative_iterate 1 j p (dirichletNormalDerivative q u)

theorem dirichletBootstrap_tangential_const_mul_memLp {U : Set ℂ} (hU : IsOpen U)
    {v : ℂ → ℂ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) (c : ℂ) (p : ℕ)
    (hvLp : MemLp (dirichletTangentialDerivative p v) 2 (volume.restrict U)) :
    MemLp (dirichletTangentialDerivative p (fun z => c * v z)) 2 (volume.restrict U) := by
  apply (hvLp.const_mul c).ae_eq
  filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
  simpa only [dirichletCoordinateDerivative_one_eq_tangential] using
    (dirichletCoordinateDerivative_const_mul_eqOn hU hv c 1 p hz).symm

theorem dirichletBootstrap_continuous_memLp {a b : ℝ}
    {v : ℂ → ℂ} (hv : Continuous v) :
    MemLp v 2 (volume.restrict (smoothDirichletHalfBox a b)) := by
  obtain ⟨M, hM⟩ := (isCompact_smoothDirichletClosedHalfBox a b).exists_bound_of_continuousOn
    hv.continuousOn
  letI : IsFiniteMeasure (volume.restrict (smoothDirichletHalfBox a b)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (dirichlet_halfBox_isBounded (a := a) (b := b)).measure_lt_top⟩
  apply MemLp.of_bound hv.aestronglyMeasurable M
  filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
    with z hz
  exact hM z ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩

/-- Every actual forcing derivative is L² on the bounded half rectangle.
This bound belongs to the smooth forcing; none is assumed for the solution. -/
theorem dirichletBootstrap_mixed_forcing_memLp {a b : ℝ}
    {G : ℂ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (p q : ℕ) :
    MemLp (dirichletMixedDerivative p q G) 2
      (volume.restrict (smoothDirichletHalfBox a b)) :=
  dirichletBootstrap_continuous_memLp (dirichletMixedDerivative_contDiff hG p q).continuous

/-- Tangential differentiation of the genuine numerator preserves L²
when the two lower normal levels have their finite cone of L² derivatives. -/
theorem dirichletNormalRecoveryExpression_tangential_memLp {a b : ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {u G : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b))
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (N p q : ℕ) (hp : p + q + 2 ≤ N)
    (h₀ : ∀ j, j + q ≤ N → MemLp (dirichletMixedDerivative j q u) 2
      (volume.restrict (smoothDirichletHalfBox a b)))
    (h₁ : ∀ j, j + (q + 1) ≤ N → MemLp (dirichletMixedDerivative j (q + 1) u) 2
      (volume.restrict (smoothDirichletHalfBox a b))) :
    MemLp (dirichletTangentialDerivative p (dirichletNormalRecoveryExpression f q u G)) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  let U := smoothDirichletHalfBox a b
  have hU : IsOpen U := isOpen_smoothDirichletHalfBox a b
  let t₀ : ℂ → ℂ := fun z => (-1 : ℂ) * dirichletNormalDerivative q G z
  let t₁ : ℂ → ℂ := fun z => dirichletGraphCurvature f z *
    dirichletNormalDerivative (q + 1) u z
  let t₂ : ℂ → ℂ := fun z => ((2 : ℂ) * dirichletGraphSlope f z) *
    dirichletMixedDerivative 1 (q + 1) u z
  let t₃ := dirichletMixedDerivative 2 q u
  have ht₀ : ContDiffOn ℝ (⊤ : ℕ∞) t₀ U :=
    dirichletBootstrap_contDiffOn_const_mul
      (dirichletCoordinateDerivative_contDiffOn hU hG.contDiffOn Complex.I q) (-1)
  have ht₁ : ContDiffOn ℝ (⊤ : ℕ∞) t₁ U :=
    (dirichletGraphCurvature_contDiff hf).contDiffOn.mul
      (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I (q + 1))
  have ht₂ : ContDiffOn ℝ (⊤ : ℕ∞) t₂ U :=
    (dirichletBootstrap_contDiff_const_mul (dirichletGraphSlope_contDiff hf) 2).contDiffOn.mul
      (dirichletMixedDerivative_contDiffOn hU hu 1 (q + 1))
  have ht₃ : ContDiffOn ℝ (⊤ : ℕ∞) t₃ U := dirichletMixedDerivative_contDiffOn hU hu 2 q
  have hm₀ : MemLp (dirichletTangentialDerivative p t₀) 2 (volume.restrict U) :=
    dirichletBootstrap_tangential_const_mul_memLp hU
      (dirichletCoordinateDerivative_contDiffOn hU hG.contDiffOn Complex.I q) (-1) p
        (dirichletBootstrap_mixed_forcing_memLp hG p q)
  have hm₁ : MemLp (dirichletTangentialDerivative p t₁) 2 (volume.restrict U) := by
    apply dirichletBootstrap_tangential_mul_memLp (dirichletGraphCurvature_contDiff hf)
      (dirichletCoordinateDerivative_contDiffOn hU hu Complex.I (q + 1)) p
    intro j hj
    exact h₁ j (by omega)
  have hm₂ : MemLp (dirichletTangentialDerivative p t₂) 2 (volume.restrict U) := by
    apply dirichletBootstrap_tangential_mul_memLp
      (dirichletBootstrap_contDiff_const_mul (dirichletGraphSlope_contDiff hf) 2)
      (dirichletMixedDerivative_contDiffOn hU hu 1 (q + 1)) p
    intro j hj
    rw [dirichletTangentialDerivative_mixed]
    exact h₁ (j + 1) (by omega)
  have hm₃ : MemLp (dirichletTangentialDerivative p t₃) 2 (volume.restrict U) := by
    rw [dirichletTangentialDerivative_mixed]
    exact h₀ (p + 2) (by omega)
  exact dirichletBootstrap_tangential_sub_memLp hU ((ht₀.add ht₁).add ht₂) ht₃ p
    (dirichletBootstrap_tangential_add_memLp hU (ht₀.add ht₁) ht₂ p
      (dirichletBootstrap_tangential_add_memLp hU ht₀ ht₁ p hm₀ hm₁) hm₂) hm₃

/-- Finite-order recovery from genuine tangential data on one actual
half rectangle. The normal-order induction uses only lower normal orders
of the same total order, rather than an assumed higher normal derivative. -/
theorem dirichlet_mixed_derivative_memLp_of_tangential_data {a b : ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {u G : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b))
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hstrong : ∀ z ∈ smoothDirichletHalfBox a b,
      dirichletFlattenedDivergence f u z = -G z) (N : ℕ)
    (htangent : ∀ j ≤ N,
      MemLp (dirichletTangentialDerivative j u) 2
        (volume.restrict (smoothDirichletHalfBox a b)) ∧
      MemLp (dirD (dirichletTangentialDerivative j u) Complex.I) 2
        (volume.restrict (smoothDirichletHalfBox a b))) :
    ∀ p q : ℕ, p + q ≤ N → MemLp (dirichletMixedDerivative p q u) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  let U := smoothDirichletHalfBox a b
  have hU : IsOpen U := isOpen_smoothDirichletHalfBox a b
  have hnormal : ∀ q p : ℕ, p + q ≤ N → MemLp (dirichletMixedDerivative p q u) 2
      (volume.restrict U) := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro p hp
      cases q with
      | zero => exact (htangent p (by omega)).1
      | succ q =>
        cases q with
        | zero =>
            apply (htangent p (by omega)).2.ae_eq
            filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
            exact (dirichletMixedDerivative_eq_normal_tangential hU hu p 1 hz).symm
        | succ q =>
            have hlow₀ : ∀ j, j + q ≤ N → MemLp (dirichletMixedDerivative j q u) 2
                (volume.restrict U) := fun j hj => ih q (by omega) j hj
            have hlow₁ : ∀ j, j + (q + 1) ≤ N →
                MemLp (dirichletMixedDerivative j (q + 1) u) 2 (volume.restrict U) :=
              fun j hj => ih (q + 1) (by omega) j hj
            have hm : MemLp (dirichletTangentialDerivative p
                (fun z => dirichletNormalCoefficientInverse f z *
                  dirichletNormalRecoveryExpression f q u G z)) 2 (volume.restrict U) := by
              apply dirichletBootstrap_tangential_mul_memLp
                (dirichletNormalCoefficientInverse_contDiff hf)
                (dirichletNormalRecoveryExpression_contDiffOn hU hf hu hG.contDiffOn q) p
              intro j hj
              exact dirichletNormalRecoveryExpression_tangential_memLp hf hu hG N j q
                (by omega) hlow₀ hlow₁
            have hrec := dirichletCoordinateDerivative_eqOn hU
              (dirichlet_normal_higher_derivative_recovery hU hf hu hG.contDiffOn hstrong q) 1 p
            apply hm.ae_eq
            filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
            simpa only [dirichletCoordinateDerivative_one_eq_tangential,
              dirichletMixedDerivative] using (hrec hz).symm
  exact fun p q hpq => hnormal q p hpq

theorem dirichlet_mixed_derivative_gradient_memLp_of_tangential_data {a b : ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {u G : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b))
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hstrong : ∀ z ∈ smoothDirichletHalfBox a b,
      dirichletFlattenedDivergence f u z = -G z) (N : ℕ)
    (htangent : ∀ j ≤ N,
      MemLp (dirichletTangentialDerivative j u) 2
        (volume.restrict (smoothDirichletHalfBox a b)) ∧
      MemLp (dirD (dirichletTangentialDerivative j u) Complex.I) 2
        (volume.restrict (smoothDirichletHalfBox a b)))
    (p q : ℕ) (horder : p + q + 1 ≤ N) (i : Fin 2) :
    MemLp (fun z => fderiv ℝ (dirichletMixedDerivative p q u) z (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox a b)) := by
  have hm := dirichlet_mixed_derivative_memLp_of_tangential_data
    hf hu hG hstrong N htangent
  fin_cases i
  · change MemLp (dirD (dirichletMixedDerivative p q u) 1) 2 _
    rw [dirD_dirichletMixedDerivative_one]
    exact hm (p + 1) q (by omega)
  · change MemLp (dirD (dirichletMixedDerivative p q u) Complex.I) 2 _
    apply (hm p (q + 1) (by omega)).ae_eq
    filter_upwards [ae_restrict_mem (isOpen_smoothDirichletHalfBox a b).measurableSet]
      with z hz
    exact (dirD_dirichletMixedDerivative_I_eqOn (isOpen_smoothDirichletHalfBox a b)
      hu p q hz).symm

/-- Compact-test localization proves the weak derivatives of every
recovered partial derivative. The weak identities are not extra inputs. -/
theorem dirichlet_mixed_derivative_isWeakGradient {a b : ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {u G : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b))
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hstrong : ∀ z ∈ smoothDirichletHalfBox a b,
      dirichletFlattenedDivergence f u z = -G z) (N : ℕ)
    (htangent : ∀ j ≤ N,
      MemLp (dirichletTangentialDerivative j u) 2
        (volume.restrict (smoothDirichletHalfBox a b)) ∧
      MemLp (dirD (dirichletTangentialDerivative j u) Complex.I) 2
        (volume.restrict (smoothDirichletHalfBox a b)))
    (p q : ℕ) (horder : p + q + 1 ≤ N) :
    IsWeakGradient (smoothDirichletHalfBox a b)
      ((dirichlet_mixed_derivative_memLp_of_tangential_data hf hu hG hstrong
        N htangent p q (by omega)).toLp (dirichletMixedDerivative p q u))
      (fun i => (dirichlet_mixed_derivative_gradient_memLp_of_tangential_data
        hf hu hG hstrong N htangent p q horder i).toLp _) := by
  exact isWeakGradient_of_contDiffOn (isOpen_smoothDirichletHalfBox a b)
    (dirichletMixedDerivative_contDiffOn (isOpen_smoothDirichletHalfBox a b) hu p q)
    (dirichlet_mixed_derivative_memLp_of_tangential_data hf hu hG hstrong
      N htangent p q (by omega))
    (dirichlet_mixed_derivative_gradient_memLp_of_tangential_data
      hf hu hG hstrong N htangent p q horder)

theorem exists_dirichlet_mixed_derivative_h1_of_tangential_data {a b : ℝ}
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {u G : ℂ → ℂ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox a b))
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hstrong : ∀ z ∈ smoothDirichletHalfBox a b,
      dirichletFlattenedDivergence f u z = -G z) (N : ℕ)
    (htangent : ∀ j ≤ N,
      MemLp (dirichletTangentialDerivative j u) 2
        (volume.restrict (smoothDirichletHalfBox a b)) ∧
      MemLp (dirD (dirichletTangentialDerivative j u) Complex.I) 2
        (volume.restrict (smoothDirichletHalfBox a b)))
    (p q : ℕ) (horder : p + q + 1 ≤ N) :
    ∃ v : NeumannH1 (smoothDirichletHalfBox a b),
      (h1Value _ v : ℂ → ℂ) =ᵐ[volume.restrict (smoothDirichletHalfBox a b)]
        dirichletMixedDerivative p q u ∧
      ∀ i : Fin 2, (h1Gradient _ i v : ℂ → ℂ)
        =ᵐ[volume.restrict (smoothDirichletHalfBox a b)]
          fun z => fderiv ℝ (dirichletMixedDerivative p q u) z (coordDir i) := by
  have hw := dirichlet_mixed_derivative_isWeakGradient hf hu hG hstrong
    N htangent p q horder
  refine ⟨h1Vector hw, ?_, ?_⟩
  · rw [h1Value_h1Vector]
    exact (dirichlet_mixed_derivative_memLp_of_tangential_data hf hu hG hstrong
      N htangent p q (by omega)).coeFn_toLp
  · intro i
    rw [h1Gradient_h1Vector]
    exact (dirichlet_mixed_derivative_gradient_memLp_of_tangential_data
      hf hu hG hstrong N htangent p q horder i).coeFn_toLp

/-- This composition uses the actual tangential energy theorem, rather
than leaving tangential high-order regularity as a final premise. -/
theorem exists_dirichlet_halfBox_mixed_derivative_memLp
    {A b : ℝ} (hA : 0 < A) (hb : 0 < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : NNReal} (hLip : LipschitzWith K f)
    {u G : ℂ → ℂ} (hc : ContinuousOn u (smoothDirichletClosedHalfBox A b))
    (hs : ContDiffOn ℝ (⊤ : ℕ∞) u (smoothDirichletHalfBox A b))
    (hz : ∀ x : ℝ, |x| < A → u (x : ℂ) = 0)
    (hm : MemLp u 2 (volume.restrict (smoothDirichletHalfBox A b)))
    (hg : ∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2
      (volume.restrict (smoothDirichletHalfBox A b)))
    (hstrong : ∀ z ∈ smoothDirichletHalfBox A b,
      dirichletFlattenedDivergence f u z = -G z)
    (hGs : ContDiff ℝ (⊤ : ℕ∞) G) (N : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
      ∀ p q : ℕ, p + q ≤ N → MemLp (dirichletMixedDerivative p q u) 2
        (volume.restrict (smoothDirichletHalfBox ρ ρ)) := by
  obtain ⟨ρ, hρ, hρA, hρb, htangent⟩ :=
    exists_dirichlet_halfBox_higher_tangential_memLp hA hb hf hLip hc hs hz hm hg hstrong hGs N
  have hWU : smoothDirichletHalfBox ρ ρ ⊆ smoothDirichletHalfBox A b := fun z hz' =>
    ⟨hz'.1.trans (by linarith), hz'.2.1, hz'.2.2.trans hρb⟩
  refine ⟨ρ, hρ, hρA, hρb, ?_⟩
  exact dirichlet_mixed_derivative_memLp_of_tangential_data hf (hs.mono hWU) hGs
    (fun z hz' => hstrong z (hWU hz')) N htangent

/-- One genuine original datum, graph chart and actual remainder work
for every finite order. The radius is allowed to depend on the order;
no all-order fixed-radius assertion or boundary derivative is assumed. -/
theorem exists_riemannMapping_flattened_all_mixed_orders {Ω : Set ℂ}
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
       MemLp u 2 (volume.restrict U) ∧
       (∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2 (volume.restrict U)) ∧
       ∀ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
         ∀ j q : ℕ, j + q ≤ N → MemLp (dirichletMixedDerivative j q u) 2
           (volume.restrict (smoothDirichletHalfBox ρ ρ))) := by
  obtain ⟨d, c, hc, f, hf, K, A, b, hc₁, hLip, hf₀, hA, hb₀,
    hmap, hu, hs, hz, hvm, hvg, htangent⟩ :=
    exists_riemannMapping_flattened_all_tangential_orders hb hS hsc F hF hinj himage hp
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let u := riemannMappingDirichletRemainder F d ∘ Ψ
  let G := lap (d : ℂ → ℂ) ∘ Ψ
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G :=
    d.property.lap.1.comp (smoothDirichletGraphChart_contDiff p c hc hf)
  have hstrong : ∀ z ∈ smoothDirichletHalfBox A b,
      dirichletFlattenedDivergence f u z = -G z :=
    riemannMapping_flattened_dirichlet_strong_equation hb hS hsc F hF hinj himage d
      p c hc hc₁ hf hmap
  refine ⟨d, c, hc, f, hf, K, A, b, hc₁, hLip, hf₀, hA, hb₀,
    hmap, hu, hs, hz, hvm, hvg, ?_⟩
  intro N
  obtain ⟨ρ, hρ, hρA, hρb, ht⟩ := htangent N
  have hWU : smoothDirichletHalfBox ρ ρ ⊆ smoothDirichletHalfBox A b := fun z hz' =>
    ⟨hz'.1.trans (by linarith), hz'.2.1, hz'.2.2.trans hρb⟩
  refine ⟨ρ, hρ, hρA, hρb, ?_⟩
  exact dirichlet_mixed_derivative_memLp_of_tangential_data hf (hs.mono hWU) hGs
    (fun z hz' => hstrong z (hWU hz')) N ht

end PolyaNeumann
end
