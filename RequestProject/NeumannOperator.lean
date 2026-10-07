module

public import RequestProject.NeumannSobolev
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The actual Neumann operator and its shifted resolvent

The inverse of the Hilbert form `q + ⟨·,·⟩` is constructed by the
adjoint of the genuine H¹ inclusion. This gives a single-valued, densely
defined Neumann operator, with exactly the weak equation already used in
the eigenspace definitions.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace PolyaNeumann

/-- The shifted form resolvent: `K = (A_N + I)⁻¹ = J J†`. -/
def neumannResolvent (Ω : Set ℂ) : L2 Ω →L[ℂ] L2 Ω :=
  (h1Value Ω).comp (ContinuousLinearMap.adjoint (h1Value Ω))

@[simp] theorem neumannResolvent_apply (Ω : Set ℂ) (f : L2 Ω) :
    neumannResolvent Ω f = h1Value Ω (ContinuousLinearMap.adjoint (h1Value Ω) f) := rfl

theorem neumannResolvent_inner (Ω : Set ℂ) (f g : L2 Ω) :
    ⟪neumannResolvent Ω f, g⟫_ℂ =
      ⟪ContinuousLinearMap.adjoint (h1Value Ω) f,
        ContinuousLinearMap.adjoint (h1Value Ω) g⟫_ℂ :=
  (ContinuousLinearMap.adjoint_inner_right (h1Value Ω)
    (ContinuousLinearMap.adjoint (h1Value Ω) f) g).symm

theorem neumannResolvent_isPositive (Ω : Set ℂ) : (neumannResolvent Ω).IsPositive :=
  ContinuousLinearMap.isPositive_self_comp_adjoint (h1Value Ω)

theorem neumannResolvent_isSelfAdjoint (Ω : Set ℂ) : IsSelfAdjoint (neumannResolvent Ω) :=
  (neumannResolvent_isPositive Ω).isSelfAdjoint

theorem neumannResolvent_compact {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) : IsCompactOperator (neumannResolvent Ω) :=
  (h1Value_isCompactOperator hb hL).comp_clm (ContinuousLinearMap.adjoint (h1Value Ω))

theorem neumannResolvent_symmetric (Ω : Set ℂ) (f g : L2 Ω) :
    ⟪neumannResolvent Ω f, g⟫_ℂ = ⟪f, neumannResolvent Ω g⟫_ℂ :=
  (neumannResolvent_isPositive Ω).isSymmetric f g

theorem h1Value_adjoint_eq_zero_iff {Ω : Set ℂ} (hΩ : IsOpen Ω) (f : L2 Ω) :
    ContinuousLinearMap.adjoint (h1Value Ω) f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    apply eq_zero_of_inner_h1 hΩ f
    intro u
    rw [← ContinuousLinearMap.adjoint_inner_right (h1Value Ω) u f, hf, inner_zero_right]
  · rintro rfl
    exact map_zero _

theorem neumannResolvent_injective {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    Function.Injective (neumannResolvent Ω) := by
  change Function.Injective (neumannResolvent Ω).toLinearMap
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  change neumannResolvent Ω f = 0 at hf
  have ha : ContinuousLinearMap.adjoint (h1Value Ω) f = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [← neumannResolvent_inner Ω f f, hf, inner_zero_left]
  exact (h1Value_adjoint_eq_zero_iff hΩ f).mp ha

theorem neumannResolvent_strictPositive {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (f : L2 Ω) (hf : f ≠ 0) : 0 < (⟪neumannResolvent Ω f, f⟫_ℂ).re := by
  rw [neumannResolvent_inner]
  have ha : ContinuousLinearMap.adjoint (h1Value Ω) f ≠ 0 := by
    intro h
    exact hf ((h1Value_adjoint_eq_zero_iff hΩ f).mp h)
  exact (re_inner_self_pos (𝕜 := ℂ)).mpr ha

theorem neumannResolvent_denseRange {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    DenseRange (neumannResolvent Ω) := by
  change Dense ((neumannResolvent Ω).range : Set (L2 Ω))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, ContinuousLinearMap.orthogonal_range]
  have hs : ContinuousLinearMap.adjoint (neumannResolvent Ω) = neumannResolvent Ω :=
    (neumannResolvent_isPositive Ω).isSymmetric.clm_adjoint_eq
  rw [hs]
  exact LinearMap.ker_eq_bot.mpr (neumannResolvent_injective hΩ)

def neumannPartialResolvent (Ω : Set ℂ) : L2 Ω →ₗ.[ℂ] L2 Ω :=
  (neumannResolvent Ω).toLinearMap.toPMap ⊤

/-- The inverse shifted operator, before subtracting the identity. -/
def neumannShiftedOperator (Ω : Set ℂ) : L2 Ω →ₗ.[ℂ] L2 Ω :=
  (neumannPartialResolvent Ω).inverse

theorem neumannShiftedOperator_domain (Ω : Set ℂ) :
    (neumannShiftedOperator Ω).domain = (neumannResolvent Ω).range := by
  rw [neumannShiftedOperator, LinearPMap.inverse_domain]
  ext f
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨(v : L2 Ω), hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨⟨v, Submodule.mem_top⟩, hv⟩

def neumannShiftedVector (Ω : Set ℂ) (f : L2 Ω) : (neumannShiftedOperator Ω).domain :=
  ⟨neumannResolvent Ω f, by rw [neumannShiftedOperator_domain]; exact ⟨f, rfl⟩⟩

@[simp] theorem neumannShiftedVector_coe (Ω : Set ℂ) (f : L2 Ω) :
    (neumannShiftedVector Ω f : L2 Ω) = neumannResolvent Ω f := rfl

theorem neumannShiftedOperator_apply_vector {Ω : Set ℂ} (hΩ : IsOpen Ω) (f : L2 Ω) :
    neumannShiftedOperator Ω (neumannShiftedVector Ω f) = f := by
  have hker : (neumannPartialResolvent Ω).ker = ⊥ := by
    rw [LinearPMap.ker_eq_bot']
    intro u hu
    apply Subtype.ext
    exact (neumannResolvent_injective hΩ).eq_iff.mp
      (by rw [ZeroMemClass.coe_zero, map_zero]; exact hu)
  exact LinearPMap.inverse_apply_eq hker (x := ⟨f, Submodule.mem_top⟩) rfl

theorem neumannResolvent_shiftedOperator {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (u : (neumannShiftedOperator Ω).domain) :
    neumannResolvent Ω (neumannShiftedOperator Ω u) = (u : L2 Ω) := by
  obtain ⟨f, hf⟩ : ∃ f, neumannResolvent Ω f = (u : L2 Ω) := by
    have hu : (u : L2 Ω) ∈ (neumannResolvent Ω).range := by
      simpa only [neumannShiftedOperator_domain] using u.property
    exact hu
  have hu : u = neumannShiftedVector Ω f := Subtype.ext hf.symm
  rw [hu, neumannShiftedOperator_apply_vector hΩ]
  rfl

theorem neumannShiftedOperator_form_representation {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (u : NeumannH1 Ω) (f : L2 Ω) :
    (∃ hu : h1Value Ω u ∈ (neumannShiftedOperator Ω).domain,
      neumannShiftedOperator Ω ⟨h1Value Ω u, hu⟩ = f) ↔
      ∀ v : NeumannH1 Ω, ⟪v, u⟫_ℂ = ⟪h1Value Ω v, f⟫_ℂ := by
  constructor
  · rintro ⟨hu, huf⟩
    have hJu := neumannResolvent_shiftedOperator hΩ ⟨h1Value Ω u, hu⟩
    rw [huf] at hJu
    have huadj : u = ContinuousLinearMap.adjoint (h1Value Ω) f :=
      h1Value_injective hΩ hJu.symm
    intro v
    rw [huadj]
    exact ContinuousLinearMap.adjoint_inner_right (h1Value Ω) v f
  · intro huf
    have huadj : u = ContinuousLinearMap.adjoint (h1Value Ω) f := by
      apply ext_inner_left ℂ
      intro v
      exact (huf v).trans (ContinuousLinearMap.adjoint_inner_right (h1Value Ω) v f).symm
    have hJu : h1Value Ω u = neumannResolvent Ω f := by rw [huadj]; rfl
    have hm : h1Value Ω u ∈ (neumannShiftedOperator Ω).domain := by
      rw [neumannShiftedOperator_domain]
      exact ⟨f, hJu.symm⟩
    refine ⟨hm, ?_⟩
    have hu : (⟨h1Value Ω u, hm⟩ : (neumannShiftedOperator Ω).domain) =
        neumannShiftedVector Ω f := Subtype.ext hJu
    rw [hu]
    exact neumannShiftedOperator_apply_vector hΩ f

/-- The Neumann Laplacian itself, obtained by subtracting the shift. -/
def neumannOperator (Ω : Set ℂ) : L2 Ω →ₗ.[ℂ] L2 Ω where
  domain := (neumannShiftedOperator Ω).domain
  toFun := (neumannShiftedOperator Ω).toFun - (neumannShiftedOperator Ω).domain.subtype

@[simp] theorem neumannOperator_domain (Ω : Set ℂ) :
    (neumannOperator Ω).domain = (neumannResolvent Ω).range :=
  neumannShiftedOperator_domain Ω

@[simp] theorem neumannOperator_apply (Ω : Set ℂ) (u : (neumannOperator Ω).domain) :
    neumannOperator Ω u = neumannShiftedOperator Ω u - (u : L2 Ω) := rfl

theorem neumannOperator_dense_domain {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    Dense ((neumannOperator Ω).domain : Set (L2 Ω)) := by
  rw [neumannOperator_domain]
  exact neumannResolvent_denseRange hΩ

/-- Representation by the actual gradient form, with no spectral assumptions. -/
theorem neumannOperator_form_representation {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (u : NeumannH1 Ω) (f : L2 Ω) :
    (∃ hu : h1Value Ω u ∈ (neumannOperator Ω).domain,
      neumannOperator Ω ⟨h1Value Ω u, hu⟩ = f) ↔
      ∀ v : NeumannH1 Ω,
        ∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ = ⟪h1Value Ω v, f⟫_ℂ := by
  have hshift := neumannShiftedOperator_form_representation hΩ u (f + h1Value Ω u)
  have hl : (∃ hu : h1Value Ω u ∈ (neumannOperator Ω).domain,
      neumannOperator Ω ⟨h1Value Ω u, hu⟩ = f) ↔
      (∃ hu : h1Value Ω u ∈ (neumannShiftedOperator Ω).domain,
        neumannShiftedOperator Ω ⟨h1Value Ω u, hu⟩ = f + h1Value Ω u) := by
    change (∃ hu : h1Value Ω u ∈ (neumannShiftedOperator Ω).domain,
      neumannShiftedOperator Ω ⟨h1Value Ω u, hu⟩ - h1Value Ω u = f) ↔ _
    simp only [sub_eq_iff_eq_add]
  rw [hl, hshift]
  apply forall_congr'
  intro v
  rw [h1_inner, inner_add_right, add_comm (inner ℂ (h1Value Ω v) f), add_left_cancel_iff]

theorem neumannOperator_mem_H1 {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (u : (neumannOperator Ω).domain) : (u : L2 Ω) ∈ H1 Ω := by
  rw [← h1Value_range]
  refine ⟨ContinuousLinearMap.adjoint (h1Value Ω) (neumannShiftedOperator Ω u), ?_⟩
  exact neumannResolvent_shiftedOperator hΩ u

/-- The operator graph agrees with the genuine weak Neumann equation. -/
theorem neumannOperator_weak_representation {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (u f : L2 Ω) :
    (∃ hu : u ∈ (neumannOperator Ω).domain, neumannOperator Ω ⟨u, hu⟩ = f) ↔
      ∃ g, IsWeakGradient Ω u g ∧ ∀ v h, IsWeakGradient Ω v h →
        ∑ i, ⟪h i, g i⟫_ℂ = ⟪v, f⟫_ℂ := by
  constructor
  · rintro ⟨hu, huf⟩
    obtain ⟨g, hg⟩ := neumannOperator_mem_H1 hΩ ⟨u, hu⟩
    refine ⟨g, hg, fun v h hv => ?_⟩
    have h := (neumannOperator_form_representation hΩ (h1Vector hg) f).mp ⟨hu, huf⟩
    simpa using h (h1Vector hv)
  · rintro ⟨g, hg, hw⟩
    apply (neumannOperator_form_representation hΩ (h1Vector hg) f).mpr
    intro v
    exact hw _ _ (h1Value_weakGradient Ω v)

/-- The partial operator is single-valued even at the level of the weak equation. -/
theorem neumannOperator_weak_rhs_unique {Ω : Set ℂ} (hΩ : IsOpen Ω) {u f f' : L2 Ω}
    (hf : ∃ g, IsWeakGradient Ω u g ∧ ∀ v h, IsWeakGradient Ω v h →
      ∑ i, ⟪h i, g i⟫_ℂ = ⟪v, f⟫_ℂ)
    (hf' : ∃ g, IsWeakGradient Ω u g ∧ ∀ v h, IsWeakGradient Ω v h →
      ∑ i, ⟪h i, g i⟫_ℂ = ⟪v, f'⟫_ℂ) : f = f' := by
  obtain ⟨hu, huf⟩ := (neumannOperator_weak_representation hΩ u f).mpr hf
  obtain ⟨hu', huf'⟩ := (neumannOperator_weak_representation hΩ u f').mpr hf'
  exact huf.symm.trans huf'

/-- Operator eigenvectors, viewed in the ambient L² space. -/
def neumannOperatorEigenspace (Ω : Set ℂ) (E : ℝ) : Submodule ℂ (L2 Ω) :=
  ((neumannOperator Ω).toFun - (E : ℂ) • (neumannOperator Ω).domain.subtype).ker.map
    (neumannOperator Ω).domain.subtype

theorem mem_neumannOperatorEigenspace_iff (Ω : Set ℂ) (E : ℝ) (u : L2 Ω) :
    u ∈ neumannOperatorEigenspace Ω E ↔
      ∃ hu : u ∈ (neumannOperator Ω).domain,
        neumannOperator Ω ⟨u, hu⟩ = (E : ℂ) • u := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.property, ?_⟩
    have h := LinearMap.mem_ker.mp hv
    change neumannOperator Ω v - (E : ℂ) • (v : L2 Ω) = 0 at h
    exact sub_eq_zero.mp h
  · rintro ⟨hu, hAu⟩
    refine ⟨⟨u, hu⟩, ?_, rfl⟩
    apply LinearMap.mem_ker.mpr
    change neumannOperator Ω ⟨u, hu⟩ - (E : ℂ) • u = 0
    exact sub_eq_zero.mpr hAu

/-- Exact identification, including the zero eigenvalue and multiplicities. -/
theorem neumannOperatorEigenspace_eq {Ω : Set ℂ} (hΩ : IsOpen Ω) (E : ℝ) :
    neumannOperatorEigenspace Ω E = neumannEigenspace Ω E := by
  ext u
  rw [mem_neumannOperatorEigenspace_iff, neumannOperator_weak_representation hΩ]
  simp only [inner_smul_right]
  rfl

theorem neumannOperator_nonneg {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (u : (neumannOperator Ω).domain) :
    0 ≤ (⟪(u : L2 Ω), neumannOperator Ω u⟫_ℂ).re := by
  obtain ⟨g, hg, hw⟩ := (neumannOperator_weak_representation hΩ (u : L2 Ω)
    (neumannOperator Ω u)).mp ⟨u.property, rfl⟩
  have h := congrArg Complex.re (hw (u : L2 Ω) g hg)
  rw [Complex.re_sum] at h
  rw [← h]
  exact Finset.sum_nonneg fun i _ => inner_self_nonneg (𝕜 := ℂ)

/-- The weak equation forces every genuine complex eigenvalue to be real and nonnegative. -/
theorem neumannOperator_eigenvalue_real_nonneg {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {c : ℂ} (u : (neumannOperator Ω).domain) (hu0 : (u : L2 Ω) ≠ 0)
    (hAu : neumannOperator Ω u = c • (u : L2 Ω)) :
    c = (c.re : ℂ) ∧ 0 ≤ c.re := by
  have hnorm : 0 < ‖(u : L2 Ω)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu0)
  obtain ⟨g, hg, hw⟩ := (neumannOperator_weak_representation hΩ (u : L2 Ω)
    (neumannOperator Ω u)).mp ⟨u.property, rfl⟩
  have hself := hw (u : L2 Ω) g hg
  rw [hAu, inner_smul_right] at hself
  simp only [inner_self_eq_norm_sq_to_K] at hself
  have hi := congrArg Complex.im hself
  simp [pow_two, Complex.mul_im, Complex.mul_re] at hi
  have him : c.im = 0 := hi.resolve_right (fun h => hu0 (congrArg Subtype.val h))
  have hpos := neumannOperator_nonneg hΩ u
  rw [hAu, inner_smul_right, inner_self_eq_norm_sq_to_K] at hpos
  simp [pow_two, Complex.mul_re] at hpos
  have hpos' : 0 ≤ c.re * ‖(u : L2 Ω)‖ ^ 2 := by
    simpa only [pow_two] using hpos
  refine ⟨?_, nonneg_of_mul_nonneg_left hpos' hnorm⟩
  apply Complex.ext
  · simp
  · simpa using him

theorem neumannShiftedOperator_symmetric {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (u v : (neumannShiftedOperator Ω).domain) :
    ⟪neumannShiftedOperator Ω u, (v : L2 Ω)⟫_ℂ =
      ⟪(u : L2 Ω), neumannShiftedOperator Ω v⟫_ℂ := by
  calc
    ⟪neumannShiftedOperator Ω u, (v : L2 Ω)⟫_ℂ =
        ⟪neumannShiftedOperator Ω u, neumannResolvent Ω (neumannShiftedOperator Ω v)⟫_ℂ := by
      rw [neumannResolvent_shiftedOperator hΩ]
    _ = ⟪neumannResolvent Ω (neumannShiftedOperator Ω u), neumannShiftedOperator Ω v⟫_ℂ :=
      (neumannResolvent_symmetric Ω _ _).symm
    _ = _ := by rw [neumannResolvent_shiftedOperator hΩ]

theorem neumannOperator_formalAdjoint {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    (neumannOperator Ω).IsFormalAdjoint (neumannOperator Ω) := by
  intro u v
  simp only [neumannOperator_apply, inner_sub_left, inner_sub_right]
  exact congrArg (· - _) (neumannShiftedOperator_symmetric hΩ u v)

def neumannOperatorVector (Ω : Set ℂ) (f : L2 Ω) : (neumannOperator Ω).domain :=
  neumannShiftedVector Ω f

@[simp] theorem neumannOperatorVector_coe (Ω : Set ℂ) (f : L2 Ω) :
    (neumannOperatorVector Ω f : L2 Ω) = neumannResolvent Ω f := rfl

theorem neumannOperator_apply_vector {Ω : Set ℂ} (hΩ : IsOpen Ω) (f : L2 Ω) :
    neumannOperator Ω (neumannOperatorVector Ω f) = f - neumannResolvent Ω f := by
  rw [neumannOperator_apply]
  exact congrArg (fun x => x - neumannResolvent Ω f)
    (neumannShiftedOperator_apply_vector hΩ f)

/-- One direction of the resolvent identity, on the genuine operator domain. -/
theorem neumannResolvent_operator {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (u : (neumannOperator Ω).domain) :
    neumannResolvent Ω (neumannOperator Ω u + (u : L2 Ω)) = (u : L2 Ω) := by
  rw [neumannOperator_apply, sub_add_cancel]
  exact neumannResolvent_shiftedOperator hΩ u

theorem neumannResolvent_adjointOperator {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (u : (neumannOperator Ω).adjoint.domain) :
    neumannResolvent Ω ((neumannOperator Ω).adjoint u + (u : L2 Ω)) = (u : L2 Ω) := by
  apply ext_inner_right ℂ
  intro f
  rw [neumannResolvent_symmetric, inner_add_left]
  have h := LinearPMap.adjoint_isFormalAdjoint
    (hT := neumannOperator_dense_domain hΩ) u (neumannOperatorVector Ω f)
  change ⟪(neumannOperator Ω).adjoint u, neumannResolvent Ω f⟫_ℂ =
    ⟪(u : L2 Ω), neumannOperator Ω (neumannOperatorVector Ω f)⟫_ℂ at h
  rw [h, neumannOperator_apply_vector hΩ, inner_sub_right]
  exact sub_add_cancel _ _

/-- Self-adjointness is proved from the resolvent, rather than assumed. -/
theorem neumannOperator_selfAdjoint {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    IsSelfAdjoint (neumannOperator Ω) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro f hf
      rw [neumannOperator_domain]
      exact ⟨(neumannOperator Ω).adjoint ⟨f, hf⟩ + f,
        neumannResolvent_adjointOperator hΩ ⟨f, hf⟩⟩
    · intro u v huv
      have hsum : (neumannOperator Ω).adjoint u + (u : L2 Ω) =
          neumannOperator Ω v + (v : L2 Ω) := by
        apply neumannResolvent_injective hΩ
        rw [neumannResolvent_adjointOperator hΩ, neumannResolvent_operator hΩ]
        exact huv
      rw [huv] at hsum
      exact add_right_cancel hsum
  · exact LinearPMap.IsFormalAdjoint.le_adjoint
      (hT := neumannOperator_dense_domain hΩ) (neumannOperator_formalAdjoint hΩ)

theorem neumannOperator_closed {Ω : Set ℂ} (hΩ : IsOpen Ω) :
    (neumannOperator Ω).IsClosed := (neumannOperator_selfAdjoint hΩ).isClosed

/-- The inverse spectral parameter is proved from both resolvent identities. -/
theorem neumannOperator_eigen_iff_resolvent {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (c : ℂ) (hc : c + 1 ≠ 0) (u : L2 Ω) :
    (∃ hu : u ∈ (neumannOperator Ω).domain,
      neumannOperator Ω ⟨u, hu⟩ = c • u) ↔
      neumannResolvent Ω u = (c + 1)⁻¹ • u := by
  constructor
  · rintro ⟨hu, hAu⟩
    have h := neumannResolvent_operator hΩ ⟨u, hu⟩
    have heq : c • u + u = (c + 1) • u := by rw [add_smul, one_smul]
    rw [hAu, heq, map_smul] at h
    calc
      neumannResolvent Ω u = (c + 1)⁻¹ • ((c + 1) • neumannResolvent Ω u) := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = (c + 1)⁻¹ • u := congrArg ((c + 1)⁻¹ • ·) h
  · intro hK
    have hKu : neumannResolvent Ω ((c + 1) • u) = u := by
      rw [map_smul, hK, smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hm : u ∈ (neumannOperator Ω).domain := by
      rw [neumannOperator_domain]
      exact ⟨(c + 1) • u, hKu⟩
    refine ⟨hm, ?_⟩
    have huv : (⟨u, hm⟩ : (neumannOperator Ω).domain) =
        neumannOperatorVector Ω ((c + 1) • u) := Subtype.ext hKu.symm
    rw [huv, neumannOperator_apply_vector hΩ, hKu, add_smul, one_smul, add_sub_cancel_right]

theorem neumannOperatorEigenspace_eq_resolvent {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (E : ℝ) (hE : E + 1 ≠ 0) :
    neumannOperatorEigenspace Ω E =
      Module.End.eigenspace (neumannResolvent Ω).toLinearMap ((E + 1 : ℝ)⁻¹ : ℂ) := by
  ext u
  rw [mem_neumannOperatorEigenspace_iff,
    neumannOperator_eigen_iff_resolvent hΩ (E : ℂ) (by exact_mod_cast hE),
    Module.End.mem_eigenspace_iff]
  norm_cast

theorem neumannEigenspace_eq_resolvent {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (E : ℝ) (hE : E + 1 ≠ 0) :
    neumannEigenspace Ω E =
      Module.End.eigenspace (neumannResolvent Ω).toLinearMap ((E + 1 : ℝ)⁻¹ : ℂ) := by
  rw [← neumannOperatorEigenspace_eq hΩ E]
  exact neumannOperatorEigenspace_eq_resolvent hΩ E hE

/-- Constants belong to the actual operator domain and have zero Neumann Laplacian. -/
theorem neumannOperator_const {Ω : Set ℂ} (hΩ : IsOpen Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (c : ℂ) :
    ∃ hu : Lp.const 2 (volume.restrict Ω) c ∈ (neumannOperator Ω).domain,
      neumannOperator Ω ⟨Lp.const 2 (volume.restrict Ω) c, hu⟩ = 0 := by
  apply (neumannOperator_weak_representation hΩ _ _).mpr
  refine ⟨0, isWeakGradient_const Ω c, fun v h hv => ?_⟩
  simp

theorem neumannResolvent_const {Ω : Set ℂ} (hΩ : IsOpen Ω)
    [IsFiniteMeasure (volume.restrict Ω)] (c : ℂ) :
    neumannResolvent Ω (Lp.const 2 (volume.restrict Ω) c) =
      Lp.const 2 (volume.restrict Ω) c := by
  have h := (neumannOperator_eigen_iff_resolvent hΩ 0 (by simp)
    (Lp.const 2 (volume.restrict Ω) c)).mp (by simpa using neumannOperator_const hΩ c)
  simpa using h

end PolyaNeumann

end
