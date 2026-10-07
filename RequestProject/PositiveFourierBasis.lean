module

public import RequestProject.LocalConformalHardySubspace
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The actual positive Fourier Hilbert basis

The orthogonal complement of the full nonpositive space has the standard
positive-frequency basis. Finite linear combinations in this basis, or
the full standard basis, have genuinely finite Fourier support.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace

theorem stdBasisZ_mem_nonpositive {n : ℤ} (hn : n ≤ 0) :
    stdBasisZ n ∈ nonpositiveFourierSubspace := by
  intro k hk
  have hkn : k ≠ n := by omega
  simp [stdBasisZ_apply, lp.single_apply, hkn]

theorem nonpositive_orthogonal_coefficient_eq_zero
    (b : nonpositiveFourierSubspaceᗮ) {n : ℤ} (hn : n ≤ 0) :
    (b : L2Z) n = 0 := by
  have h := (Submodule.mem_orthogonal _ _).mp b.property (stdBasisZ n)
    (stdBasisZ_mem_nonpositive hn)
  simpa [stdBasisZ_apply, lp.inner_single_left, RCLike.inner_apply'] using h

theorem stdBasisZ_mem_nonpositive_orthogonal {n : ℤ} (hn : 0 < n) :
    stdBasisZ n ∈ nonpositiveFourierSubspaceᗮ := by
  have heq : posProj (stdBasisZ n) = stdBasisZ n := by
    apply lp.ext
    funext k
    by_cases hkn : k = n
    · subst k
      simp [posProj, diagOp_apply, hn]
    · simp [posProj, diagOp_apply, stdBasisZ_apply, lp.single_apply, hkn]
  rw [← heq]
  exact posProj_mem_nonpositive_orthogonal _

def positiveFourierVector (n : {n : ℤ // 0 < n}) :
    nonpositiveFourierSubspaceᗮ :=
  ⟨stdBasisZ n, stdBasisZ_mem_nonpositive_orthogonal n.property⟩

theorem orthonormal_positiveFourierVector :
    Orthonormal ℂ positiveFourierVector := by
  exact (stdBasisZ.orthonormal.comp Subtype.val Subtype.val_injective).codRestrict
    nonpositiveFourierSubspaceᗮ
    (fun n => stdBasisZ_mem_nonpositive_orthogonal n.property)

theorem positiveFourierVector_span_orthogonal_eq_bot :
    (Submodule.span ℂ (range positiveFourierVector))ᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro b hb
  apply Subtype.ext
  apply lp.ext
  funext n
  change (b : L2Z) n = 0
  by_cases hn : 0 < n
  · have h := (Submodule.mem_orthogonal _ _).mp hb
      (positiveFourierVector ⟨n, hn⟩)
      (Submodule.subset_span (show positiveFourierVector ⟨n, hn⟩ ∈
        range positiveFourierVector from ⟨⟨n, hn⟩, rfl⟩))
    change ⟪stdBasisZ n, (b : L2Z)⟫_ℂ = 0 at h
    simpa [stdBasisZ_apply, lp.inner_single_left, RCLike.inner_apply'] using h
  · exact nonpositive_orthogonal_coefficient_eq_zero b (le_of_not_gt hn)

def positiveFourierHilbertBasis :
    HilbertBasis {n : ℤ // 0 < n} ℂ nonpositiveFourierSubspaceᗮ :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_positiveFourierVector
    positiveFourierVector_span_orthogonal_eq_bot

@[simp] theorem positiveFourierHilbertBasis_apply (n : {n : ℤ // 0 < n}) :
    positiveFourierHilbertBasis n = positiveFourierVector n := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    orthonormal_positiveFourierVector positiveFourierVector_span_orthogonal_eq_bot) n

/-- The linear subspace of sequences having genuinely finite support. -/
def finiteFourierSubmodule : Submodule ℂ L2Z where
  carrier := {b | (Function.support (b : ℤ → ℂ)).Finite}
  zero_mem' := Set.finite_empty.subset fun n hn => hn (by simp)
  add_mem' := by
    intro b d hb hd
    refine (hb.union hd).subset ?_
    intro n hn
    by_contra h
    have hb0 : b n = 0 := by
      by_contra hb0
      exact h (Or.inl hb0)
    have hd0 : d n = 0 := by
      by_contra hd0
      exact h (Or.inr hd0)
    exact hn (by simp [hb0, hd0])
  smul_mem' := by
    intro a b hb
    refine hb.subset ?_
    intro n hn
    by_contra hb0
    exact hn (by simp [not_not.mp hb0])

theorem stdBasisZ_mem_finiteFourierSubmodule (n : ℤ) :
    stdBasisZ n ∈ finiteFourierSubmodule := by
  refine (finite_singleton n).subset ?_
  intro k hk
  by_contra hkn
  have hkn' : k ≠ n := by simpa only [mem_singleton_iff] using hkn
  exact hk (by simp [stdBasisZ_apply, lp.single_apply, hkn'])

theorem finite_support_of_mem_span_stdBasisZ {b : L2Z}
    (hb : b ∈ Submodule.span ℂ (range stdBasisZ)) :
    (Function.support (b : ℤ → ℂ)).Finite := by
  apply (show Submodule.span ℂ (range stdBasisZ) ≤ finiteFourierSubmodule from ?_) hb
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact stdBasisZ_mem_finiteFourierSubmodule n

theorem finite_support_of_mem_span_positiveFourierHilbertBasis
    {b : nonpositiveFourierSubspaceᗮ}
    (hb : b ∈ Submodule.span ℂ (range positiveFourierHilbertBasis)) :
    (Function.support ((b : L2Z) : ℤ → ℂ)).Finite := by
  have hle : Submodule.span ℂ (range positiveFourierHilbertBasis) ≤
      finiteFourierSubmodule.comap nonpositiveFourierSubspaceᗮ.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change (positiveFourierHilbertBasis n : L2Z) ∈ finiteFourierSubmodule
    rw [positiveFourierHilbertBasis_apply]
    exact stdBasisZ_mem_finiteFourierSubmodule n
  exact hle hb

theorem isSobolevSeq_of_finite_fourier_support (s : ℝ) {b : L2Z}
    (hb : (Function.support (b : ℤ → ℂ)).Finite) :
    IsSobolevSeq s (b : ℤ → ℂ) := by
  apply summable_of_finite_support
  refine hb.subset ?_
  intro n hn
  by_contra hb0
  exact hn (by simp [not_not.mp hb0])

end PolyaNeumann

end
