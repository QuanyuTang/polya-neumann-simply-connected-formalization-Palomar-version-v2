module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Tactic
public import RequestProject.Defs

/-!
# Compact smooth representatives on an arbitrary open neighborhood

A function smooth on a neighborhood of a compact set has a global smooth,
compactly supported representative equal to it on a neighborhood of that
set. The neighborhood need not be a disk or star shaped. This allows local
inverse conformal coordinates to supply genuine physical test functions.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set Filter
open scoped Topology

theorem exists_smooth_compact_cutoff {K U : Set ℂ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ ∀ x ∈ K, χ =ᶠ[𝓝 x] (fun _ => 1) := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨M, hM, hLM, hMU⟩ := exists_compact_between hL hU hLU
  obtain ⟨f, hfSupp, hf, hfRange⟩ :=
    (isOpen_interior (s := M)).exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  obtain ⟨g, hgSupp, hg, hgRange⟩ :=
    hL.isClosed.isOpen_compl.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  have hf0 (x : ℂ) : 0 ≤ f x := (hfRange (mem_range_self x)).1
  have hg0 (x : ℂ) : 0 ≤ g x := (hgRange (mem_range_self x)).1
  have hden (x : ℂ) : 0 < f x + g x := by
    by_cases hx : x ∈ L
    · have hfx : f x ≠ 0 := by
        rw [← Function.mem_support, hfSupp]
        exact hLM hx
      have := lt_of_le_of_ne (hf0 x) hfx.symm
      linarith [hg0 x]
    · have hgx : g x ≠ 0 := by
        rw [← Function.mem_support, hgSupp]
        exact hx
      have := lt_of_le_of_ne (hg0 x) hgx.symm
      linarith [hf0 x]
  let χ : ℂ → ℝ := fun x => f x / (f x + g x)
  have hχSupp : Function.support χ = interior M := by
    have hsum : Function.support (fun x => f x + g x) = univ :=
      eq_univ_of_forall (fun x => (hden x).ne')
    simp only [χ, Function.support_div, hfSupp, hsum, inter_univ]
  have hχts : tsupport χ ⊆ M := by
    rw [tsupport, hχSupp]
    exact hM.isClosed.closure_subset_iff.mpr interior_subset
  refine ⟨χ, hf.div (hf.add hg) (fun x => (hden x).ne'),
    hM.of_isClosed_subset isClosed_closure hχts, hχts.trans hMU, ?_⟩
  intro x hx
  filter_upwards [isOpen_interior.mem_nhds (hKL hx)] with y hy
  have hgy : g y = 0 := by
    rw [← Function.notMem_support, hgSupp]
    exact not_not.mpr (interior_subset hy)
  dsimp [χ]
  rw [hgy, add_zero, div_self]
  have hfy := hden y
  rw [hgy, add_zero] at hfy
  exact hfy.ne'

theorem exists_smooth_compact_extension {K U : Set ℂ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {φ : ℂ → ℂ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U) :
    ∃ f : ℂ → ℂ, TestFunction univ f ∧ ∀ x ∈ K, f =ᶠ[𝓝 x] φ := by
  obtain ⟨χ, hχ, hχc, hχU, hχone⟩ := exists_smooth_compact_cutoff hK hU hKU
  let f : ℂ → ℂ := fun x => (χ x : ℂ) * φ x
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact (Complex.ofRealCLM.contDiff.comp hχ).contDiffAt.mul
        (hφ.contDiffAt (hU.mem_nhds hx))
    · have hx' : x ∉ tsupport χ := fun h => hx (hχU h)
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx'] with y hy
      simp only [f, hy, Pi.zero_apply, Complex.ofReal_zero, zero_mul]
  refine ⟨f, ⟨hfs,
    (hχc.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero).mul_right,
    subset_univ _⟩, ?_⟩
  intro x hx
  filter_upwards [hχone x hx] with y hy
  simp only [f, hy, Complex.ofReal_one, one_mul]

end PolyaNeumann

end
