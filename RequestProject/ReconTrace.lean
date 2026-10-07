module

public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Analysis.Complex.Tietze
public import RequestProject.ReconBasic

/-!
# Boundary densities orthogonal to all smooth functions

If `h` is continuous on `[0, 2π]` and `∫₀^{2π} h φ(γ) γ' = 0` for every smooth compactly supported
`φ`, then `h = 0` on `[0, 2π]` (`eq_zero_of_integral_comp_mul_deriv`).

The proof approximates continuous functions uniformly by smooth ones, and represents every
continuous closed function of the parameter as `Ψ ∘ γ` (Tietze extension through the quotient
map `[0, 2π] → ∂Ω`).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ} {γ : ℝ → ℂ}

/-- A smooth real cutoff equal to `1` on a ball. -/
lemma exists_cutoff_one_on_ball (R : ℝ) (hR : 0 < R) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ ∀ z ∈ closedBall (0 : ℂ) R, χ z = 1 := by
  let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR, by linarith⟩
  exact ⟨b, b.contDiff, b.hasCompactSupport, fun z hz => b.one_of_mem_closedBall hz⟩

lemma intervalIntegrable_mul_comp_mul_deriv {K : NNReal} (hK : LipschitzWith K γ) {h : ℝ → ℂ}
    (hh : ContinuousOn h (Icc 0 (2 * π))) {F : ℂ → ℂ} (hF : Continuous F) :
    IntervalIntegrable (fun θ => h θ * F (γ θ) * deriv γ θ) volume 0 (2 * π) := by
  have hd : IntervalIntegrable (deriv γ) volume 0 (2 * π) := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mpr ?_
    exact Measure.integrableOn_of_bounded (M := K) measure_Ioc_lt_top.ne
      (measurable_deriv γ).aestronglyMeasurable
      (Eventually.of_forall fun θ => norm_deriv_le_of_lipschitz hK)
  refine hd.continuousOn_mul ?_
  rw [uIcc_of_le (by positivity)]
  exact hh.mul (hF.comp hK.continuous).continuousOn

/-- Orthogonality to smooth functions extends to continuous compactly supported functions. -/
lemma integral_comp_mul_deriv_eq_zero_of_continuous {K : NNReal} (hK : LipschitzWith K γ)
    {h : ℝ → ℂ} (hh : ContinuousOn h (Icc 0 (2 * π)))
    (horth : ∀ φ : ℂ → ℂ, TestFunction univ φ →
      ∫ θ in (0 : ℝ)..(2 * π), h θ * φ (γ θ) * deriv γ θ = 0)
    {Ψ : ℂ → ℂ} (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    ∫ θ in (0 : ℝ)..(2 * π), h θ * Ψ (γ θ) * deriv γ θ = 0 := by
  obtain ⟨Mh, hMh⟩ := isCompact_Icc.exists_bound_of_continuousOn hh
  have hMh0 : 0 ≤ Mh := (norm_nonneg _).trans (hMh 0 ⟨le_rfl, by positivity⟩)
  obtain ⟨R, hR0, hR⟩ : ∃ R, 0 < R ∧ ∀ θ ∈ Icc (0 : ℝ) (2 * π), γ θ ∈ closedBall (0 : ℂ) R := by
    obtain ⟨R, hR⟩ := (isCompact_Icc.image hK.continuous).isBounded.subset_closedBall (0 : ℂ)
    exact ⟨max R 1, by positivity, fun θ hθ =>
      closedBall_subset_closedBall (le_max_left _ _) (hR (mem_image_of_mem γ hθ))⟩
  obtain ⟨χ, hχ, hχc, hχ1⟩ := exists_cutoff_one_on_ball R hR0
  have hu := HasCompactSupport.uniformContinuous_of_continuous hΨc hΨ
  refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
  rw [zero_add]
  set C : ℝ := Mh * K * (2 * π) + 1 with hC
  have hCpos : 0 < C := by positivity
  obtain ⟨g, hg, hgΨ⟩ := hu.exists_contDiff_dist_le (div_pos hε hCpos)
  set φ : ℂ → ℂ := fun z => (χ z : ℂ) * g z with hφ
  have hφt : TestFunction univ φ := by
    refine ⟨(Complex.ofRealCLM.contDiff.comp hχ).mul (hg.of_le (by exact_mod_cast le_top)), ?_,
      subset_univ _⟩
    exact (hχc.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right
  have e := horth φ hφt
  have hφγ : ∀ θ ∈ Icc (0 : ℝ) (2 * π), φ (γ θ) = g (γ θ) := fun θ hθ => by
    simp [hφ, hχ1 _ (hR θ hθ)]
  have hiΨ := intervalIntegrable_mul_comp_mul_deriv hK hh hΨ
  have hiφ := intervalIntegrable_mul_comp_mul_deriv hK hh hφt.1.continuous
  have hdiff : ∫ θ in (0 : ℝ)..(2 * π), h θ * Ψ (γ θ) * deriv γ θ =
      ∫ θ in (0 : ℝ)..(2 * π), (h θ * Ψ (γ θ) * deriv γ θ - h θ * φ (γ θ) * deriv γ θ) := by
    rw [intervalIntegral.integral_sub hiΨ hiφ, e, sub_zero]
  rw [hdiff]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Mh * (ε / C) * K)
    fun θ hθ => ?_).trans ?_
  · rw [uIoc_of_le (by positivity)] at hθ
    have hθ' : θ ∈ Icc (0 : ℝ) (2 * π) := Ioc_subset_Icc_self hθ
    rw [← sub_mul, ← mul_sub, hφγ θ hθ', norm_mul, norm_mul]
    gcongr
    · exact hMh θ hθ'
    · rw [← dist_eq_norm, dist_comm]; exact (hgΨ _).le
    · exact norm_deriv_le_of_lipschitz hK
  · rw [sub_zero, abs_of_pos (by positivity)]
    calc Mh * (ε / C) * K * (2 * π) = ε * (Mh * K * (2 * π) / C) := by ring
      _ ≤ ε * 1 := by
          gcongr
          rw [div_le_one hCpos, hC]; linarith
      _ = ε := mul_one ε

/-- A continuous closed function of the parameter is `Ψ ∘ γ` for a continuous compactly
supported `Ψ` on `ℂ`. -/
lemma exists_continuous_comp_eq (hγ : IsBoundaryParam Ω γ) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Icc 0 (2 * π))) (hg0 : g 0 = g (2 * π)) :
    ∃ Ψ : ℂ → ℂ, Continuous Ψ ∧ HasCompactSupport Ψ ∧ ∀ θ ∈ Icc 0 (2 * π), Ψ (γ θ) = g θ := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have h2π : (0 : ℝ) < 2 * π := by positivity
  set S : Set ℂ := γ '' Icc 0 (2 * π) with hS
  have hSc : IsCompact S := isCompact_Icc.image hK.continuous
  -- well-definedness on `S`
  have hwd : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ θ' ∈ Icc (0 : ℝ) (2 * π), γ θ = γ θ' → g θ = g θ' := by
    have hend : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
    have key : ∀ θ ∈ Icc (0 : ℝ) (2 * π), θ < 2 * π → ∀ θ' ∈ Icc (0 : ℝ) (2 * π),
        γ θ = γ θ' → g θ = g θ' := by
      intro θ hθ hlt θ' hθ' he
      rcases lt_or_eq_of_le hθ'.2 with h' | h'
      · rw [hγ.injOn ⟨hθ.1, hlt⟩ ⟨hθ'.1, h'⟩ he]
      · subst h'
        rw [hend] at he
        rw [hγ.injOn ⟨hθ.1, hlt⟩ ⟨le_rfl, h2π⟩ he, hg0]
    intro θ hθ θ' hθ' he
    rcases lt_or_eq_of_le hθ.2 with h | h
    · exact key θ hθ h θ' hθ' he
    · rcases lt_or_eq_of_le hθ'.2 with h' | h'
      · exact (key θ' hθ' h' θ hθ he.symm).symm
      · rw [h, h']
  choose! θof hθof using fun p (hp : p ∈ S) => hp
  set Ψ₀ : S → ℂ := fun p => g (θof p) with hΨ₀
  have hΨ₀q : ∀ θ (hθ : θ ∈ Icc (0 : ℝ) (2 * π)), Ψ₀ ⟨γ θ, mem_image_of_mem γ hθ⟩ = g θ := by
    intro θ hθ
    have hm : γ θ ∈ S := mem_image_of_mem γ hθ
    exact hwd _ (hθof _ hm).1 _ hθ (hθof _ hm).2
  set q : Icc (0 : ℝ) (2 * π) → S := fun θ => ⟨γ θ, mem_image_of_mem γ θ.2⟩ with hq
  have hqc : Continuous q := (hK.continuous.comp continuous_subtype_val).subtype_mk _
  have hqs : Function.Surjective q := by
    rintro ⟨p, θ, hθ, rfl⟩
    exact ⟨⟨θ, hθ⟩, rfl⟩
  have hqq : Topology.IsQuotientMap q := hqc.isClosedMap.isQuotientMap hqc hqs
  have hΨ₀c : Continuous Ψ₀ := by
    rw [hqq.continuous_iff]
    have : Ψ₀ ∘ q = fun θ : Icc (0 : ℝ) (2 * π) => g θ := funext fun θ => hΨ₀q θ θ.2
    rw [this]
    exact hg.comp_continuous continuous_subtype_val (fun θ => θ.2)
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hSc.isClosed ⟨Ψ₀, hΨ₀c⟩
  obtain ⟨R, hR0, hR⟩ : ∃ R, 0 < R ∧ S ⊆ closedBall (0 : ℂ) R := by
    obtain ⟨R, hR⟩ := hSc.isBounded.subset_closedBall (0 : ℂ)
    exact ⟨max R 1, by positivity, hR.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
  obtain ⟨χ, hχ, hχc, hχ1⟩ := exists_cutoff_one_on_ball R hR0
  refine ⟨fun z => (χ z : ℂ) * G z, (Complex.continuous_ofReal.comp hχ.continuous).mul
    G.continuous, (hχc.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right,
    fun θ hθ => ?_⟩
  have hm : γ θ ∈ S := mem_image_of_mem γ hθ
  have hGθ : G (γ θ) = Ψ₀ ⟨γ θ, hm⟩ := by
    have := congrArg (fun F : C(S, ℂ) => F ⟨γ θ, hm⟩) hG
    simpa using this
  simp only [hχ1 _ (hR hm), Complex.ofReal_one, one_mul, hGθ]
  exact hΨ₀q θ hθ

/-- A continuous boundary density orthogonal to `φ ∘ γ · γ'` for every test function `φ`
vanishes. -/
theorem eq_zero_of_integral_comp_mul_deriv (hγ : IsBoundaryParam Ω γ)
    {h : ℝ → ℂ} (hh : ContinuousOn h (Icc 0 (2 * π)))
    (horth : ∀ φ : ℂ → ℂ, TestFunction univ φ →
      ∫ θ in (0 : ℝ)..(2 * π), h θ * φ (γ θ) * deriv γ θ = 0) :
    ∀ θ ∈ Icc 0 (2 * π), h θ = 0 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨c, hc, hspeed⟩ := hγ.const_speed
  have h2π : (0 : ℝ) < 2 * π := by positivity
  -- `h γ' = 0` a.e. on `(0, 2π)`
  have hloc : LocallyIntegrableOn (fun θ => h θ * deriv γ θ) (Ioo 0 (2 * π)) volume := by
    have hi : IntegrableOn (fun θ => h θ * deriv γ θ) (Ioc 0 (2 * π)) volume := by
      have := intervalIntegrable_mul_comp_mul_deriv hK hh (F := fun _ => (1 : ℂ))
        continuous_const
      simp only [mul_one] at this
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h2π.le).mp this
    exact (hi.mono_set Ioo_subset_Ioc_self).locallyIntegrableOn
  have hae := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hg hgc hgs => by
      obtain ⟨Ψ, hΨ, hΨc, hΨγ⟩ := exists_continuous_comp_eq hγ (g := fun θ => (g θ : ℂ))
        (Complex.continuous_ofReal.comp hg.continuous).continuousOn (by
          have h0 : g 0 = 0 := image_eq_zero_of_notMem_tsupport (fun h' => (hgs h').1.false)
          have h1 : g (2 * π) = 0 :=
            image_eq_zero_of_notMem_tsupport (fun h' => (hgs h').2.false)
          simp [h0, h1])
      have e := integral_comp_mul_deriv_eq_zero_of_continuous hK hh horth hΨ hΨc
      rw [intervalIntegral.integral_of_le h2π.le] at e
      rw [← e, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc 0 (2 * π))]
      · refine setIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
        simp only [hΨγ θ (Ioc_subset_Icc_self hθ), Complex.real_smul]
        ring
      · intro θ hθ
        have : θ ∉ tsupport g := fun h' => hθ (Ioo_subset_Ioc_self (hgs h'))
        simp [image_eq_zero_of_notMem_tsupport this])
  -- `h = 0` a.e. on `(0, 2π)`
  have hae' : ∀ᵐ θ, θ ∈ Ioo 0 (2 * π) → h θ = 0 := by
    filter_upwards [hae, hspeed] with θ h1 h2 hθ
    have hne : deriv γ θ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h2; exact hc.ne h2
    exact (mul_eq_zero.mp (h1 hθ)).resolve_right hne
  -- by continuity, `h = 0` on `(0, 2π)`
  have hIoo : ∀ θ ∈ Ioo (0 : ℝ) (2 * π), h θ = 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨θ₀, hθ₀, hne⟩ := hcon
    have hopen : IsOpen (Ioo (0 : ℝ) (2 * π) ∩ h ⁻¹' {0}ᶜ) :=
      (hh.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo isOpen_compl_singleton
    have hzero : volume (Ioo (0 : ℝ) (2 * π) ∩ h ⁻¹' {0}ᶜ) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hae'] with θ hθ hmem
      exact hmem.2 (hθ hmem.1)
    have := hopen.measure_eq_zero_iff (μ := volume) |>.mp hzero
    exact (this ▸ (show θ₀ ∈ Ioo (0 : ℝ) (2 * π) ∩ h ⁻¹' {0}ᶜ from ⟨hθ₀, hne⟩) :
      θ₀ ∈ (∅ : Set ℝ))
  -- and on the closed interval
  have heq : EqOn h (fun _ => (0 : ℂ)) (Icc 0 (2 * π)) :=
    EqOn.of_subset_closure (s := Ioo 0 (2 * π)) hIoo hh continuousOn_const
      Ioo_subset_Icc_self (by rw [closure_Ioo h2π.ne])
  exact fun θ hθ => heq hθ

end PolyaNeumann
