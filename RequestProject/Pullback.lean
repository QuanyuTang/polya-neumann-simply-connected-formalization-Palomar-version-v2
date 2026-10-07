module

public import RequestProject.BallZarnescu
public import RequestProject.Rellich
public import RequestProject.Approximation
public import RequestProject.WeakCompact
public import RequestProject.BiLipschitz
public import RequestProject.BZCoef
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions

/-!
# Pulled-back Neumann forms for the Ball–Zarnescu approximation (Lemmas 10.9–10.13)

* `PullbackData Ω A`: the output of Lemmas 10.9 and 10.10 for a Ball–Zarnescu approximation
  `A` (`Ω_n = f_n(Ω)`): coefficient matrices `A_n` on `Ω`, uniformly bounded and uniformly
  elliptic and equal to `I` off the collars, a lower bound for the densities
  `ρ_n = |det Df_n|`, and the pullback isomorphisms `L²(Ω_n) ≅ L²(Ω)`, `w ↦ w ∘ f_n`, which
  carry the `L²(Ω_n)` inner product to the weighted inner product `∫_Ω ρ_n ⟨·, ·⟩`, preserve
  `H¹`, and carry the Neumann form of `Ω_n` to `q_n[u] = ∫_Ω ∇ū · A_n ∇u`.
* `exists_bzChainRule`, `exists_pullbackData`: the bi-Lipschitz Sobolev chain rule and change of
  variables, which produce these data.
* `exists_pullbackForms` (proved from `exists_pullbackData`): the min–max bound of Lemma 10.10,
  the uniform convergence `q_n → q_Ω` of Lemma 10.11 and the orthonormal limits of
  Lemma 10.13, by Rellich compactness, weak compactness in `L²` and weak lower semicontinuity.
-/

@[expose] public section

open scoped ComplexConjugate
open MeasureTheory Filter Topology

noncomputable section

namespace PolyaNeumann

/-- The pointwise sesquilinear density `∑_{i,k} M_{ik} ⟨ξ_i, η_k⟩` of a real `2 × 2` matrix. -/
def coefSesq (M : Matrix (Fin 2) (Fin 2) ℝ) (ξ η : Fin 2 → ℂ) : ℂ :=
  ∑ i, ∑ k, (M i k : ℂ) * inner ℂ (ξ i) (η k)

/-- The quadratic form `q_M[g] = Re ∫_Ω ∑_{i,k} M_{ik} conj(g_i) g_k` of a matrix field `M` on a
gradient `g = (g_x, g_y)`. -/
def gradForm (Ω : Set ℂ) (M : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → L2 Ω) : ℝ :=
  (∫ w in Ω, coefSesq (M w) (fun i => (g i : ℂ → ℂ) w) (fun i => (g i : ℂ → ℂ) w)).re

/-- The data produced by Lemmas 10.9 and 10.10 for a Ball–Zarnescu approximation `A`
(`Ω_n = f_n(Ω)`, `ρ_n = |det Df_n|`). In the paper `A_n = ρ_n (Df_n)⁻¹ (Df_n)⁻ᵀ`. -/
structure PullbackData (Ω : Set ℂ) (A : BallZarnescuApprox Ω) where
  /-- The coefficient matrices `A_n`. -/
  coef : ℕ → ℂ → Matrix (Fin 2) (Fin 2) ℝ
  coef_meas : ∀ n i k, AEStronglyMeasurable (fun w => coef n w i k) (volume.restrict Ω)
  /-- A uniform bound for the entries. -/
  bound : ℝ
  coef_bound : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), ∀ i k, |coef n w i k| ≤ bound
  /-- A uniform ellipticity constant, also a lower bound for the densities. -/
  ellip : ℝ
  ellip_pos : 0 < ellip
  coef_ellip : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), ∀ ξ : Fin 2 → ℂ,
    ellip * ∑ i, ‖ξ i‖ ^ 2 ≤ (coefSesq (coef n w) ξ ξ).re
  coef_eq_one : ∀ n, ∀ w ∈ Ω, w ∉ A.collar n → coef n w = 1
  density_ge : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), ellip ≤ |(fderiv ℝ (A.map n) w).det|
  /-- The pullbacks `w ↦ w ∘ f_n`. -/
  pull : ∀ n, L2 (A.map n '' Ω) ≃ₗ[ℂ] L2 Ω
  pull_inner : ∀ n (v w : L2 (A.map n '' Ω)), inner ℂ v w =
    ∫ x in Ω, ((|(fderiv ℝ (A.map n) x).det| : ℝ) : ℂ) *
      inner ℂ ((pull n v : ℂ → ℂ) x) ((pull n w : ℂ → ℂ) x)
  pull_H1 : ∀ n v, v ∈ H1 (A.map n '' Ω) ↔ pull n v ∈ H1 Ω
  pull_energy : ∀ n v (g : Fin 2 → L2 Ω), IsWeakGradient Ω (pull n v) g →
    neumannEnergy (A.map n '' Ω) v = ENNReal.ofReal (gradForm Ω (coef n) g)

/-- The chain rule and the change of variables for one bi-Lipschitz map `f`: for `v ∈ L²(f(Ω))`
and `u = v ∘ f`, `v ∈ H¹(f(Ω))` if and only if `u ∈ H¹(Ω)`, and then the Neumann energy of `v` is
the weighted gradient form of `u` with the coefficient matrix `|det Df| (Df)⁻¹ (Df)⁻ᵀ`. -/
lemma bzChainRule_of_bilip {Ω : Set ℂ} (hΩ : IsOpen Ω) {f : ℂ ≃ₜ ℂ} {K : NNReal} (hK : 0 < K)
    (hf : LipschitzOnWith K f Ω) (hg : LipschitzOnWith K f.symm (f '' Ω))
    (v : L2 (f '' Ω)) (u : L2 Ω)
    (hu : (u : ℂ → ℂ) =ᵐ[volume.restrict Ω] fun x => (v : ℂ → ℂ) (f x)) :
    (v ∈ H1 (f '' Ω) ↔ u ∈ H1 Ω) ∧
      ∀ g : Fin 2 → L2 Ω, IsWeakGradient Ω u g →
        neumannEnergy (f '' Ω) v =
          ENNReal.ofReal (gradForm Ω (fun w => bzCoef (fderiv ℝ f w)) g) := by
  have hΩ' : IsOpen (f '' Ω) := f.isOpenMap Ω hΩ
  -- the converse direction: `u ∈ H¹(Ω) → v ∈ H¹(f(Ω))`
  have hback : u ∈ H1 Ω → v ∈ H1 (f '' Ω) := by
    rintro ⟨g, hg'⟩
    have hv : (v : ℂ → ℂ) =ᵐ[volume.restrict (f '' Ω)] fun y => (u : ℂ → ℂ) (f.symm y) := by
      have := (quasiMeasurePreserving_symm_restrict hf).ae_eq hu
      filter_upwards [this] with y hy
      simp only [Function.comp_apply, Homeomorph.apply_symm_apply] at hy
      exact hy.symm
    obtain ⟨G, hG, -⟩ := exists_isWeakGradient_comp_bilip (f := f.symm) (Ω := f '' Ω)
      (f.symm_image_image Ω) hΩ' hK hg (by simpa using hf) hg' hv
    exact ⟨G, hG⟩
  have hfwd : v ∈ H1 (f '' Ω) → u ∈ H1 Ω := by
    rintro ⟨G, hG⟩
    obtain ⟨g, hg', -⟩ := exists_isWeakGradient_comp_bilip rfl hΩ hK hf hg hG hu
    exact ⟨g, hg'⟩
  refine ⟨⟨hfwd, hback⟩, fun g hgu => ?_⟩
  obtain ⟨G, hG⟩ := hback ⟨g, hgu⟩
  obtain ⟨g', hg', hg'eq⟩ := exists_isWeakGradient_comp_bilip rfl hΩ hK hf hg hG hu
  have hgg : g = g' := hgu.unique hΩ hg'
  subst hgg
  rw [neumannEnergy_eq_of_isWeakGradient hΩ' hG]
  have hdet : ∀ᵐ w ∂(volume.restrict Ω), (fderiv ℝ f w).det ≠ 0 :=
    (ae_inv_sq_le_abs_det hΩ hf hg).mono fun w hw =>
      abs_pos.mp (lt_of_lt_of_le (by have := hK; positivity) hw)
  have hpt : ∀ᵐ w ∂(volume.restrict Ω),
      coefSesq (bzCoef (fderiv ℝ f w)) (fun i => (g i : ℂ → ℂ) w) (fun i => (g i : ℂ → ℂ) w) =
        |(fderiv ℝ f w).det| • ∑ j, inner ℂ ((G j : ℂ → ℂ) (f w)) ((G j : ℂ → ℂ) (f w)) := by
    filter_upwards [hdet, ae_all_iff.2 hg'eq] with w hw hgw
    simp only [coefSesq, hgw, chainGrad]
    rw [sesq_bzCoef_chain _ hw]
    simp only [inner_self_eq_norm_sq_to_K, Complex.real_smul]
    push_cast
    rfl
  have hS : (∫ y in f '' Ω, ∑ j, inner ℂ ((G j : ℂ → ℂ) y) ((G j : ℂ → ℂ) y)) =
      ∑ j, inner ℂ (G j) (G j) := by
    rw [integral_finset_sum _ (fun j _ => L2.integrable_inner (G j) (G j))]
    simp only [L2.inner_def]
  have hform : gradForm Ω (fun w => bzCoef (fderiv ℝ f w)) g = ∑ j, ‖G j‖ ^ 2 := by
    rw [gradForm, integral_congr_ae hpt, ← integral_image_bilip hΩ hf
      (fun y => ∑ j, inner ℂ ((G j : ℂ → ℂ) y) ((G j : ℂ → ℂ) y)), hS, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) (G j)).symm
  rw [hform, ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  rfl


/-- Lemma 10.9 and the Sobolev part of Lemma 10.10 for a Ball–Zarnescu approximation
`Ω_n = f_n(Ω)`: there are coefficient matrices `A_n` on `Ω` (in the paper
`A_n = ρ_n (Df_n)⁻¹ (Df_n)⁻ᵀ`), uniformly bounded and uniformly elliptic and equal to `I` off the
collars, such that for `v ∈ L²(Ω_n)` and `u = v ∘ f_n ∈ L²(Ω)`: `v ∈ H¹(Ω_n)` if and only if
`u ∈ H¹(Ω)`, and then `q_{Ω_n}[v] = ∫_Ω ∇ū · A_n ∇u`. Proved from the bi-Lipschitz Sobolev chain
rule `∇(v ∘ f) = (Df)ᵀ (∇v) ∘ f` (`exists_isWeakGradient_comp_bilip`) and the change of variables
formula `integral_image_bilip`. -/
theorem exists_bzChainRule {Ω : Set ℂ} (hL : IsLipschitzDomain Ω) (A : BallZarnescuApprox Ω) :
    ∃ (coef : ℕ → ℂ → Matrix (Fin 2) (Fin 2) ℝ) (bound ellip : ℝ),
      (∀ n i k, AEStronglyMeasurable (fun w => coef n w i k) (volume.restrict Ω)) ∧
      (∀ n, ∀ᵐ w ∂(volume.restrict Ω), ∀ i k, |coef n w i k| ≤ bound) ∧ 0 < ellip ∧
      (∀ n, ∀ᵐ w ∂(volume.restrict Ω), ∀ ξ : Fin 2 → ℂ,
        ellip * ∑ i, ‖ξ i‖ ^ 2 ≤ (coefSesq (coef n w) ξ ξ).re) ∧
      (∀ n, ∀ w ∈ Ω, w ∉ A.collar n → coef n w = 1) ∧
      ∀ n (v : L2 (A.map n '' Ω)) (u : L2 Ω),
        (u : ℂ → ℂ) =ᵐ[volume.restrict Ω] (fun x => (v : ℂ → ℂ) (A.map n x)) →
        (v ∈ H1 (A.map n '' Ω) ↔ u ∈ H1 Ω) ∧
        ∀ g : Fin 2 → L2 Ω, IsWeakGradient Ω u g →
          neumannEnergy (A.map n '' Ω) v = ENNReal.ofReal (gradForm Ω (coef n) g) := by
  have hΩ : IsOpen Ω := hL.1.1
  set K : NNReal := max A.lip 1
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hK' : (0 : ℝ) < K := hK
  have hf : ∀ n, LipschitzOnWith K (A.map n) Ω := fun n =>
    lipschitzOnWith_weaken ((A.lipschitz n).mono subset_closure) (le_max_left _ _)
  have hg : ∀ n, LipschitzOnWith K (A.map n).symm (A.map n '' Ω) := fun n =>
    lipschitzOnWith_weaken ((A.lipschitz_symm n).mono subset_closure) (le_max_left _ _)
  have hnorm : ∀ n, ∀ w ∈ Ω, ‖fderiv ℝ (A.map n) w‖ ≤ K := fun n w hw =>
    norm_fderiv_le_of_lipschitzOn ℝ (hΩ.mem_nhds hw) (hf n)
  refine ⟨fun n w => bzCoef (fderiv ℝ (A.map n) w), 2 * (K : ℝ) ^ 2 * (K : ℝ) ^ 2,
    (2 * (K : ℝ) ^ 2 * (K : ℝ) ^ 2)⁻¹, fun n i k =>
      ((measurable_bzCoef i k).comp (measurable_fderiv ℝ _)).aestronglyMeasurable,
    fun n => ?_, by positivity, fun n => ?_, fun n w _ hwc => ?_,
    fun n v u hu => bzChainRule_of_bilip hΩ hK (hf n) (hg n) v u hu⟩
  · filter_upwards [ae_inv_sq_le_abs_det hΩ (hf n) (hg n), ae_restrict_mem hΩ.measurableSet]
      with w hw hwΩ i k
    have hpos : 0 < ((K : ℝ) ^ 2)⁻¹ := by positivity
    calc |bzCoef (fderiv ℝ (A.map n) w) i k|
        ≤ 2 * ‖fderiv ℝ (A.map n) w‖ ^ 2 / |(fderiv ℝ (A.map n) w).det| := abs_bzCoef_le _ i k
      _ ≤ 2 * (K : ℝ) ^ 2 / ((K : ℝ) ^ 2)⁻¹ := by
          gcongr
          exact hnorm n w hwΩ
      _ = 2 * (K : ℝ) ^ 2 * (K : ℝ) ^ 2 := by field_simp
  · filter_upwards [ae_inv_sq_le_abs_det hΩ (hf n) (hg n), ae_restrict_mem hΩ.measurableSet]
      with w hw hwΩ ξ
    set T := fderiv ℝ (A.map n) w
    have hpos : 0 < ((K : ℝ) ^ 2)⁻¹ := by positivity
    have hT : T.det ≠ 0 := abs_pos.mp (hpos.trans_le hw)
    have e := bzCoef_ellip T hT ξ
    have hre := re_sesq_bzCoef_nonneg T ξ
    have hTK : ‖T‖ ^ 2 ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hnorm n w hwΩ) 2
    have hsum : 0 ≤ ∑ i, ‖ξ i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    change _ ≤ (∑ i, ∑ k, ((bzCoef T) i k : ℂ) * inner ℂ (ξ i) (ξ k)).re
    set R := (∑ i, ∑ k, ((bzCoef T) i k : ℂ) * inner ℂ (ξ i) (ξ k)).re
    have h1 : ((K : ℝ) ^ 2)⁻¹ * ∑ i, ‖ξ i‖ ^ 2 ≤ 2 * (K : ℝ) ^ 2 * R :=
      (mul_le_mul_of_nonneg_right hw hsum).trans (e.trans (by gcongr))
    rw [inv_mul_le_iff₀ (by positivity)]
    rw [inv_mul_le_iff₀ (by positivity)] at h1
    nlinarith
  · have hev : (A.map n : ℂ → ℂ) =ᶠ[𝓝 w] id :=
      Filter.eventually_of_mem ((A.collar_closed n).isOpen_compl.mem_nhds hwc)
        fun x hx => A.eq_self n x hx
    show bzCoef (fderiv ℝ (A.map n) w) = 1
    rw [hev.fderiv_eq, fderiv_id]
    exact bzCoef_id

/-- Lemmas 10.9 and 10.10: the pullback data exist for every Ball–Zarnescu approximation of a
bounded Lipschitz domain. Proved from the bi-Lipschitz change of variables (`bilipPull`,
`inner_eq_integral_bilipPull`, `ae_inv_sq_le_abs_det`) and the Sobolev chain rule
`exists_bzChainRule`. -/
theorem exists_pullbackData {Ω : Set ℂ} (hL : IsLipschitzDomain Ω) (A : BallZarnescuApprox Ω) :
    Nonempty (PullbackData Ω A) := by
  obtain ⟨coef, bound, ellip, hm, hbd, hell, hel, hone, hchain⟩ := exists_bzChainRule hL A
  have hΩ : IsOpen Ω := hL.1.1
  set K : NNReal := max A.lip 1
  have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hf : ∀ n, LipschitzOnWith K (A.map n) Ω := fun n =>
    lipschitzOnWith_weaken ((A.lipschitz n).mono subset_closure) (le_max_left _ _)
  have hg : ∀ n, LipschitzOnWith K (A.map n).symm (A.map n '' Ω) := fun n =>
    lipschitzOnWith_weaken ((A.lipschitz_symm n).mono subset_closure) (le_max_left _ _)
  set e := min ellip ((K : ℝ) ^ 2)⁻¹
  have he : 0 < e := lt_min hell (by positivity)
  exact ⟨{
    coef := coef
    coef_meas := hm
    bound := bound
    coef_bound := hbd
    ellip := e
    ellip_pos := he
    coef_ellip := fun n => (hel n).mono fun w hw ξ =>
      le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (Finset.sum_nonneg fun i _ => sq_nonneg _)) (hw ξ)
    coef_eq_one := hone
    density_ge := fun n => (ae_inv_sq_le_abs_det hΩ (hf n) (hg n)).mono fun w hw =>
      (min_le_right _ _).trans hw
    pull := fun n => bilipPull hΩ hK (hf n) (hg n)
    pull_inner := fun n v w => inner_eq_integral_bilipPull hΩ hK (hf n) (hg n) v w
    pull_H1 := fun n v => (hchain n v _ (bilipPull_ae hΩ hK (hf n) (hg n) v)).1
    pull_energy := fun n v g hg' => (hchain n v _ (bilipPull_ae hΩ hK (hf n) (hg n) v)).2 g hg' }⟩

/-! ### The gradient forms -/

section GradForm

variable {Ω : Set ℂ} {M : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {C : ℝ}

lemma coefSesq_one (ξ η : Fin 2 → ℂ) : coefSesq 1 ξ η = ∑ i, inner ℂ (ξ i) (η i) := by
  simp [coefSesq, Matrix.one_apply]

lemma coefSesq_add_left (N : Matrix (Fin 2) (Fin 2) ℝ) (ξ ξ' η : Fin 2 → ℂ) :
    coefSesq N (ξ + ξ') η = coefSesq N ξ η + coefSesq N ξ' η := by
  simp [coefSesq, mul_add, Finset.sum_add_distrib]

lemma coefSesq_add_right (N : Matrix (Fin 2) (Fin 2) ℝ) (ξ η η' : Fin 2 → ℂ) :
    coefSesq N ξ (η + η') = coefSesq N ξ η + coefSesq N ξ η' := by
  simp only [coefSesq, Pi.add_apply, inner_add_right, mul_add, Finset.sum_add_distrib]

lemma coefSesq_smul_left (N : Matrix (Fin 2) (Fin 2) ℝ) (c : ℂ) (ξ η : Fin 2 → ℂ) :
    coefSesq N (c • ξ) η = conj c * coefSesq N ξ η := by
  simp only [coefSesq, Pi.smul_apply, inner_smul_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma coefSesq_smul_right (N : Matrix (Fin 2) (Fin 2) ℝ) (c : ℂ) (ξ η : Fin 2 → ℂ) :
    coefSesq N ξ (c • η) = c * coefSesq N ξ η := by
  simp only [coefSesq, Pi.smul_apply, inner_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma ae_coeFn_add_pi (g g' : Fin 2 → L2 Ω) :
    ∀ᵐ w ∂(volume.restrict Ω), ∀ i, ((g + g') i : ℂ → ℂ) w = (g i : ℂ → ℂ) w + (g' i : ℂ → ℂ) w :=
  ae_all_iff.mpr fun i => Lp.coeFn_add (g i) (g' i)

lemma ae_coeFn_smul_pi (c : ℂ) (g : Fin 2 → L2 Ω) :
    ∀ᵐ w ∂(volume.restrict Ω), ∀ i, ((c • g) i : ℂ → ℂ) w = c * (g i : ℂ → ℂ) w :=
  ae_all_iff.mpr fun i => Lp.coeFn_smul c (g i)

lemma integrable_coefSesq (hMm : ∀ i k, AEStronglyMeasurable (fun w => M w i k) (volume.restrict Ω))
    (hMb : ∀ᵐ w ∂(volume.restrict Ω), ∀ i k, |M w i k| ≤ C) (g h : Fin 2 → L2 Ω) :
    Integrable (fun w => coefSesq (M w) (fun i => (g i : ℂ → ℂ) w) (fun i => (h i : ℂ → ℂ) w))
      (volume.restrict Ω) := by
  unfold coefSesq
  refine integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun k _ => ?_
  exact (L2.integrable_inner (g i) (h k)).bdd_mul
    (Complex.continuous_ofReal.comp_aestronglyMeasurable (hMm i k))
    (hMb.mono fun w hw => by simpa [Complex.norm_real] using hw i k)

/-- The sesquilinear form `(g, h) ↦ ∫_Ω ∑_{i,k} M_{ik} ⟨g_i, h_k⟩` on gradients. -/
def gradSesq (hMm : ∀ i k, AEStronglyMeasurable (fun w => M w i k) (volume.restrict Ω))
    (hMb : ∀ᵐ w ∂(volume.restrict Ω), ∀ i k, |M w i k| ≤ C) :
    (Fin 2 → L2 Ω) →ₗ⋆[ℂ] (Fin 2 → L2 Ω) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun g h => ∫ w in Ω, coefSesq (M w) (fun i => (g i : ℂ → ℂ) w) (fun i => (h i : ℂ → ℂ) w))
    (fun g₁ g₂ h => by
      rw [← integral_add (integrable_coefSesq hMm hMb _ _) (integrable_coefSesq hMm hMb _ _)]
      refine integral_congr_ae ?_
      filter_upwards [ae_coeFn_add_pi g₁ g₂] with w hw
      rw [← coefSesq_add_left]
      congr 1
      funext i
      exact hw i)
    (fun c g h => by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [ae_coeFn_smul_pi c g] with w hw
      rw [← coefSesq_smul_left]
      congr 1
      funext i
      exact hw i)
    (fun g h₁ h₂ => by
      rw [← integral_add (integrable_coefSesq hMm hMb _ _) (integrable_coefSesq hMm hMb _ _)]
      refine integral_congr_ae ?_
      filter_upwards [ae_coeFn_add_pi h₁ h₂] with w hw
      rw [← coefSesq_add_right]
      congr 1
      funext i
      exact hw i)
    (fun c g h => by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [ae_coeFn_smul_pi c h] with w hw
      rw [← coefSesq_smul_right]
      congr 1
      funext i
      exact hw i)

lemma gradSesq_apply (hMm : ∀ i k, AEStronglyMeasurable (fun w => M w i k) (volume.restrict Ω))
    (hMb : ∀ᵐ w ∂(volume.restrict Ω), ∀ i k, |M w i k| ≤ C) (g h : Fin 2 → L2 Ω) :
    gradSesq hMm hMb g h =
      ∫ w in Ω, coefSesq (M w) (fun i => (g i : ℂ → ℂ) w) (fun i => (h i : ℂ → ℂ) w) := rfl

lemma gradForm_eq_re (hMm : ∀ i k, AEStronglyMeasurable (fun w => M w i k) (volume.restrict Ω))
    (hMb : ∀ᵐ w ∂(volume.restrict Ω), ∀ i k, |M w i k| ≤ C) (g : Fin 2 → L2 Ω) :
    gradForm Ω M g = (gradSesq hMm hMb g g).re := by
  rw [gradSesq_apply]; rfl

lemma gradForm_smul (hMm : ∀ i k, AEStronglyMeasurable (fun w => M w i k) (volume.restrict Ω))
    (hMb : ∀ᵐ w ∂(volume.restrict Ω), ∀ i k, |M w i k| ≤ C) (c : ℂ) (g : Fin 2 → L2 Ω) :
    gradForm Ω M (c • g) = ‖c‖ ^ 2 * gradForm Ω M g := by
  rw [gradForm_eq_re hMm hMb, gradForm_eq_re hMm hMb]
  simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
  rw [← mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]

lemma gradForm_one (g : Fin 2 → L2 Ω) : gradForm Ω 1 g = ∑ i, ‖g i‖ ^ 2 := by
  unfold gradForm
  simp only [Pi.one_apply, coefSesq_one]
  rw [integral_finset_sum _ fun i _ => L2.integrable_inner (g i) (g i), Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← L2.inner_def, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- If `M = I` on `F ∩ Ω` and `M` is positive semidefinite, then `∑ᵢ ∫_F |gᵢ|² ≤ q_M[g]`. -/
lemma integral_restrict_le_gradForm
    (hMm : ∀ i k, AEStronglyMeasurable (fun w => M w i k) (volume.restrict Ω))
    (hMb : ∀ᵐ w ∂(volume.restrict Ω), ∀ i k, |M w i k| ≤ C)
    (hMp : ∀ᵐ w ∂(volume.restrict Ω), ∀ ξ : Fin 2 → ℂ, 0 ≤ (coefSesq (M w) ξ ξ).re)
    (hΩ : MeasurableSet Ω) {F : Set ℂ} (hF : MeasurableSet F)
    (hMF : ∀ w ∈ Ω, w ∈ F → M w = 1) (g : Fin 2 → L2 Ω) :
    ∑ i, ∫ w in F, ‖(g i : ℂ → ℂ) w‖ ^ 2 ∂(volume.restrict Ω) ≤ gradForm Ω M g := by
  have hint : ∀ i, Integrable (fun w => ‖(g i : ℂ → ℂ) w‖ ^ 2) (volume.restrict Ω) := fun i =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  rw [← integral_finset_sum _ fun i _ => (hint i).integrableOn, ← integral_indicator hF,
    gradForm]
  refine (integral_mono_ae ((integrable_finset_sum _ fun i _ => hint i).indicator hF)
    (integrable_coefSesq hMm hMb g g).re ?_).trans_eq
    (integral_re (integrable_coefSesq hMm hMb g g))
  filter_upwards [hMp, ae_restrict_mem hΩ] with w hw hwΩ
  by_cases hwF : w ∈ F
  · rw [Set.indicator_of_mem hwF, hMF w hwΩ hwF, coefSesq_one, map_sum]
    exact le_of_eq (Finset.sum_congr rfl fun i _ => (inner_self_eq_norm_sq _).symm)
  · rw [Set.indicator_of_notMem hwF]
    exact hw _

/-- Convergence of the gradient sesquilinear forms when the matrices are eventually `I`. -/
lemma tendsto_integral_coefSesq (M : ℕ → ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (hMm : ∀ n i k, AEStronglyMeasurable (fun w => M n w i k) (volume.restrict Ω))
    (hMb : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), ∀ i k, |M n w i k| ≤ C)
    (hev : ∀ᵐ w ∂(volume.restrict Ω), ∀ᶠ n in atTop, M n w = 1) (g h : Fin 2 → L2 Ω) :
    Tendsto (fun n => ∫ w in Ω, coefSesq (M n w) (fun i => (g i : ℂ → ℂ) w)
      (fun i => (h i : ℂ → ℂ) w)) atTop
      (𝓝 (∫ w in Ω, coefSesq 1 (fun i => (g i : ℂ → ℂ) w) (fun i => (h i : ℂ → ℂ) w))) := by
  set C' := max C 0
  refine tendsto_integral_of_dominated_convergence
    (fun w => C' * ∑ i, ∑ k, ‖inner ℂ ((g i : ℂ → ℂ) w) ((h k : ℂ → ℂ) w)‖)
    (fun n => (integrable_coefSesq (hMm n) (hMb n) g h).aestronglyMeasurable)
    ((integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun k _ =>
      (L2.integrable_inner (g i) (h k)).norm).const_mul C') (fun n => ?_) ?_
  · filter_upwards [hMb n] with w hw
    unfold coefSesq
    calc _ ≤ ∑ i, ‖∑ k, ((M n w i k : ℝ) : ℂ) *
          inner ℂ ((g i : ℂ → ℂ) w) ((h k : ℂ → ℂ) w)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ k, ‖((M n w i k : ℝ) : ℂ) *
          inner ℂ ((g i : ℂ → ℂ) w) ((h k : ℂ → ℂ) w)‖ :=
        Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ ≤ ∑ i, ∑ k, C' * ‖inner ℂ ((g i : ℂ → ℂ) w) ((h k : ℂ → ℂ) w)‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right ((hw i k).trans (le_max_left _ _)) (norm_nonneg _)
      _ = _ := by simp_rw [Finset.mul_sum]
  · filter_upwards [hev] with w hw
    exact tendsto_const_nhds.congr' (hw.mono fun n hn => by simp only [hn])

end GradForm

/-! ### Weak gradients on a subspace of `H¹` -/

/-- The weak gradient, as a linear map on a subspace of `H¹(Ω)` (`Ω` open). -/
def gradOf {Ω : Set ℂ} (hΩ : IsOpen Ω) (S : Submodule ℂ (L2 Ω)) (hS : (S : Set (L2 Ω)) ⊆ H1 Ω) :
    S →ₗ[ℂ] (Fin 2 → L2 Ω) where
  toFun u := (hS u.2).choose
  map_add' u v := (hS (u + v).2).choose_spec.unique hΩ (by
    simpa using (hS u.2).choose_spec.add (hS v.2).choose_spec)
  map_smul' c u := (hS (c • u).2).choose_spec.unique hΩ (by
    simpa using (hS u.2).choose_spec.smul c)

lemma isWeakGradient_gradOf {Ω : Set ℂ} (hΩ : IsOpen Ω) (S : Submodule ℂ (L2 Ω))
    (hS : (S : Set (L2 Ω)) ⊆ H1 Ω) (u : S) : IsWeakGradient Ω u (gradOf hΩ S hS u) :=
  (hS u.2).choose_spec

/-! ### Hilbert space and `L²` facts -/

/-- In a separable Hilbert space, finitely many bounded sequences have a common subsequence along
which all of them converge in some sense, provided each of these senses of convergence is
inherited by subsequences and every subsequence has a further convergent subsequence. -/
theorem exists_common_subseq {ι : Type*} [Fintype ι] (P : ι → (ℕ → ℕ) → Prop)
    (hmono : ∀ i (θ θ' : ℕ → ℕ), P i θ → StrictMono θ' → P i (θ ∘ θ'))
    (hex : ∀ i (θ : ℕ → ℕ), StrictMono θ → ∃ θ' : ℕ → ℕ, StrictMono θ' ∧ P i (θ ∘ θ')) :
    ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ i, P i θ := by
  classical
  suffices h : ∀ s : Finset ι, ∃ θ : ℕ → ℕ, StrictMono θ ∧ ∀ i ∈ s, P i θ by
    obtain ⟨θ, hθ, hP⟩ := h Finset.univ
    exact ⟨θ, hθ, fun i => hP i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | insert a s ha ih =>
    obtain ⟨θ, hθ, hP⟩ := ih
    obtain ⟨θ', hθ', hP'⟩ := hex a θ hθ
    refine ⟨θ ∘ θ', hθ.comp hθ', fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hP'
    · exact hmono i θ θ' (hP i hi) hθ'

/-- Weak convergence is preserved by continuous linear maps. -/
lemma weak_tendsto_map {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : H →L[ℂ] K) {x : ℕ → H} {y : H}
    (hx : ∀ z, Tendsto (fun n => inner ℂ z (x n)) atTop (𝓝 (inner ℂ z y))) :
    ∀ z, Tendsto (fun n => inner ℂ z (T (x n))) atTop (𝓝 (inner ℂ z (T y))) := by
  intro z
  simp_rw [← ContinuousLinearMap.adjoint_inner_left]
  exact hx _

/-- Weak lower semicontinuity of the norm. -/
lemma weak_lsc_norm_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {x : ℕ → H} {y : H}
    (hx : ∀ z, Tendsto (fun n => inner ℂ z (x n)) atTop (𝓝 (inner ℂ z y))) :
    ∀ ε > 0, ∀ᶠ n in atTop, ‖y‖ ^ 2 - ε ≤ ‖x n‖ ^ 2 := by
  intro ε hε
  have h := (Complex.continuous_re.tendsto _).comp (hx y)
  have hyy : (inner ℂ y y : ℂ).re = ‖y‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hyy] at h
  filter_upwards [h.eventually (lt_mem_nhds (show ‖y‖ ^ 2 - ε / 2 < ‖y‖ ^ 2 by linarith))]
    with n hn
  have h1 := re_inner_le_norm (𝕜 := ℂ) y (x n)
  simp only [Function.comp_apply] at hn
  have h2 : (inner ℂ y (x n)).re = RCLike.re (inner ℂ y (x n)) := rfl
  nlinarith [sq_nonneg (‖y‖ - ‖x n‖)]

lemma integral_norm_sq_eq_of {μ : Measure ℂ} (u : Lp ℂ 2 μ) :
    ∫ w, ‖(u : ℂ → ℂ) w‖ ^ 2 ∂μ = ‖u‖ ^ 2 := by
  have h := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) u u)
  rw [inner_self_eq_norm_sq, ← integral_re (L2.integrable_inner u u)] at h
  simp_rw [inner_self_eq_norm_sq] at h
  exact h.symm

lemma integral_norm_sq_eq {Ω : Set ℂ} (u : L2 Ω) :
    ∫ w in Ω, ‖(u : ℂ → ℂ) w‖ ^ 2 = ‖u‖ ^ 2 :=
  integral_norm_sq_eq_of u

/-- Weak lower semicontinuity of `∫_F |·|²`. -/
lemma weak_lsc_restrict {Ω : Set ℂ} {x : ℕ → L2 Ω} {y : L2 Ω}
    (hx : ∀ z, Tendsto (fun n => inner ℂ z (x n)) atTop (𝓝 (inner ℂ z y))) (F : Set ℂ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∫ w in F, ‖(y : ℂ → ℂ) w‖ ^ 2 ∂(volume.restrict Ω) - ε ≤
      ∫ w in F, ‖(x n : ℂ → ℂ) w‖ ^ 2 ∂(volume.restrict Ω) := by
  intro ε hε
  set T := LpToLpRestrictCLM ℂ ℂ ℂ (volume.restrict Ω) 2 F
  have hT : ∀ v : L2 Ω, ∫ w in F, ‖(v : ℂ → ℂ) w‖ ^ 2 ∂(volume.restrict Ω) = ‖T v‖ ^ 2 := by
    intro v
    rw [← integral_norm_sq_eq_of (T v)]
    refine integral_congr_ae ?_
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ F v] with w hw
    rw [hw]
  simp_rw [hT]
  exact weak_lsc_norm_sq (weak_tendsto_map T hx) ε hε

/-- Weak gradients pass to limits with strongly convergent functions and weakly convergent
gradients. -/
lemma isWeakGradient_of_weak_tendsto {Ω : Set ℂ} {u : ℕ → L2 Ω} {g : ℕ → Fin 2 → L2 Ω}
    {U : L2 Ω} {G : Fin 2 → L2 Ω} (hg : ∀ n, IsWeakGradient Ω (u n) (g n))
    (hu : Tendsto u atTop (𝓝 U))
    (hG : ∀ i z, Tendsto (fun n => inner ℂ z (g n i)) atTop (𝓝 (inner ℂ z (G i)))) :
    IsWeakGradient Ω U G := by
  intro φ hφ i
  have hmem : ∀ ψ : ℂ → ℂ, Continuous ψ → HasCompactSupport ψ →
      MemLp (fun w => (starRingEnd ℂ) (ψ w)) 2 (volume.restrict Ω) := fun ψ hc hs =>
    ((Complex.continuous_conj.comp hc).memLp_of_hasCompactSupport
      (hs.comp_left (map_zero _))).restrict Ω
  have key : ∀ (ψ : ℂ → ℂ) (hψ : MemLp (fun w => (starRingEnd ℂ) (ψ w)) 2 (volume.restrict Ω))
      (H : L2 Ω), ∫ w in Ω, H w * ψ w = inner ℂ (hψ.toLp _) H := by
    intro ψ hψ H
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hψ.coeFn_toLp] with w hw
    simp only [hw, RCLike.inner_apply, Complex.conj_conj]
  have hd : Continuous fun w => fderiv ℝ φ w (coordDir i) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : HasCompactSupport fun w => fderiv ℝ φ w (coordDir i) :=
    (hφ.2.1.fderiv ℝ).comp_left (g := fun T : ℂ →L[ℝ] ℂ => T (coordDir i)) rfl
  have h1 := tendsto_integral_mul (hmem _ hd hds) hu
  have h2 : Tendsto (fun n => -∫ w in Ω, g n i w * φ w) atTop (𝓝 (-∫ w in Ω, G i w * φ w)) := by
    simp_rw [key φ (hmem _ hφ.1.continuous hφ.2.1)]
    exact (hG i _).neg
  refine tendsto_nhds_unique h1 ?_
  exact h2.congr fun n => (hg n φ hφ i).symm

/-- Hölder's inequality in `L²(Ω)`. -/
lemma integral_norm_mul_le {Ω : Set ℂ} (u v : L2 Ω) :
    ∫ w in Ω, ‖(u : ℂ → ℂ) w‖ * ‖(v : ℂ → ℂ) w‖ ≤ ‖u‖ * ‖v‖ := by
  have h2 : ENNReal.ofReal 2 = 2 := by simp
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := volume.restrict Ω) (f := (u : ℂ → ℂ))
    (g := (v : ℂ → ℂ)) Real.HolderConjugate.two_two (by rw [h2]; exact Lp.memLp u)
    (by rw [h2]; exact Lp.memLp v)
  simp_rw [Real.rpow_two] at h
  rwa [integral_norm_sq_eq, integral_norm_sq_eq, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h

lemma integrable_norm_mul_L2 {Ω : Set ℂ} (u v : L2 Ω) :
    Integrable (fun w => ‖(u : ℂ → ℂ) w‖ * ‖(v : ℂ → ℂ) w‖) (volume.restrict Ω) :=
  (Lp.memLp u).norm.integrable_mul (Lp.memLp v).norm

/-- Weighted inner products converge along strongly convergent sequences, for uniformly bounded
weights converging to `1` almost everywhere. -/
lemma tendsto_weighted_inner {Ω : Set ℂ} (ρ : ℕ → ℂ → ℝ) (C : ℝ)
    (hm : ∀ n, AEStronglyMeasurable (ρ n) (volume.restrict Ω))
    (hb₀ : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), |ρ n w| ≤ C)
    (ht : ∀ᵐ w ∂(volume.restrict Ω), Tendsto (fun n => ρ n w) atTop (𝓝 1))
    {x y : ℕ → L2 Ω} {X Y : L2 Ω} (hx : Tendsto x atTop (𝓝 X)) (hy : Tendsto y atTop (𝓝 Y)) :
    Tendsto (fun n => ∫ w in Ω, (ρ n w : ℂ) * inner ℂ ((x n : ℂ → ℂ) w) ((y n : ℂ → ℂ) w))
      atTop (𝓝 (inner ℂ X Y)) := by
  set C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  have hb : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), |ρ n w| ≤ C' := fun n =>
    (hb₀ n).mono fun w hw => hw.trans (le_max_left _ _)
  -- the fixed term, by dominated convergence
  have hE : Tendsto (fun n => ∫ w in Ω, (ρ n w : ℂ) * inner ℂ ((X : ℂ → ℂ) w) ((Y : ℂ → ℂ) w))
      atTop (𝓝 (inner ℂ X Y)) := by
    rw [L2.inner_def]
    refine tendsto_integral_of_dominated_convergence
      (fun w => C' * ‖inner ℂ ((X : ℂ → ℂ) w) ((Y : ℂ → ℂ) w)‖)
      (fun n => (integrable_weight_inner (hm n) (hb n) _ _).aestronglyMeasurable)
      ((L2.integrable_inner _ _).norm.const_mul C') (fun n => ?_) ?_
    · filter_upwards [hb n] with w hw
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    · filter_upwards [ht] with w hw
      have := ((Complex.continuous_ofReal.tendsto 1).comp hw).mul_const
        (inner ℂ ((X : ℂ → ℂ) w) ((Y : ℂ → ℂ) w))
      simpa using this
  -- the difference term
  have hD : Tendsto (fun n => C' * (‖x n - X‖ * ‖y n‖ + ‖X‖ * ‖y n - Y‖)) atTop (𝓝 0) := by
    have h := (((tendsto_iff_norm_sub_tendsto_zero.mp hx).mul hy.norm).add
      ((tendsto_const_nhds (x := ‖X‖)).mul
        (tendsto_iff_norm_sub_tendsto_zero.mp hy))).const_mul C'
    simpa using h
  have hbound : ∀ n, ‖(∫ w in Ω, (ρ n w : ℂ) * inner ℂ ((x n : ℂ → ℂ) w) ((y n : ℂ → ℂ) w)) -
      ∫ w in Ω, (ρ n w : ℂ) * inner ℂ ((X : ℂ → ℂ) w) ((Y : ℂ → ℂ) w)‖ ≤
      C' * (‖x n - X‖ * ‖y n‖ + ‖X‖ * ‖y n - Y‖) := by
    intro n
    rw [← integral_sub (integrable_weight_inner (hm n) (hb n) _ _)
      (integrable_weight_inner (hm n) (hb n) _ _)]
    have hint := ((integrable_norm_mul_L2 (x n - X) (y n)).add
      (integrable_norm_mul_L2 X (y n - Y))).const_mul C'
    refine (norm_integral_le_of_norm_le hint ?_).trans ?_
    · filter_upwards [hb n, Lp.coeFn_sub (x n) X, Lp.coeFn_sub (y n) Y] with w hw h1 h2
      simp only [Pi.add_apply]
      rw [h1, h2, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, Pi.sub_apply,
        Pi.sub_apply]
      refine mul_le_mul hw ?_ (norm_nonneg _) hC'
      have e : inner ℂ ((x n : ℂ → ℂ) w) ((y n : ℂ → ℂ) w) -
          inner ℂ ((X : ℂ → ℂ) w) ((Y : ℂ → ℂ) w) =
          inner ℂ ((x n : ℂ → ℂ) w - (X : ℂ → ℂ) w) ((y n : ℂ → ℂ) w) +
          inner ℂ ((X : ℂ → ℂ) w) ((y n : ℂ → ℂ) w - (Y : ℂ → ℂ) w) := by
        rw [inner_sub_left, inner_sub_right]; ring
      rw [e]
      exact (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    · simp only [Pi.add_apply]
      rw [integral_const_mul, integral_add (integrable_norm_mul_L2 _ _)
        (integrable_norm_mul_L2 _ _)]
      exact mul_le_mul_of_nonneg_left (add_le_add (integral_norm_mul_le _ _)
        (integral_norm_mul_le _ _)) hC'
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa using hD.add (tendsto_iff_norm_sub_tendsto_zero.mp hE))
  calc _ = ‖((∫ w in Ω, (ρ n w : ℂ) * inner ℂ ((x n : ℂ → ℂ) w) ((y n : ℂ → ℂ) w)) -
        ∫ w in Ω, (ρ n w : ℂ) * inner ℂ ((X : ℂ → ℂ) w) ((Y : ℂ → ℂ) w)) +
        ((∫ w in Ω, (ρ n w : ℂ) * inner ℂ ((X : ℂ → ℂ) w) ((Y : ℂ → ℂ) w)) -
          inner ℂ X Y)‖ := by ring_nf
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add_left (hbound n) _)

/-! ### Densities of the Ball–Zarnescu maps -/

/-- The density `ρ_n = |det Df_n|`. -/
def bzDensity {Ω : Set ℂ} (A : BallZarnescuApprox Ω) (n : ℕ) : ℂ → ℝ :=
  fun w => |(fderiv ℝ (A.map n) w).det|

lemma bzDensity_aestronglyMeasurable {Ω : Set ℂ} (A : BallZarnescuApprox Ω) (n : ℕ) :
    AEStronglyMeasurable (bzDensity A n) (volume.restrict Ω) :=
  ((continuous_abs.comp ContinuousLinearMap.continuous_det).measurable.comp
    (measurable_fderiv ℝ _)).aestronglyMeasurable

lemma bzDensity_bound {Ω : Set ℂ} (hΩ : IsOpen Ω) (A : BallZarnescuApprox Ω) (n : ℕ) :
    ∀ᵐ w ∂(volume.restrict Ω), |bzDensity A n w| ≤ (A.lip : ℝ) ^ 2 :=
  ae_restrict_of_forall_mem hΩ.measurableSet fun w hw => by
    rw [bzDensity, abs_abs]
    exact abs_det_fderiv_le hΩ ((A.lipschitz n).mono subset_closure) hw

lemma bzDensity_tendsto {Ω : Set ℂ} (hΩ : IsOpen Ω) (A : BallZarnescuApprox Ω) {ψ : ℕ → ℕ}
    (hψ : Tendsto ψ atTop atTop) :
    ∀ᵐ w ∂(volume.restrict Ω), Tendsto (fun n => bzDensity A (ψ n) w) atTop (𝓝 1) := by
  refine ae_restrict_of_forall_mem hΩ.measurableSet fun w hw => ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hψ.eventually (A.collar_shrink w hw)] with n hn
  have hloc : (A.map (ψ n) : ℂ → ℂ) =ᶠ[𝓝 w] id :=
    Filter.mem_of_superset ((A.collar_closed _).isOpen_compl.mem_nhds hn)
      fun x hx => A.eq_self _ x hx
  rw [bzDensity, hloc.fderiv_eq, fderiv_id, ContinuousLinearMap.det, ContinuousLinearMap.coe_id,
    LinearMap.det_id, abs_one]

/-! ### Coercivity of the pulled-back forms -/

/-- A lower bound for a weight gives a lower bound for the weighted mass. -/
lemma weightedMass_ge {Ω : Set ℂ} {ρ : ℂ → ℝ} {c C : ℝ}
    (hm : AEStronglyMeasurable ρ (volume.restrict Ω))
    (hb : ∀ᵐ w ∂(volume.restrict Ω), |ρ w| ≤ C)
    (hc : ∀ᵐ w ∂(volume.restrict Ω), c ≤ ρ w) (u : L2 Ω) :
    c * ‖u‖ ^ 2 ≤ weightedMass Ω ρ u := by
  have hint : Integrable (fun w => ‖(u : ℂ → ℂ) w‖ ^ 2) (volume.restrict Ω) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hint2 : Integrable (fun w => ρ w * ‖(u : ℂ → ℂ) w‖ ^ 2) (volume.restrict Ω) :=
    hint.bdd_mul hm (hb.mono fun w hw => by simpa [Real.norm_eq_abs] using hw)
  rw [← integral_norm_sq_eq, ← integral_const_mul, weightedMass]
  refine integral_mono_ae (hint.const_mul c) hint2 ?_
  filter_upwards [hc] with w hw
  exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)

/-- Uniform ellipticity gives coercivity of the gradient form. -/
lemma ellip_le_gradForm {Ω : Set ℂ} {M : ℂ → Matrix (Fin 2) (Fin 2) ℝ} {c C : ℝ}
    (hMm : ∀ i k, AEStronglyMeasurable (fun w => M w i k) (volume.restrict Ω))
    (hMb : ∀ᵐ w ∂(volume.restrict Ω), ∀ i k, |M w i k| ≤ C)
    (hMe : ∀ᵐ w ∂(volume.restrict Ω), ∀ ξ : Fin 2 → ℂ,
      c * ∑ i, ‖ξ i‖ ^ 2 ≤ (coefSesq (M w) ξ ξ).re) (g : Fin 2 → L2 Ω) :
    c * ∑ i, ‖g i‖ ^ 2 ≤ gradForm Ω M g := by
  have hint : ∀ i, Integrable (fun w => ‖(g i : ℂ → ℂ) w‖ ^ 2) (volume.restrict Ω) := fun i =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have e : c * ∑ i, ‖g i‖ ^ 2 = ∫ w in Ω, c * ∑ i, ‖(g i : ℂ → ℂ) w‖ ^ 2 := by
    rw [integral_const_mul, integral_finset_sum _ fun i _ => hint i]
    simp_rw [integral_norm_sq_eq]
  rw [e, gradForm]
  refine (integral_mono_ae ((integrable_finset_sum _ fun i _ => hint i).const_mul c)
    (integrable_coefSesq hMm hMb g g).re ?_).trans_eq
    (integral_re (integrable_coefSesq hMm hMb g g))
  filter_upwards [hMe] with w hw
  exact hw _

/-- The sets `F_N` of points outside all collars `C_m`, `m ≥ N`. -/
def collarFree {Ω : Set ℂ} (A : BallZarnescuApprox Ω) (N : ℕ) : Set ℂ :=
  ⋂ m ∈ Set.Ici N, (A.collar m)ᶜ

lemma measurableSet_collarFree {Ω : Set ℂ} (A : BallZarnescuApprox Ω) (N : ℕ) :
    MeasurableSet (collarFree A N) :=
  MeasurableSet.biInter (Set.to_countable _) fun m _ => (A.collar_closed m).measurableSet.compl

/-- Integrals over the collar-free sets converge to the integral over `Ω`. -/
lemma tendsto_setIntegral_collarFree {Ω : Set ℂ} (A : BallZarnescuApprox Ω) {f : ℂ → ℝ} (hf : Integrable f (volume.restrict Ω)) :
    Tendsto (fun N => ∫ w in collarFree A N, f w ∂(volume.restrict Ω)) atTop
      (𝓝 (∫ w in Ω, f w)) := by
  have hmono : Monotone (collarFree A) := fun N N' hNN' w hw => by
    simp only [collarFree, Set.mem_iInter] at hw ⊢
    exact fun m hm => hw m (le_trans hNN' hm)
  have h := tendsto_setIntegral_of_monotone (μ := volume.restrict Ω)
    (measurableSet_collarFree A) hmono hf.integrableOn
  have hU : Ω ⊆ ⋃ N, collarFree A N := fun w hw => by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (A.collar_shrink w hw)
    exact Set.mem_iUnion.mpr ⟨N, by simpa [collarFree] using hN⟩
  rwa [Measure.restrict_restrict (MeasurableSet.iUnion (measurableSet_collarFree A)),
    Set.inter_eq_self_of_subset_right hU] at h

/-! ### Lemmas 10.10, 10.11 and 10.13 from the pullback data -/

namespace PullbackData

variable {Ω : Set ℂ} {A : BallZarnescuApprox Ω} (P : PullbackData Ω A)

open Classical in
/-- The pulled-back Neumann form `q_n[u] = ∫_Ω ∇ū · A_n ∇u` on `H¹(Ω)` (`0` off `H¹(Ω)`). -/
def formQ (n : ℕ) (u : L2 Ω) : ℝ :=
  if h : u ∈ H1 Ω then gradForm Ω (P.coef n) h.choose else 0

lemma formQ_eq (hΩ : IsOpen Ω) (n : ℕ) {u : L2 Ω} {g : Fin 2 → L2 Ω}
    (hg : IsWeakGradient Ω u g) : P.formQ n u = gradForm Ω (P.coef n) g := by
  have h : u ∈ H1 Ω := ⟨g, hg⟩
  rw [formQ, dif_pos h, h.choose_spec.unique hΩ hg]

lemma weightedMass_pull (hΩ : IsOpen Ω) (n : ℕ) (v : L2 (A.map n '' Ω)) :
    weightedMass Ω (bzDensity A n) (P.pull n v) = ‖v‖ ^ 2 := by
  have h := congrArg RCLike.re (P.pull_inner n v v)
  have hi : Integrable (fun x => ((bzDensity A n x : ℝ) : ℂ) *
      inner ℂ ((P.pull n v : ℂ → ℂ) x) ((P.pull n v : ℂ → ℂ) x)) (volume.restrict Ω) :=
    integrable_weight_inner (bzDensity_aestronglyMeasurable A n) (bzDensity_bound hΩ A n) _ _
  rw [inner_self_eq_norm_sq] at h
  erw [← integral_re hi] at h
  rw [h, weightedMass]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  show bzDensity A n w * _ = RCLike.re (((bzDensity A n w : ℝ) : ℂ) * inner ℂ _ _)
  rw [RCLike.re_to_complex, Complex.re_ofReal_mul, ← RCLike.re_to_complex, inner_self_eq_norm_sq]

lemma weightedMass_smul' (ρ : ℂ → ℝ) (c : ℂ) (u : L2 Ω) :
    weightedMass Ω ρ (c • u) = ‖c‖ ^ 2 * weightedMass Ω ρ u := by
  unfold weightedMass
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c u] with w hw
  rw [hw, Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

/-- Lemma 10.10 (min–max for the pulled-back quotient). -/
theorem minmax (hΩ : IsOpen Ω) (j n : ℕ) (S : Submodule ℂ (L2 Ω))
    (hS : Module.finrank ℂ S = j + 1) (hSH : (S : Set (L2 Ω)) ⊆ H1 Ω) :
    neumannEigenvalue (A.map n '' Ω) j ≤
      ⨆ (u : L2 Ω) (_ : u ∈ S) (_ : ‖u‖ = 1),
        ENNReal.ofReal (P.formQ n u / weightedMass Ω (bzDensity A n) u) := by
  set e : L2 Ω ≃ₗ[ℂ] L2 (A.map n '' Ω) := (P.pull n).symm
  have hS' : Module.finrank ℂ (S.map (e : L2 Ω →ₗ[ℂ] L2 (A.map n '' Ω))) = j + 1 := by
    rw [LinearEquiv.finrank_map_eq]; exact hS
  unfold neumannEigenvalue
  refine (iInf₂_le (S.map (e : L2 Ω →ₗ[ℂ] L2 (A.map n '' Ω))) hS').trans
    (iSup₂_le fun v hv => iSup_le fun hv0 => ?_)
  obtain ⟨u, huS, rfl⟩ := Submodule.mem_map.mp hv
  have hpu : P.pull n (e u) = u := LinearEquiv.apply_symm_apply _ _
  obtain ⟨g, hg⟩ := hSH huS
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hv0 (map_zero _)
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  set c : ℂ := ((‖u‖⁻¹ : ℝ) : ℂ)
  have hc : ‖c‖ = ‖u‖⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnu)]
  have hcu : ‖c • u‖ = 1 := by
    rw [norm_smul, hc, inv_mul_cancel₀ hnu.ne']
  refine le_trans ?_ (le_iSup₂_of_le (c • u) (S.smul_mem c huS) (le_iSup_of_le hcu le_rfl))
  have hen : neumannEnergy (A.map n '' Ω) (e u) = ENNReal.ofReal (gradForm Ω (P.coef n) g) :=
    P.pull_energy n (e u) g (by rw [hpu]; exact hg)
  have hwm : weightedMass Ω (bzDensity A n) u = ‖e u‖ ^ 2 := by
    rw [← P.weightedMass_pull hΩ n (e u), hpu]
  have hev : 0 < ‖e u‖ := norm_pos_iff.mpr hv0
  have hq : P.formQ n (c • u) / weightedMass Ω (bzDensity A n) (c • u) =
      gradForm Ω (P.coef n) g / ‖e u‖ ^ 2 := by
    rw [P.formQ_eq hΩ n (hg.smul c), gradForm_smul (P.coef_meas n) (P.coef_bound n),
      weightedMass_smul', hwm, mul_div_mul_left _ _ (by rw [hc]; positivity)]
  rw [hq, ENNReal.ofReal_div_of_pos (by positivity), ← hen, rayleigh,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, enorm_eq_nnnorm]
  exact le_rfl

/-- Lemma 10.11 (convergence of the pulled-back Neumann forms). -/
theorem formQ_tendsto (hΩ : IsOpen Ω) (S : Submodule ℂ (L2 Ω)) (hS : FiniteDimensional ℂ S)
    (hSH : (S : Set (L2 Ω)) ⊆ H1 Ω) :
    TendstoUniformlyOn P.formQ (fun u => (neumannEnergy Ω u).toReal) atTop
      ((S : Set (L2 Ω)) ∩ Metric.sphere 0 1) := by
  have hev : ∀ᵐ w ∂(volume.restrict Ω), ∀ᶠ n in atTop, P.coef n w = 1 :=
    ae_restrict_of_forall_mem hΩ.measurableSet fun w hw =>
      (A.collar_shrink w hw).mono fun n hn => P.coef_eq_one n w hw hn
  have h1m : ∀ i k, AEStronglyMeasurable (fun w : ℂ => (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) w i k)
      (volume.restrict Ω) := fun _ _ => aestronglyMeasurable_const
  have h1b : ∀ᵐ w ∂(volume.restrict Ω), ∀ i k,
      |(fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) w i k| ≤ 1 :=
    Eventually.of_forall fun w i k => by
      simp only [Matrix.one_apply]
      split_ifs <;> simp
  set G := gradOf hΩ S hSH
  set Bn : ℕ → S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ := fun n =>
    ((gradSesq (P.coef_meas n) (P.coef_bound n)).comp G).compl₂ G
  set B : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ := ((gradSesq h1m h1b).comp G).compl₂ G
  set b := Module.finBasis ℂ S
  have hentries : ∀ r s, Tendsto (fun n => Bn n (b r) (b s)) atTop (𝓝 (B (b r) (b s))) :=
    fun r s => tendsto_integral_coefSesq P.coef P.coef_meas P.coef_bound hev (G (b r)) (G (b s))
  have hK : Bornology.IsBounded {u : S | ‖u‖ = 1} :=
    (Metric.isBounded_closedBall (x := (0 : S)) (r := 1)).subset fun u hu => by
      simp only [Set.mem_setOf_eq] at hu
      simp [hu]
  have hU := tendstoUniformlyOn_sesq_of_basis b Bn B hentries hK
  have hU' := Complex.uniformContinuous_re.comp_tendstoUniformlyOn hU
  intro t ht
  filter_upwards [hU' t ht] with n hn
  rintro u ⟨huS, hu1⟩
  have h1 := hn ⟨u, huS⟩ (by simpa using hu1)
  have hgu := isWeakGradient_gradOf hΩ S hSH ⟨u, huS⟩
  have eq1 : P.formQ n u = (Bn n ⟨u, huS⟩ ⟨u, huS⟩).re := by
    rw [P.formQ_eq hΩ n hgu, gradForm_eq_re (P.coef_meas n) (P.coef_bound n)]
    rfl
  have eq2 : (neumannEnergy Ω u).toReal = (B ⟨u, huS⟩ ⟨u, huS⟩).re := by
    have e3 : (B ⟨u, huS⟩ ⟨u, huS⟩).re = gradForm Ω (fun _ => 1) (G ⟨u, huS⟩) :=
      (gradForm_eq_re h1m h1b _).symm
    rw [e3, neumannEnergy_eq_of_isWeakGradient hΩ hgu, ENNReal.toReal_sum fun i _ => by simp]
    simp only [ENNReal.toReal_pow, ENNReal.coe_toReal, coe_nnnorm]
    exact (gradForm_one _).symm
  rw [eq1, eq2]
  exact h1

/-- Almost-minimizing orthonormal families for the min–max formula: if `μ_j(D) < ∞`, there are
`j + 1` orthonormal functions on whose span the Neumann energy is at most `(μ_j(D) + ε) ‖·‖²`. -/
theorem exists_orthonormal_energy_le (D : Set ℂ) (j : ℕ) (hμ : neumannEigenvalue D j ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : Fin (j + 1) → L2 D, Orthonormal ℂ e ∧ ∀ a : Fin (j + 1) → ℂ,
      neumannEnergy D (∑ r, a r • e r) ≤
        ENNReal.ofReal (((neumannEigenvalue D j).toReal + ε) * ∑ r, ‖a r‖ ^ 2) := by
  have hlt : (⨅ (S : Submodule ℂ (L2 D)) (_ : Module.finrank ℂ S = j + 1),
      ⨆ (u : L2 D) (_ : u ∈ S) (_ : u ≠ 0), rayleigh D u) <
      neumannEigenvalue D j + ENNReal.ofReal ε :=
    ENNReal.lt_add_right hμ (by simpa using hε)
  obtain ⟨S, hS⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hSj, hsup⟩ := iInf_lt_iff.mp hS
  haveI : FiniteDimensional ℂ S := Module.finite_of_finrank_eq_succ hSj
  set ob := (stdOrthonormalBasis ℂ S).reindex (finCongr hSj)
  have hon : Orthonormal ℂ (fun r => (ob r : L2 D)) := by
    rw [orthonormal_iff_ite]
    intro r s
    exact orthonormal_iff_ite.mp ob.orthonormal r s
  refine ⟨fun r => (ob r : L2 D), hon, fun a => ?_⟩
  set v := ∑ r, a r • (ob r : L2 D)
  have hvS : v ∈ S := S.sum_mem fun r _ => S.smul_mem _ (ob r).2
  have hn : ‖v‖ ^ 2 = ∑ r, ‖a r‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, hon.inner_sum]
    simp only [Complex.conj_mul']
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    norm_cast
  by_cases hv : v = 0
  · rw [hv]
    refine le_trans (iInf₂_le 0 isWeakGradient_zero) ?_
    simp
  · have hr : rayleigh D v ≤ neumannEigenvalue D j + ENNReal.ofReal ε :=
      (le_iSup₂_of_le v hvS (le_iSup (fun _ : v ≠ 0 => rayleigh D v) hv)).trans hsup.le
    have hne : (‖v‖₊ : ENNReal) ^ 2 ≠ 0 := by simpa using hv
    have e1 : (‖v‖₊ : ENNReal) ^ 2 = ENNReal.ofReal (∑ r, ‖a r‖ ^ 2) := by
      rw [← hn, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, enorm_eq_nnnorm]
    unfold rayleigh at hr
    rw [ENNReal.div_le_iff hne (by simp), e1] at hr
    refine hr.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add ENNReal.toReal_nonneg hε.le,
      ENNReal.ofReal_toReal hμ]

/-- Almost-minimizing families: if `μ_j(Ω_n) < ∞`, there are `j + 1` functions in `H¹(Ω)`,
orthonormal for `m_n`, on whose span `q_n ≤ (μ_j(Ω_n) + ε) m_n`. -/
theorem exists_almostMinimizers (j n : ℕ)
    (hμ : neumannEigenvalue (A.map n '' Ω) j ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ (u : Fin (j + 1) → L2 Ω) (G : Fin (j + 1) → Fin 2 → L2 Ω),
      (∀ r, IsWeakGradient Ω (u r) (G r)) ∧
      (∀ r s, ∫ w in Ω, (bzDensity A n w : ℂ) * inner ℂ ((u r : ℂ → ℂ) w) ((u s : ℂ → ℂ) w) =
        if r = s then 1 else 0) ∧
      ∀ a : Fin (j + 1) → ℂ, gradForm Ω (P.coef n) (∑ r, a r • G r) ≤
        ((neumannEigenvalue (A.map n '' Ω) j).toReal + ε) * ∑ r, ‖a r‖ ^ 2 := by
  obtain ⟨e, he, hE⟩ := exists_orthonormal_energy_le (A.map n '' Ω) j hμ hε
  have hH : ∀ r, P.pull n (e r) ∈ H1 Ω := by
    intro r
    refine (P.pull_H1 n _).mp (mem_H1_of_neumannEnergy_ne_top ?_)
    have h1 := hE (Pi.single r 1)
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  choose G hG using hH
  refine ⟨fun r => P.pull n (e r), G, hG, fun r s => ?_, fun a => ?_⟩
  · rw [← orthonormal_iff_ite.mp he r s]
    exact (P.pull_inner n (e r) (e s)).symm
  · have hgrad : IsWeakGradient Ω (P.pull n (∑ r, a r • e r)) (∑ r, a r • G r) := by
      rw [map_sum]
      simp_rw [map_smul]
      exact IsWeakGradient.sum _ _ _ fun r _ => (hG r).smul (a r)
    have h := hE a
    rw [P.pull_energy n _ _ hgrad] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- Weak lower semicontinuity of the pulled-back forms (the last step of Lemma 10.13): if the
gradients `g_n` converge weakly to `Γ` and `q_{κ(n)}[g_n] ≤ β_n → β` with `κ(n) → ∞`, then
`∫_Ω |Γ|² ≤ β`. On the sets `F_N` outside the collars `C_m`, `m ≥ N`, the matrices `A_m` equal
`I`, and elsewhere they are positive. -/
theorem lsc_gradForm (hΩ : MeasurableSet Ω) (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (g : ℕ → Fin 2 → L2 Ω) (Γ : Fin 2 → L2 Ω)
    (hw : ∀ i z, Tendsto (fun n => inner ℂ z (g n i)) atTop (𝓝 (inner ℂ z (Γ i))))
    (β : ℕ → ℝ) (β₀ : ℝ) (hβ : Tendsto β atTop (𝓝 β₀))
    (hq : ∀ n, gradForm Ω (P.coef (κ n)) (g n) ≤ β n) :
    ∑ i, ‖Γ i‖ ^ 2 ≤ β₀ := by
  have hMp : ∀ m, ∀ᵐ w ∂(volume.restrict Ω), ∀ ξ : Fin 2 → ℂ,
      0 ≤ (coefSesq (P.coef m w) ξ ξ).re := fun m =>
    (P.coef_ellip m).mono fun w hw ξ =>
      le_trans (mul_nonneg P.ellip_pos.le (Finset.sum_nonneg fun i _ => sq_nonneg _)) (hw ξ)
  have hF : ∀ N, ∑ i, ∫ w in collarFree A N, ‖(Γ i : ℂ → ℂ) w‖ ^ 2 ∂(volume.restrict Ω) ≤ β₀ := by
    intro N
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h1 : ∀ i, ∀ᶠ n in atTop,
        ∫ w in collarFree A N, ‖(Γ i : ℂ → ℂ) w‖ ^ 2 ∂(volume.restrict Ω) - ε / 2 ≤
          ∫ w in collarFree A N, ‖(g n i : ℂ → ℂ) w‖ ^ 2 ∂(volume.restrict Ω) :=
      fun i => weak_lsc_restrict (hw i) _ (ε / 2) (by positivity)
    have h3 : ∀ᶠ n in atTop,
        ∑ i, ∫ w in collarFree A N, ‖(Γ i : ℂ → ℂ) w‖ ^ 2 ∂(volume.restrict Ω) - ε ≤ β n := by
      filter_upwards [h1 0, h1 1, hκ.eventually_ge_atTop N] with n hn0 hn1 hn2
      have hMF : ∀ w ∈ Ω, w ∈ collarFree A N → P.coef (κ n) w = 1 := by
        intro w hwΩ hwF
        refine P.coef_eq_one _ w hwΩ ?_
        simp only [collarFree, Set.mem_iInter] at hwF
        exact hwF (κ n) hn2
      have h := integral_restrict_le_gradForm (P.coef_meas (κ n)) (P.coef_bound (κ n))
        (hMp (κ n)) hΩ (measurableSet_collarFree A N) hMF (g n)
      simp only [Fin.sum_univ_two] at h ⊢
      linarith [hq n]
    have := ge_of_tendsto hβ h3
    linarith
  have hint : ∀ i, Integrable (fun w => ‖(Γ i : ℂ → ℂ) w‖ ^ 2) (volume.restrict Ω) := fun i =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hlim : Tendsto (fun N => ∑ i, ∫ w in collarFree A N, ‖(Γ i : ℂ → ℂ) w‖ ^ 2
      ∂(volume.restrict Ω)) atTop (𝓝 (∑ i, ‖Γ i‖ ^ 2)) := by
    refine tendsto_finset_sum _ fun i _ => ?_
    rw [← integral_norm_sq_eq]
    exact tendsto_setIntegral_collarFree A (hint i)
  exact le_of_tendsto' hlim hF

/-- The compactness step of Lemma 10.13: almost-minimizing families along a sequence of
indices tending to infinity have orthonormal limits in `L²(Ω)`, with `q_Ω ≤ B ‖·‖²` on their
span. -/
theorem limits_of_almostMinimizers (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (j : ℕ) (ψ : ℕ → ℕ) (hψ : Tendsto ψ atTop atTop)
    (u : ℕ → Fin (j + 1) → L2 Ω) (G : ℕ → Fin (j + 1) → Fin 2 → L2 Ω)
    (hG : ∀ n r, IsWeakGradient Ω (u n r) (G n r))
    (horth : ∀ n r s, ∫ w in Ω, (bzDensity A (ψ n) w : ℂ) *
      inner ℂ ((u n r : ℂ → ℂ) w) ((u n s : ℂ → ℂ) w) = if r = s then 1 else 0)
    (b : ℕ → ℝ) (B : ℝ) (hbB : Tendsto b atTop (𝓝 B))
    (hq : ∀ n (a : Fin (j + 1) → ℂ), gradForm Ω (P.coef (ψ n)) (∑ r, a r • G n r) ≤
      b n * ∑ r, ‖a r‖ ^ 2) :
    ∃ U : Fin (j + 1) → L2 Ω, Orthonormal ℂ U ∧ ∀ a : Fin (j + 1) → ℂ,
      neumannEnergy Ω (∑ r, a r • U r) ≤ ENNReal.ofReal (B * ∑ r, ‖a r‖ ^ 2) := by
  have hΩ : IsOpen Ω := hL.1.1
  set c := P.ellip
  have hc : 0 < c := P.ellip_pos
  -- uniform bounds in `H¹`
  have hmass : ∀ n r, weightedMass Ω (bzDensity A (ψ n)) (u n r) = 1 := by
    intro n r
    have e : ∫ w in Ω, (bzDensity A (ψ n) w : ℂ) *
        inner ℂ ((u n r : ℂ → ℂ) w) ((u n r : ℂ → ℂ) w) =
        ((weightedMass Ω (bzDensity A (ψ n)) (u n r) : ℝ) : ℂ) := by
      rw [weightedMass, ← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      simp only
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    have h := horth n r r
    rw [e, if_pos rfl] at h
    exact_mod_cast h
  have hub : ∀ n r, ‖u n r‖ ≤ Real.sqrt (1 / c) := by
    intro n r
    have h := weightedMass_ge (bzDensity_aestronglyMeasurable A (ψ n)) (bzDensity_bound hΩ A (ψ n))
      (P.density_ge (ψ n)) (u n r)
    rw [hmass] at h
    have h2 : ‖u n r‖ ^ 2 ≤ 1 / c := by rw [le_div_iff₀ hc]; linarith
    simpa using Real.abs_le_sqrt h2
  obtain ⟨Bm, hBm⟩ := hbB.bddAbove_range
  have hBm' : ∀ n, b n ≤ Bm := fun n => hBm ⟨n, rfl⟩
  have hGb : ∀ n r i, ‖G n r i‖ ≤ Real.sqrt (Bm / c) := by
    intro n r i
    have h1 := hq n (Pi.single r 1)
    have e1 : ∑ s, (Pi.single r (1 : ℂ) : Fin (j + 1) → ℂ) s • G n s = G n r := by
      rw [Finset.sum_eq_single r (fun s _ hs => by simp [hs]) (by simp)]
      simp
    have e2 : ∑ s, ‖(Pi.single r (1 : ℂ) : Fin (j + 1) → ℂ) s‖ ^ 2 = 1 := by
      rw [Finset.sum_eq_single r (fun s _ hs => by simp [hs]) (by simp)]
      simp
    rw [e1, e2, mul_one] at h1
    have h2 := ellip_le_gradForm (P.coef_meas (ψ n)) (P.coef_bound (ψ n)) (P.coef_ellip (ψ n))
      (G n r)
    have h3 : ‖G n r i‖ ^ 2 ≤ ∑ k, ‖G n r k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖G n r k‖ ^ 2) (fun k _ => sq_nonneg _)
        (Finset.mem_univ i)
    have h4 : ‖G n r i‖ ^ 2 ≤ Bm / c := by
      rw [le_div_iff₀ hc]
      nlinarith [hBm' n]
    simpa using Real.abs_le_sqrt h4
  set R := max (Real.sqrt (1 / c)) (Real.sqrt (Bm / c))
  -- a common subsequence
  let Pr : Fin (j + 1) ⊕ (Fin (j + 1) × Fin 2) → (ℕ → ℕ) → Prop := fun k θ =>
    Sum.elim (fun r => ∃ V, Tendsto (fun n => u (θ n) r) atTop (𝓝 V))
      (fun ri => ∃ V, ∀ z, Tendsto (fun n => inner ℂ z (G (θ n) ri.1 ri.2)) atTop
        (𝓝 (inner ℂ z V))) k
  obtain ⟨θ, hθ, hP⟩ := exists_common_subseq Pr
    (fun k θ θ' hk hθ' => by
      cases k with
      | inl r =>
        obtain ⟨V, hV⟩ := hk
        exact ⟨V, hV.comp hθ'.tendsto_atTop⟩
      | inr ri =>
        obtain ⟨V, hV⟩ := hk
        exact ⟨V, fun z => (hV z).comp hθ'.tendsto_atTop⟩)
    (fun k θ hθ => by
      cases k with
      | inl r =>
        obtain ⟨φ', hφ', V, hV⟩ := rellich_compact hb hL (fun n => u (θ n) r)
          (fun n => G (θ n) r) (fun n => hG (θ n) r) R (fun n => (hub _ r).trans (le_max_left _ _))
          (fun n i => (hGb _ r i).trans (le_max_right _ _))
        exact ⟨φ', hφ', V, hV⟩
      | inr ri =>
        obtain ⟨φ', hφ', V, hV⟩ := exists_weak_subseq (fun n => G (θ n) ri.1 ri.2) R
          (fun n => (hGb _ _ _).trans (le_max_right _ _))
        exact ⟨φ', hφ', V, hV⟩)
  choose U hU using fun r => hP (Sum.inl r)
  choose Γ hΓ using fun ri : Fin (j + 1) × Fin 2 => hP (Sum.inr ri)
  have hUG : ∀ r, IsWeakGradient Ω (U r) (fun i => Γ (r, i)) := fun r =>
    isWeakGradient_of_weak_tendsto (fun n => hG (θ n) r) (hU r) (fun i z => hΓ (r, i) z)
  have hψθ : Tendsto (fun n => ψ (θ n)) atTop atTop := hψ.comp hθ.tendsto_atTop
  refine ⟨U, ?_, fun a => ?_⟩
  · -- orthonormality of the limits
    rw [orthonormal_iff_ite]
    intro r s
    have h := tendsto_weighted_inner (fun n => bzDensity A (ψ (θ n))) ((A.lip : ℝ) ^ 2)
      (fun n => bzDensity_aestronglyMeasurable A _) (fun n => bzDensity_bound hΩ A _)
      (bzDensity_tendsto hΩ A hψθ) (hU r) (hU s)
    refine tendsto_nhds_unique h ?_
    simp_rw [horth]
    exact tendsto_const_nhds
  · -- the energy bound
    set Γa : Fin 2 → L2 Ω := ∑ r, a r • (fun i => Γ (r, i))
    have hV : IsWeakGradient Ω (∑ r, a r • U r) Γa :=
      IsWeakGradient.sum _ _ _ fun r _ => (hUG r).smul (a r)
    have hw : ∀ i z, Tendsto (fun n => inner ℂ z ((∑ r, a r • G (θ n) r) i)) atTop
        (𝓝 (inner ℂ z (Γa i))) := by
      intro i z
      simp only [Γa, Finset.sum_apply, Pi.smul_apply, inner_sum, inner_smul_right]
      exact tendsto_finset_sum _ fun r _ => (hΓ (r, i) z).const_mul (a r)
    have hlsc := P.lsc_gradForm hΩ.measurableSet (fun n => ψ (θ n)) hψθ
      (fun n => ∑ r, a r • G (θ n) r) Γa hw (fun n => b (θ n) * ∑ r, ‖a r‖ ^ 2)
      (B * ∑ r, ‖a r‖ ^ 2) ((hbB.comp hθ.tendsto_atTop).mul_const _) (fun n => hq (θ n) a)
    refine (iInf₂_le Γa hV).trans (le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hlsc))
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, enorm_eq_nnnorm]

include P in
/-- The compactness part of Lemma 10.13. -/
theorem limits (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) (j : ℕ) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (lam : ENNReal) (hlam : lam < ⊤)
    (h : Tendsto (fun n => neumannEigenvalue (A.map (φ n) '' Ω) j) atTop (𝓝 lam)) :
    ∃ u : Fin (j + 1) → L2 Ω, Orthonormal ℂ u ∧ ∀ a : Fin (j + 1) → ℂ,
      neumannEnergy Ω (∑ r, a r • u r) ≤ lam * ENNReal.ofReal (∑ r, ‖a r‖ ^ 2) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually (Iio_mem_nhds hlam))
  have hfin : ∀ n, neumannEigenvalue (A.map (φ (n + N)) '' Ω) j ≠ ⊤ := fun n =>
    (hN (n + N) (Nat.le_add_left N n)).ne
  choose u G hG horth hq using fun n =>
    P.exists_almostMinimizers j (φ (n + N)) (hfin n) (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  have hψ : Tendsto (fun n => φ (n + N)) atTop atTop :=
    hφ.tendsto_atTop.comp (tendsto_add_atTop_nat N)
  have hbB : Tendsto (fun n => (neumannEigenvalue (A.map (φ (n + N)) '' Ω) j).toReal +
      1 / ((n : ℝ) + 1)) atTop (𝓝 (lam.toReal + 0)) :=
    ((ENNReal.tendsto_toReal hlam.ne).comp (h.comp (tendsto_add_atTop_nat N))).add
      tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at hbB
  obtain ⟨U, hU, hE⟩ := P.limits_of_almostMinimizers hb hL j (fun n => φ (n + N)) hψ u G hG
    horth _ _ hbB hq
  refine ⟨U, hU, fun a => (hE a).trans (le_of_eq ?_)⟩
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hlam.ne]

end PullbackData

/-- Lemmas 10.10, 10.11 and the compactness part of Lemma 10.13, for the Ball–Zarnescu
approximation `Ω_n = f_n(Ω)`: with the pulled-back mass `m_n[u,u] = ∫_Ω ρ_n |u|²`,
`ρ_n = |det Df_n|` (`weightedMass`), there are pulled-back Neumann forms `q_n[u,u]` on `L²(Ω)`
(`q_n[u,u] = ∫_Ω ∇ū · A_n ∇u`) such that `μ_j(Ω_n)` obeys the min–max bound for `q_n / m_n` on
subspaces of `H¹(Ω)` (Lemma 10.10), `q_n → q_Ω` uniformly on unit spheres of finite-dimensional
subspaces of `H¹(Ω)` (Lemma 10.11), and along subsequences with convergent eigenvalues there are
orthonormal limits of the pulled-back eigenfunctions.
Proved from the pullback data `exists_pullbackData` (Lemmas 10.9–10.10). -/
theorem exists_pullbackForms {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (A : BallZarnescuApprox Ω) :
    ∃ formQ : ℕ → L2 Ω → ℝ,
      (∀ (j n : ℕ) (S : Submodule ℂ (L2 Ω)), Module.finrank ℂ S = j + 1 →
        (S : Set (L2 Ω)) ⊆ H1 Ω → neumannEigenvalue (A.map n '' Ω) j ≤
          ⨆ (u : L2 Ω) (_ : u ∈ S) (_ : ‖u‖ = 1), ENNReal.ofReal (formQ n u /
            weightedMass Ω (fun w => |(fderiv ℝ (A.map n) w).det|) u)) ∧
      (∀ S : Submodule ℂ (L2 Ω), FiniteDimensional ℂ S → (S : Set (L2 Ω)) ⊆ H1 Ω →
        TendstoUniformlyOn formQ (fun u => (neumannEnergy Ω u).toReal) atTop
          ((S : Set (L2 Ω)) ∩ Metric.sphere 0 1)) ∧
      (∀ (j : ℕ) (φ : ℕ → ℕ), StrictMono φ → ∀ lam : ENNReal, lam < ⊤ →
        Tendsto (fun n => neumannEigenvalue (A.map (φ n) '' Ω) j) atTop (𝓝 lam) →
        ∃ u : Fin (j + 1) → L2 Ω, Orthonormal ℂ u ∧ ∀ a : Fin (j + 1) → ℂ,
          neumannEnergy Ω (∑ r, a r • u r) ≤ lam * ENNReal.ofReal (∑ r, ‖a r‖ ^ 2)) := by
  obtain ⟨P⟩ := exists_pullbackData hL A
  exact ⟨P.formQ, fun j n S hS hSH => P.minmax hL.1.1 j n S hS hSH,
    fun S hS hSH => P.formQ_tendsto hL.1.1 S hS hSH, fun j φ hφ lam hlam h =>
      P.limits hb hL j φ hφ lam hlam h⟩

end PolyaNeumann

end
