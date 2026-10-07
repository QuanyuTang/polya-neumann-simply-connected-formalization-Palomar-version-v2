module

public import RequestProject.Finite
public import RequestProject.CurveContinuity

/-!
# Smooth approximation and the limiting inequality (Lemmas 10.11–10.14, Theorem 10.15)

This file formalizes the limiting part of Section 10 of the paper, with the analytic inputs
coming from the approximation (External theorem BZ, Lemmas 10.9–10.10, Rellich compactness)
as explicit hypotheses.

* **Lemma 10.11 (uniform convergence on a finite-dimensional space)**
  `tendstoUniformlyOn_sesq_of_basis`: sesquilinear forms on a finite-dimensional space that
  converge on every pair of basis vectors converge uniformly on bounded sets (on the diagonal).
* **Lemma 10.12 (upper limit of eigenvalues)** `limsup_le_neumannEigenvalue`: if `μ_j(Ω_n)` is
  bounded by the min–max quotient of forms `q_n / m_n` on `(j+1)`-dimensional subspaces of
  `H¹(Ω)` and `q_n → q_Ω`, `m_n → 1` uniformly on the unit sphere of every such subspace,
  then `limsup μ_j(Ω_n) ≤ μ_j(Ω)`.
* **Lemma 10.13 (convergence of eigenvalues and area)** `neumannEigenvalue_le_of_orthonormal`
  (the min–max step: `j+1` orthonormal functions with `q_Ω ≤ λ ‖·‖²` on their span give
  `μ_j(Ω) ≤ λ`), `tendsto_neumannEigenvalue` (`μ_j(Ω_n) → μ_j(Ω)`, with the compactness of
  Lemma 10.13 supplying the orthonormal limits as a hypothesis), and `tendsto_volume_of_density`
  (`|Ω_n| = ∫_Ω ρ_n → |Ω|` by dominated convergence).
* **Lemma 10.14 and Theorem 10.15 (the limit step)** `lipschitz_quantitative_of_approximation`:
  the quantitative smooth inequalities on approximating domains pass to the limit, using the
  continuity of the monodromy under uniform curve convergence.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Real

noncomputable section

namespace PolyaNeumann

/-! ### Lemma 10.11 -/

section FiniteForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℂ V] in
/-- Expansion of a sesquilinear form on the diagonal in a basis. -/
lemma sesq_apply_self_eq_sum_basis (b : Module.Basis ι ℂ V) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (u : V) :
    B u u = ∑ r, ∑ s, (starRingEnd ℂ) (b.equivFun u r) * b.equivFun u s * B (b r) (b s) := by
  conv_lhs => rw [← b.sum_equivFun u]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    RingHom.id_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
  ring

/-- **Lemma 10.11 (uniform convergence on a finite-dimensional space).** Sesquilinear forms
on a finite-dimensional space that converge on all pairs of basis vectors converge uniformly
(on the diagonal) on every bounded set, in particular on the unit sphere. -/
theorem tendstoUniformlyOn_sesq_of_basis (b : Module.Basis ι ℂ V)
    (Bn : ℕ → V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (h : ∀ r s, Tendsto (fun n => Bn n (b r) (b s)) atTop (𝓝 (B (b r) (b s))))
    {K : Set V} (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun n u => Bn n u u) (fun u => B u u) atTop K := by
  set cL : V →L[ℂ] (ι → ℂ) := LinearMap.toContinuousLinearMap b.equivFun.toLinearMap
  obtain ⟨R0, hR0⟩ := hK.exists_norm_le
  set R : ℝ := ‖cL‖ * max R0 0
  have hR : 0 ≤ R := by positivity
  -- the coefficients are bounded on `K`
  have hcoef : ∀ u ∈ K, ∀ r, ‖b.equivFun u r‖ ≤ R := fun u hu r =>
    calc ‖b.equivFun u r‖ ≤ ‖cL u‖ := norm_le_pi_norm (cL u) r
      _ ≤ ‖cL‖ * ‖u‖ := cL.le_opNorm u
      _ ≤ R := mul_le_mul_of_nonneg_left ((hR0 u hu).trans (le_max_left _ _)) (norm_nonneg _)
  set D : ℕ → ℝ := fun n => ∑ r, ∑ s, ‖Bn n (b r) (b s) - B (b r) (b s)‖
  have hD : Tendsto D atTop (𝓝 0) := by
    have : Tendsto D atTop (𝓝 (∑ r : ι, ∑ s : ι, (0 : ℝ))) :=
      tendsto_finset_sum _ fun r _ => tendsto_finset_sum _ fun s _ =>
        (tendsto_iff_norm_sub_tendsto_zero.mp (h r s))
    simpa using this
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε' : 0 < ε / (R ^ 2 + 1) := by positivity
  filter_upwards [(hD.eventually (gt_mem_nhds hε'))] with n hn u hu
  rw [dist_comm, dist_eq_norm, sesq_apply_self_eq_sum_basis b (Bn n),
    sesq_apply_self_eq_sum_basis b B, ← Finset.sum_sub_distrib]
  calc ‖∑ r, (∑ s, (starRingEnd ℂ) (b.equivFun u r) * b.equivFun u s * (Bn n) (b r) (b s) -
        ∑ s, (starRingEnd ℂ) (b.equivFun u r) * b.equivFun u s * B (b r) (b s))‖
      ≤ ∑ r, ∑ s, R ^ 2 * ‖Bn n (b r) (b s) - B (b r) (b s)‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
        rw [← Finset.sum_sub_distrib]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
        rw [← mul_sub, norm_mul, norm_mul, Complex.norm_conj, sq]
        gcongr
        · exact hcoef u hu r
        · exact hcoef u hu s
    _ = R ^ 2 * D n := by simp only [D, Finset.mul_sum]
    _ ≤ R ^ 2 * (ε / (R ^ 2 + 1)) := by gcongr
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

end FiniteForm

/-! ### Lemmas 10.12 and 10.13: eigenvalue convergence -/

section Eigen

variable {Ω : Set ℂ}

/-- A function of finite Neumann energy lies in `H¹(Ω)`. -/
lemma mem_H1_of_neumannEnergy_ne_top {u : L2 Ω} (h : neumannEnergy Ω u ≠ ⊤) : u ∈ H1 Ω := by
  by_contra hu
  apply h
  unfold neumannEnergy
  exact iInf₂_eq_top.mpr fun g hg => absurd ⟨g, hg⟩ hu

/-- **Lemma 10.12 (upper limit of eigenvalues).** Suppose that the numbers `μ n` (the
eigenvalues `μ_j(Ω_n)`) obey the min–max bound for the quotients `q_n[u,u] / m_n[u,u]` on
`(j+1)`-dimensional subspaces of `H¹(Ω)` (Lemma 10.10), and that on the unit sphere of every
such subspace `q_n → q_Ω` and `m_n → ‖·‖² = 1` uniformly (Lemma 10.11). Then
`limsup μ_j(Ω_n) ≤ μ_j(Ω)`. -/
theorem limsup_le_neumannEigenvalue (j : ℕ) (μ : ℕ → ENNReal) (q m : ℕ → L2 Ω → ℝ)
    (hmin : ∀ n (S : Submodule ℂ (L2 Ω)), Module.finrank ℂ S = j + 1 → (S : Set (L2 Ω)) ⊆ H1 Ω →
      μ n ≤ ⨆ (u : L2 Ω) (_ : u ∈ S) (_ : ‖u‖ = 1), ENNReal.ofReal (q n u / m n u))
    (hq : ∀ S : Submodule ℂ (L2 Ω), Module.finrank ℂ S = j + 1 → (S : Set (L2 Ω)) ⊆ H1 Ω →
      TendstoUniformlyOn q (fun u => (neumannEnergy Ω u).toReal) atTop
        ((S : Set (L2 Ω)) ∩ Metric.sphere 0 1))
    (hm : ∀ S : Submodule ℂ (L2 Ω), Module.finrank ℂ S = j + 1 → (S : Set (L2 Ω)) ⊆ H1 Ω →
      TendstoUniformlyOn m (fun _ => 1) atTop ((S : Set (L2 Ω)) ∩ Metric.sphere 0 1)) :
    limsup μ atTop ≤ neumannEigenvalue Ω j := by
  set μj := neumannEigenvalue Ω j with hμj
  rcases eq_or_ne μj ⊤ with htop | hfin
  · rw [htop]; exact le_top
  set M := μj.toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hδ' : (0 : ℝ) < δ := hδ
  set ε : ℝ := min (1 / 2) (δ / (M + δ + 2))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε2 : ε ≤ 1 / 2 := min_le_left _ _
  have hεδ : ε * (M + δ + 2) ≤ δ := by
    have : ε ≤ δ / (M + δ + 2) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity)] at this
  -- a subspace almost realizing the min–max value
  have hlt : μj < ENNReal.ofReal (M + ε) := by
    rw [ENNReal.ofReal_add hM hε.le, ENNReal.ofReal_toReal hfin]
    exact ENNReal.lt_add_right hfin (by simpa using hε)
  obtain ⟨S, hS, hSlt⟩ : ∃ S : Submodule ℂ (L2 Ω), Module.finrank ℂ S = j + 1 ∧
      (⨆ (u : L2 Ω) (_ : u ∈ S) (_ : u ≠ 0), rayleigh Ω u) < ENNReal.ofReal (M + ε) := by
    rw [hμj, neumannEigenvalue] at hlt
    obtain ⟨S, hS⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hS', hlt'⟩ := iInf_lt_iff.mp hS
    exact ⟨S, hS', hlt'⟩
  have hray : ∀ v ∈ S, v ≠ 0 → rayleigh Ω v < ENNReal.ofReal (M + ε) := fun v hv hv0 =>
    lt_of_le_of_lt (le_iSup₂_of_le v hv (le_iSup (fun _ : v ≠ 0 => rayleigh Ω v) hv0)) hSlt
  -- it lies in `H¹(Ω)`
  have hH1 : (S : Set (L2 Ω)) ⊆ H1 Ω := by
    intro v hv
    by_cases hv0 : v = 0
    · exact hv0 ▸ ⟨0, isWeakGradient_zero⟩
    · refine mem_H1_of_neumannEnergy_ne_top fun htop => ?_
      have := hray v hv hv0
      rw [rayleigh, htop, ENNReal.top_div_of_ne_top (by simp)] at this
      exact absurd this (by simp)
  have hunit : ∀ v ∈ S, ‖v‖ = 1 → (neumannEnergy Ω v).toReal ≤ M + ε := by
    intro v hv h1
    have hv0 : v ≠ 0 := by rintro rfl; simp at h1
    have := hray v hv hv0
    have hn : (‖v‖₊ : ENNReal) = 1 := by
      rw [← ENNReal.coe_one, ENNReal.coe_inj]; exact Subtype.ext h1
    rw [rayleigh, hn, one_pow, div_one] at this
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) this.le
  -- uniform convergence on its unit sphere
  have hq' := Metric.tendstoUniformlyOn_iff.mp (hq S hS hH1) ε hε
  have hm' := Metric.tendstoUniformlyOn_iff.mp (hm S hS hH1) ε hε
  have hbound : ∀ᶠ n in atTop, μ n ≤ μj + δ := by
    filter_upwards [hq', hm'] with n hqn hmn
    refine (hmin n S hS hH1).trans (iSup₂_le fun v hv => iSup_le fun h1 => ?_)
    have hvs : v ∈ (S : Set (L2 Ω)) ∩ Metric.sphere 0 1 := ⟨hv, by simpa using h1⟩
    have hqv : q n v < M + 2 * ε := by
      have h := hqn v hvs
      rw [Real.dist_eq] at h
      have := hunit v hv h1
      linarith [(abs_lt.mp h).1]
    have hmv : 1 - ε < m n v := by
      have h := hmn v hvs
      rw [Real.dist_eq] at h
      linarith [(abs_lt.mp h).2]
    have hmpos : 0 < m n v := by linarith
    have hquot : q n v / m n v ≤ M + δ := by
      rw [div_le_iff₀ hmpos]
      nlinarith
    calc ENNReal.ofReal (q n v / m n v) ≤ ENNReal.ofReal (M + δ) := ENNReal.ofReal_le_ofReal hquot
      _ = μj + δ := by
        rw [ENNReal.ofReal_add hM hδ'.le, ENNReal.ofReal_toReal hfin]; simp
  exact limsup_le_of_le (by isBoundedDefault) hbound

/-- **Lemma 10.13 (min–max step).** If `u_0, …, u_j` are orthonormal in `L²(Ω)` and
`q_Ω[∑ a_r u_r] ≤ λ ∑ |a_r|²` for all coefficients, then `μ_j(Ω) ≤ λ`. -/
theorem neumannEigenvalue_le_of_orthonormal (j : ℕ) (u : Fin (j + 1) → L2 Ω)
    (hu : Orthonormal ℂ u) (lam : ENNReal)
    (h : ∀ a : Fin (j + 1) → ℂ,
      neumannEnergy Ω (∑ r, a r • u r) ≤ lam * ENNReal.ofReal (∑ r, ‖a r‖ ^ 2)) :
    neumannEigenvalue Ω j ≤ lam := by
  have hS : Module.finrank ℂ (Submodule.span ℂ (Set.range u)) = j + 1 := by
    rw [finrank_span_eq_card hu.linearIndependent]; simp
  unfold neumannEigenvalue
  refine (iInf₂_le (Submodule.span ℂ (Set.range u)) hS).trans
    (iSup₂_le fun v hv => iSup_le fun hv0 => ?_)
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  have hn : ‖∑ r, a r • u r‖ ^ 2 = ∑ r, ‖a r‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, hu.inner_sum]
    simp only [Complex.conj_mul']
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    norm_cast
  have e1 : (‖∑ r, a r • u r‖₊ : ENNReal) ^ 2 = ENNReal.ofReal (∑ r, ‖a r‖ ^ 2) := by
    rw [← hn, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, enorm_eq_nnnorm]
  have hne : (‖∑ r, a r • u r‖₊ : ENNReal) ^ 2 ≠ 0 := by simpa using hv0
  unfold rayleigh
  rw [ENNReal.div_le_iff hne (by simp), e1]
  exact h a

/-- **Lemma 10.13 (convergence of eigenvalues).** Under the hypotheses of Lemma 10.12, and
the compactness statement of Lemma 10.13 (along every subsequence on which `μ_j(Ω_n)`
converges to a finite `λ` there are `j+1` orthonormal limits with `q_Ω ≤ λ ‖·‖²` on their
span), `μ_j(Ω_n) → μ_j(Ω)`. -/
theorem tendsto_neumannEigenvalue (j : ℕ) (μ : ℕ → ENNReal)
    (q m : ℕ → L2 Ω → ℝ)
    (hmin : ∀ n (S : Submodule ℂ (L2 Ω)), Module.finrank ℂ S = j + 1 → (S : Set (L2 Ω)) ⊆ H1 Ω →
      μ n ≤ ⨆ (u : L2 Ω) (_ : u ∈ S) (_ : ‖u‖ = 1), ENNReal.ofReal (q n u / m n u))
    (hq : ∀ S : Submodule ℂ (L2 Ω), Module.finrank ℂ S = j + 1 → (S : Set (L2 Ω)) ⊆ H1 Ω →
      TendstoUniformlyOn q (fun u => (neumannEnergy Ω u).toReal) atTop
        ((S : Set (L2 Ω)) ∩ Metric.sphere 0 1))
    (hm : ∀ S : Submodule ℂ (L2 Ω), Module.finrank ℂ S = j + 1 → (S : Set (L2 Ω)) ⊆ H1 Ω →
      TendstoUniformlyOn m (fun _ => 1) atTop ((S : Set (L2 Ω)) ∩ Metric.sphere 0 1))
    (hcpt : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ lam : ENNReal, lam < ⊤ →
      Tendsto (μ ∘ φ) atTop (𝓝 lam) →
      ∃ u : Fin (j + 1) → L2 Ω, Orthonormal ℂ u ∧ ∀ a : Fin (j + 1) → ℂ,
        neumannEnergy Ω (∑ r, a r • u r) ≤ lam * ENNReal.ofReal (∑ r, ‖a r‖ ^ 2)) :
    Tendsto μ atTop (𝓝 (neumannEigenvalue Ω j)) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ (limsup_le_neumannEigenvalue j μ q m hmin hq hm)
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  obtain ⟨φ, hφ, hφc⟩ :=
    extraction_of_frequently_atTop (frequently_lt_of_liminf_lt (by isBoundedDefault) hc1)
  obtain ⟨lam, ψ, hψ, hlim⟩ := SeqCompactSpace.tendsto_subseq (μ ∘ φ)
  have hlam : lam ≤ c := le_of_tendsto' hlim fun n => (hφc (ψ n)).le
  have hlamtop : lam < ⊤ := lt_of_le_of_lt hlam (lt_of_lt_of_le hc2 le_top)
  obtain ⟨u, hu, hE⟩ := hcpt (φ ∘ ψ) (hφ.comp hψ) lam hlamtop hlim
  exact absurd ((neumannEigenvalue_le_of_orthonormal j u hu lam hE).trans hlam) (not_le.mpr hc2)

/-- **Lemma 10.13 (convergence of area).** If `|Ω_n| = ∫_Ω ρ_n` (change of variables), the
densities `ρ_n` are uniformly bounded, a.e. strongly measurable, and `ρ_n → 1` a.e. on `Ω`, and
`|Ω| < ∞`, then `|Ω_n| → |Ω|`. -/
theorem tendsto_volume_of_density (hfin : volume Ω ≠ ⊤) (Ωs : ℕ → Set ℂ) (ρ : ℕ → ℂ → ℝ)
    (C : ℝ) (hmeas : ∀ n, AEStronglyMeasurable (ρ n) (volume.restrict Ω))
    (hbound : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), |ρ n w| ≤ C)
    (hlim : ∀ᵐ w ∂(volume.restrict Ω), Tendsto (fun n => ρ n w) atTop (𝓝 1))
    (hvol : ∀ n, volume (Ωs n) = ENNReal.ofReal (∫ w in Ω, ρ n w)) :
    Tendsto (fun n => volume (Ωs n)) atTop (𝓝 (volume Ω)) := by
  haveI : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hfin
  have h1 : Tendsto (fun n => ∫ w in Ω, ρ n w) atTop (𝓝 (∫ w in Ω, (1 : ℝ))) :=
    tendsto_integral_of_dominated_convergence (fun _ => C) hmeas (integrable_const C)
      (fun n => by simpa [Real.norm_eq_abs] using hbound n) hlim
  have h2 : (∫ w in Ω, (1 : ℝ)) = (volume Ω).toReal := by simp [Measure.real]
  rw [h2] at h1
  simp_rw [hvol]
  have := (ENNReal.continuous_ofReal.tendsto _).comp h1
  rwa [Function.comp_def, ENNReal.ofReal_toReal hfin] at this

end Eigen

/-! ### Lemma 10.14 and Theorem 10.15: the limit step -/

/-- **Lemma 10.14 and Theorem 10.15 (limit step).** Let `Ω_n` be domains with closed Lipschitz
boundary curves `γ_n` converging uniformly to the closed Lipschitz curve `γ` with bounded
lengths, and suppose each `Ω_n` satisfies the quantitative smooth eigenvalue inequality
(Corollary 9.8) `|Ω_n| μ_j(Ω_n) + 2 ‖U_{γ_n}(μ_j(Ω_n)) - I‖ ≤ 4π j`. If `|Ω_n| → |Ω|` and
`μ_j(Ω_n) → μ_j(Ω)` (Lemma 10.13), with both limits finite, then
`|Ω| μ_j(Ω) + 2 ‖U_γ(μ_j(Ω)) - I‖ ≤ 4π j`. -/
theorem lipschitz_quantitative_of_approximation {Ω : Set ℂ} (Ωs : ℕ → Set ℂ) (j : ℕ)
    {γ : ℝ → ℂ} {γs : ℕ → ℝ → ℂ} {K : NNReal} {Ks : ℕ → NNReal}
    (hK : LipschitzWith K γ) (hKs : ∀ n, LipschitzWith (Ks n) (γs n))
    (hclosed : γ (2 * π) = γ 0) (hclosed' : ∀ n, γs n (2 * π) = γs n 0)
    (hunif : TendstoUniformlyOn γs γ atTop (Set.Icc 0 (2 * π)))
    (hlen : ∃ B, ∀ n, ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (γs n) θ‖ ≤ B)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ (neumannEigenvalue Ω j).toReal W)
    {Ws : ℕ → ℝ → Ell2 →L[ℂ] Ell2}
    (hWs : ∀ n, IsTransport (γs n) (neumannEigenvalue (Ωs n) j).toReal (Ws n))
    (hsmooth : ∀ n, volume (Ωs n) * neumannEigenvalue (Ωs n) j +
      ENNReal.ofReal (2 * ‖monodromy (Ws n) - 1‖) ≤ ENNReal.ofReal (4 * π * j))
    (hvolfin : volume Ω ≠ ⊤) (hμfin : neumannEigenvalue Ω j ≠ ⊤)
    (hvol : Tendsto (fun n => volume (Ωs n)) atTop (𝓝 (volume Ω)))
    (hμ : Tendsto (fun n => neumannEigenvalue (Ωs n) j) atTop (𝓝 (neumannEigenvalue Ω j))) :
    volume Ω * neumannEigenvalue Ω j + ENNReal.ofReal (2 * ‖monodromy W - 1‖) ≤
      ENNReal.ofReal (4 * π * j) := by
  have hE := (ENNReal.tendsto_toReal hμfin).comp hμ
  have hU := monodromy_tendsto_of_tendstoUniformlyOn hK hKs hclosed hclosed' hunif hlen hE hW hWs
  have hN : Tendsto (fun n => ENNReal.ofReal (2 * ‖monodromy (Ws n) - 1‖)) atTop
      (𝓝 (ENNReal.ofReal (2 * ‖monodromy W - 1‖))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (((hU.sub_const 1).norm).const_mul 2)
  have hL := (ENNReal.Tendsto.mul hvol (Or.inr hμfin) hμ (Or.inr hvolfin)).add hN
  exact le_of_tendsto' hL hsmooth

end PolyaNeumann

end
