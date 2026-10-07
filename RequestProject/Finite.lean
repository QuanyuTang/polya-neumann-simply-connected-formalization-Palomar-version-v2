module

public import RequestProject.Spectrum

/-!
# Finiteness of the Neumann eigenvalues

For a nonempty open set `Ω`, every min–max value `μ_j(Ω)` is finite.  We exhibit a
`(j+1)`-dimensional space of smooth compactly supported bumps on which the Rayleigh
quotient is bounded.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ}

lemma TestFunction.memLp_fderiv {φ : ℂ → ℂ} (hφ : TestFunction Ω φ) (v : ℂ) :
    MemLp (fun w => fderiv ℝ φ w v) 2 (volume.restrict Ω) := by
  obtain ⟨hs, hc, -⟩ := hφ
  exact (((hs.continuous_fderiv (by simp)).clm_apply continuous_const :).memLp_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) v)).restrict Ω

lemma TestFunction.memLp {φ : ℂ → ℂ} (hφ : TestFunction Ω φ) :
    MemLp φ 2 (volume.restrict Ω) := by
  obtain ⟨hs, hc, -⟩ := hφ
  exact (hs.continuous.memLp_of_hasCompactSupport hc).restrict Ω

lemma integrable_L2_mul {f g : ℂ → ℂ} (hf : MemLp f 2 (volume.restrict Ω))
    (hg : MemLp g 2 (volume.restrict Ω)) :
    Integrable (fun w => f w * g w) (volume.restrict Ω) :=
  hf.integrable_mul hg

lemma IsWeakGradient.add {u v : L2 Ω} {g h : Fin 2 → L2 Ω} (hu : IsWeakGradient Ω u g)
    (hv : IsWeakGradient Ω v h) : IsWeakGradient Ω (u + v) (g + h) := by
  intro φ hφ i
  have e1 : (fun w => ((u + v : L2 Ω) : ℂ → ℂ) w * fderiv ℝ φ w (coordDir i))
      =ᵐ[volume.restrict Ω] fun w => (u : ℂ → ℂ) w * fderiv ℝ φ w (coordDir i) +
        (v : ℂ → ℂ) w * fderiv ℝ φ w (coordDir i) := by
    filter_upwards [Lp.coeFn_add u v] with w hw
    rw [hw, Pi.add_apply, add_mul]
  have e2 : (fun w => ((g + h) i : ℂ → ℂ) w * φ w)
      =ᵐ[volume.restrict Ω] fun w => (g i : ℂ → ℂ) w * φ w + (h i : ℂ → ℂ) w * φ w := by
    filter_upwards [Lp.coeFn_add (g i) (h i)] with w hw
    rw [Pi.add_apply, hw, Pi.add_apply, add_mul]
  rw [integral_congr_ae e1, integral_congr_ae e2,
    integral_add (integrable_L2_mul (Lp.memLp u) (hφ.memLp_fderiv _))
      (integrable_L2_mul (Lp.memLp v) (hφ.memLp_fderiv _)),
    integral_add (integrable_L2_mul (Lp.memLp (g i)) hφ.memLp)
      (integrable_L2_mul (Lp.memLp (h i)) hφ.memLp),
    hu φ hφ i, hv φ hφ i, neg_add]

lemma IsWeakGradient.smul {u : L2 Ω} {g : Fin 2 → L2 Ω} (c : ℂ) (hu : IsWeakGradient Ω u g) :
    IsWeakGradient Ω (c • u) (c • g) := by
  intro φ hφ i
  have e1 : (fun w => ((c • u : L2 Ω) : ℂ → ℂ) w * fderiv ℝ φ w (coordDir i))
      =ᵐ[volume.restrict Ω] fun w => c * ((u : ℂ → ℂ) w * fderiv ℝ φ w (coordDir i)) := by
    filter_upwards [Lp.coeFn_smul c u] with w hw
    rw [hw, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have e2 : (fun w => ((c • g) i : ℂ → ℂ) w * φ w)
      =ᵐ[volume.restrict Ω] fun w => c * ((g i : ℂ → ℂ) w * φ w) := by
    filter_upwards [Lp.coeFn_smul c (g i)] with w hw
    rw [Pi.smul_apply, hw, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_congr_ae e1, integral_congr_ae e2, integral_const_mul, integral_const_mul,
    hu φ hφ i, mul_neg]

lemma isWeakGradient_zero : IsWeakGradient Ω 0 0 := by
  intro φ hφ i
  have e1 : (fun w => ((0 : L2 Ω) : ℂ → ℂ) w * fderiv ℝ φ w (coordDir i))
      =ᵐ[volume.restrict Ω] fun _ => 0 := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict Ω)] with w hw
    rw [hw]; simp
  have e2 : (fun w => ((0 : Fin 2 → L2 Ω) i : ℂ → ℂ) w * φ w)
      =ᵐ[volume.restrict Ω] fun _ => 0 := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict Ω)] with w hw
    show ((0 : L2 Ω) : ℂ → ℂ) w * φ w = 0
    rw [hw]; simp
  rw [integral_congr_ae e1, integral_congr_ae e2]; simp

lemma IsWeakGradient.sum {ι : Type*} (s : Finset ι) (u : ι → L2 Ω) (g : ι → Fin 2 → L2 Ω)
    (h : ∀ k ∈ s, IsWeakGradient Ω (u k) (g k)) :
    IsWeakGradient Ω (∑ k ∈ s, u k) (∑ k ∈ s, g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isWeakGradient_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-- The classical gradient of a smooth compactly supported function is its weak gradient. -/
lemma isWeakGradient_of_smooth {f : ℂ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hu : MemLp f 2 (volume.restrict Ω))
    (hg : ∀ i, MemLp (fun w => fderiv ℝ f w (coordDir i)) 2 (volume.restrict Ω)) :
    IsWeakGradient Ω (hu.toLp f) (fun i => (hg i).toLp _) := by
  intro φ hφ i
  obtain ⟨hs, hφc, hsupp⟩ := hφ
  have e1' : (fun w => ((hu.toLp f : L2 Ω) : ℂ → ℂ) w * fderiv ℝ φ w (coordDir i))
      =ᵐ[volume.restrict Ω] fun w => f w * fderiv ℝ φ w (coordDir i) := by
    filter_upwards [hu.coeFn_toLp] with w hw; rw [hw]
  have e2' : (fun w => (((hg i).toLp _ : L2 Ω) : ℂ → ℂ) w * φ w)
      =ᵐ[volume.restrict Ω] fun w => fderiv ℝ f w (coordDir i) * φ w := by
    filter_upwards [(hg i).coeFn_toLp] with w hw; rw [hw]
  rw [integral_congr_ae e1', integral_congr_ae e2']
  have hout : ∀ w ∉ Ω, w ∉ tsupport φ := fun w hw h => hw (hsupp h)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => by
      simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) (hout w hw)]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => by
      simp [image_eq_zero_of_notMem_tsupport (hout w hw)])]
  have hfd : Continuous fun w => fderiv ℝ f w (coordDir i) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφd : Continuous fun w => fderiv ℝ φ w (coordDir i) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hfd.mul hs.continuous).integrable_of_hasCompactSupport (hφc.mul_left))
    ((hf.continuous.mul hφd).integrable_of_hasCompactSupport
      ((hφc.fderiv_apply (𝕜 := ℝ) _).mul_left))
    ((hf.continuous.mul hs.continuous).integrable_of_hasCompactSupport hφc.mul_left)
    (fun x _ => (hf.differentiable (by simp)) x) (fun x _ => (hs.differentiable (by simp)) x)

/-- If `u_0, …, u_j ∈ H¹(Ω)` are linearly independent in `L²(Ω)`, then `μ_j(Ω) < ∞`. -/
lemma neumannEigenvalue_lt_top_of_family (j : ℕ) (u : Fin (j + 1) → L2 Ω)
    (g : Fin (j + 1) → Fin 2 → L2 Ω) (hli : LinearIndependent ℂ u)
    (hg : ∀ k, IsWeakGradient Ω (u k) (g k)) : neumannEigenvalue Ω j < ⊤ := by
  set T := Fintype.linearCombination ℂ u
  set Gr := Fintype.linearCombination ℂ g
  have hinj : Function.Injective T := hli.fintypeLinearCombination_injective
  set e := LinearEquiv.ofInjective T hinj
  let L : LinearMap.range T →ₗ[ℂ] (Fin 2 → L2 Ω) := Gr ∘ₗ e.symm.toLinearMap
  let Lc := LinearMap.toContinuousLinearMap L
  have hrank : Module.finrank ℂ (LinearMap.range T) = j + 1 := by
    rw [← e.finrank_eq]; simp
  have hbound : ∀ v ∈ LinearMap.range T, v ≠ 0 →
      rayleigh Ω v ≤ 2 * (‖Lc‖₊ : ENNReal) ^ 2 := by
    intro v hv _
    obtain ⟨a, rfl⟩ := hv
    have hgrad : IsWeakGradient Ω (T a) (Gr a) := by
      simp only [T, Gr, Fintype.linearCombination_apply]
      exact IsWeakGradient.sum _ _ _ fun k _ => (hg k).smul (a k)
    have hL : Gr a = Lc ⟨T a, a, rfl⟩ := by
      change Gr a = Gr (e.symm ⟨T a, a, rfl⟩)
      congr 1
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      ext1; simp [e]
    have hnorm : ∀ i, ‖Gr a i‖ ≤ ‖Lc‖ * ‖T a‖ := by
      intro i
      refine (norm_le_pi_norm _ i).trans ?_
      rw [hL]
      exact (Lc.le_opNorm _).trans_eq (by rfl)
    have henergy : neumannEnergy Ω (T a) ≤ 2 * (‖Lc‖₊ : ENNReal) ^ 2 * (‖T a‖₊ : ENNReal) ^ 2 := by
      refine (iInf₂_le (Gr a) hgrad).trans ?_
      rw [Fin.sum_univ_two]
      have h' : ∀ i, (‖Gr a i‖₊ : ENNReal) ^ 2 ≤ (‖Lc‖₊ : ENNReal) ^ 2 * (‖T a‖₊ : ENNReal) ^ 2 := by
        intro i
        rw [← mul_pow]
        gcongr
        rw [← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
        simpa using hnorm i
      calc (‖Gr a 0‖₊ : ENNReal) ^ 2 + (‖Gr a 1‖₊ : ENNReal) ^ 2
          ≤ (‖Lc‖₊ : ENNReal) ^ 2 * (‖T a‖₊ : ENNReal) ^ 2 +
            (‖Lc‖₊ : ENNReal) ^ 2 * (‖T a‖₊ : ENNReal) ^ 2 := add_le_add (h' 0) (h' 1)
        _ = _ := by ring
    exact ENNReal.div_le_of_le_mul henergy
  calc neumannEigenvalue Ω j
      ≤ ⨆ (v : L2 Ω) (_ : v ∈ LinearMap.range T) (_ : v ≠ 0), rayleigh Ω v :=
        iInf₂_le (LinearMap.range T) hrank
    _ ≤ 2 * (‖Lc‖₊ : ENNReal) ^ 2 := iSup₂_le fun v hv => iSup_le fun hv0 => hbound v hv hv0
    _ < ⊤ := by
      apply ENNReal.mul_lt_top (by simp)
      exact ENNReal.pow_lt_top ENNReal.coe_lt_top

lemma coeFn_sum_smul {ι : Type*} (s : Finset ι) (a : ι → ℂ) (u : ι → L2 Ω) :
    ((∑ k ∈ s, a k • u k : L2 Ω) : ℂ → ℂ) =ᵐ[volume.restrict Ω]
      fun w => ∑ k ∈ s, a k * (u k : ℂ → ℂ) w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict Ω)] with w hw
    simpa using hw
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    filter_upwards [Lp.coeFn_add (a b • u b) (∑ k ∈ s, a k • u k), Lp.coeFn_smul (a b) (u b),
      ih] with w h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Finset.sum_insert hb, Pi.smul_apply, smul_eq_mul]

/-- Lemma 3.3 (finiteness): on a nonempty open set every Neumann min–max value is finite. -/
theorem neumannEigenvalue_lt_top_of_isOpen (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (j : ℕ) :
    neumannEigenvalue Ω j < ⊤ := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ z hz
  set n : ℕ := j + 1
  have hn : (0 : ℝ) < n := by positivity
  set δ : ℝ := r / n
  have hδ : 0 < δ := div_pos hr hn
  let c : Fin n → ℂ := fun k => z + (((k : ℕ) : ℝ) * δ : ℝ)
  let b : ∀ k, ContDiffBump (c k) := fun k => ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  let f : Fin n → ℂ → ℂ := fun k w => ((b k w : ℝ) : ℂ)
  have hf : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (f k) := fun k =>
    Complex.ofRealCLM.contDiff.comp (b k).contDiff
  have hfc : ∀ k, HasCompactSupport (f k) := fun k =>
    (b k).hasCompactSupport.comp_left Complex.ofReal_zero
  have hu : ∀ k, MemLp (f k) 2 (volume.restrict Ω) := fun k =>
    ((hf k).continuous.memLp_of_hasCompactSupport (hfc k)).restrict Ω
  have hg : ∀ k i, MemLp (fun w => fderiv ℝ (f k) w (coordDir i)) 2 (volume.restrict Ω) :=
    fun k i => ((((hf k).continuous_fderiv (by simp)).clm_apply continuous_const :
      Continuous fun w => fderiv ℝ (f k) w (coordDir i)).memLp_of_hasCompactSupport
        ((hfc k).fderiv_apply (𝕜 := ℝ) _)).restrict Ω
  -- values at the centres
  have hdist : ∀ k m : Fin n, dist (c m) (c k) = |((m : ℕ) : ℝ) - (k : ℕ)| * δ := by
    intro k m
    simp only [c, dist_eq_norm, add_sub_add_left_eq_sub, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    rw [← sub_mul, abs_mul, abs_of_pos hδ]
  have hval : ∀ k m : Fin n, f k (c m) = if k = m then 1 else 0 := by
    intro k m
    split_ifs with h
    · subst h
      simp only [f]
      rw [(b k).one_of_mem_closedBall (Metric.mem_closedBall_self (by
        change (0 : ℝ) ≤ δ / 4; positivity))]
      simp
    · simp only [f]
      rw [(b k).zero_of_le_dist]
      · simp
      · rw [hdist]
        change δ / 2 ≤ _
        have h1 : (1 : ℝ) ≤ |((m : ℕ) : ℝ) - (k : ℕ)| := by
          have hne : (m : ℕ) ≠ (k : ℕ) := fun h' => h (Fin.ext h'.symm)
          rcases Nat.lt_or_gt_of_ne hne with h' | h'
          · rw [abs_sub_comm, abs_of_pos (by
              have : ((m : ℕ) : ℝ) < (k : ℕ) := by exact_mod_cast h'
              linarith)]
            have : ((m : ℕ) : ℝ) + 1 ≤ (k : ℕ) := by exact_mod_cast h'
            linarith
          · rw [abs_of_pos (by
              have : ((k : ℕ) : ℝ) < (m : ℕ) := by exact_mod_cast h'
              linarith)]
            have : ((k : ℕ) : ℝ) + 1 ≤ (m : ℕ) := by exact_mod_cast h'
            linarith
        nlinarith
  have hcmem : ∀ m : Fin n, c m ∈ Ω := by
    intro m
    apply hball
    rw [Metric.mem_ball]
    simp only [c, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    have hm : ((m : ℕ) : ℝ) < n := by exact_mod_cast m.2
    calc ((m : ℕ) : ℝ) * δ < n * δ := by gcongr
      _ = r := by simp only [δ]; field_simp
  apply neumannEigenvalue_lt_top_of_family j (fun k => (hu k).toLp _)
    (fun k i => (hg k i).toLp _) _ (fun k => isWeakGradient_of_smooth (hf k) (hu k) (hg k))
  rw [Fintype.linearIndependent_iff]
  intro a ha m
  have hae := coeFn_sum_smul Finset.univ a (fun k => (hu k).toLp _)
  rw [ha] at hae
  have hall : ∀ᵐ w ∂(volume.restrict Ω), ∀ k, ((hu k).toLp (f k) : ℂ → ℂ) w = f k w :=
    ae_all_iff.mpr fun k => (hu k).coeFn_toLp
  have hF : (fun w => ∑ k, a k * f k w) =ᵐ[volume.restrict Ω] fun _ => 0 := by
    filter_upwards [hae, hall, Lp.coeFn_zero ℂ 2 (volume.restrict Ω)] with w h1 h2 h3
    have h4 := h1.symm.trans h3
    simp only [h2] at h4
    simpa using h4
  have hcont : Continuous fun w => ∑ k, a k * f k w :=
    continuous_finset_sum _ fun k _ => continuous_const.mul (hf k).continuous
  have heq := Measure.eqOn_open_of_ae_eq hF hΩ hcont.continuousOn continuousOn_const
    (hcmem m)
  simp only [hval] at heq
  simpa using heq

end PolyaNeumann

end
