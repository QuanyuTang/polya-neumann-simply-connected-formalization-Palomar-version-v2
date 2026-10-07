module

public import RequestProject.ReconBasic
public import RequestProject.BallZarnescu

/-!
# Density of smooth functions in `H¹` of a Lipschitz domain

For a bounded Lipschitz domain `Ω`, restrictions to `Ω` of smooth compactly supported functions
on `ℂ` are dense in `H¹(Ω)` (`exists_testFunction_approx`).

Proof. Let `f_n` be the Ball–Zarnescu maps: bi-Lipschitz homeomorphisms with `f_n(Ω̄) ⊂ Ω`, equal
to the identity off boundary collars `C_n` shrinking to `∂Ω`. For `v ∈ H¹(Ω)`, `v ∘ f_n` lies in
`H¹(U_n)` with `U_n = f_n⁻¹(Ω) ⊃ Ω̄` (bi-Lipschitz chain rule), so it is approximated on `Ω` by
mollifications cut off far away (`tendsto_approx_of_closure_subset`). Since `v ∘ f_n = v` off
`C_n`, the uniform bi-Lipschitz bounds give `v ∘ f_n → v` in `H¹(Ω)` (`tendsto_collar_bound`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ComplexConjugate Real NNReal ENNReal

noncomputable section

namespace PolyaNeumann

/-! ### Approximation of `H¹` functions defined on a neighbourhood of `Ω̄` -/

/-- The mollifier sequence with radii `1/(k+1)`. -/
def stdBump (k : ℕ) : ContDiffBump (0 : ℂ) :=
  ⟨1 / ((k : ℝ) + 1) / 2, 1 / ((k : ℝ) + 1), by positivity,
    by have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
       linarith⟩

lemma stdBump_rOut (k : ℕ) : (stdBump k).rOut = 1 / ((k : ℝ) + 1) := rfl

lemma tendsto_stdBump_rOut : Tendsto (fun k => (stdBump k).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- An `H¹` function on an open set `U ⊇ Ω̄` (`Ω` bounded) is approximated on `Ω` by test
functions on `ℂ`. -/
theorem tendsto_approx_of_closure_subset {Ω U : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hΩm : MeasurableSet Ω) (hU : IsOpen U) (hΩU : closure Ω ⊆ U) {w : L2 U} {G : Fin 2 → L2 U}
    (hG : IsWeakGradient U w G) :
    ∃ φ : ℕ → ℂ → ℂ, (∀ k, TestFunction univ (φ k)) ∧
      Tendsto (fun k => eLpNorm (fun z => φ k z - extZero U w z) 2 (volume.restrict Ω))
        atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun k => eLpNorm (fun z => fderiv ℝ (φ k) z (coordDir i) -
        extZero U (G i) z) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
  have hUm : MeasurableSet U := hU.measurableSet
  -- a uniform margin around `Ω̄` inside `U`
  have hcpt : IsCompact (closure Ω) := hb.isCompact_closure
  obtain ⟨δ, hδ, hδsub⟩ := hcpt.exists_cthickening_subset_open hU hΩU
  -- a cutoff equal to `1` near `Ω̄`
  obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : ℂ)
  set R' : ℝ := |R| + 1
  have hR' : 0 < R' := by positivity
  set χ : ContDiffBump (0 : ℂ) := ⟨R', R' + 1, hR', by linarith⟩
  have hχ1 : ∀ z ∈ ball (0 : ℂ) R', χ z = 1 := fun z hz =>
    χ.one_of_mem_closedBall (ball_subset_closedBall hz)
  have hΩball : closure Ω ⊆ ball (0 : ℂ) R' := by
    refine (closure_minimal hR isClosed_closedBall).trans fun z hz => ?_
    rw [mem_closedBall] at hz; rw [mem_ball]
    linarith [le_abs_self R]
  set V := extZero U w
  set Gx : Fin 2 → ℂ → ℂ := fun j => extZero U (G j)
  have hV : MemLp V 2 volume := memLp_extZero hUm w
  have hGx : ∀ j, MemLp (Gx j) 2 volume := fun j => memLp_extZero hUm (G j)
  set ψ : ℕ → ℂ → ℂ := fun k => mollify ((stdBump k).normed volume) V
  have hψs : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k) := fun k =>
    HasCompactSupport.contDiff_convolution_left _ ((stdBump k).hasCompactSupport_normed)
      ((stdBump k).contDiff_normed) (hV.locallyIntegrable one_le_two)
  set φ : ℕ → ℂ → ℂ := fun k z => ((χ z : ℝ) : ℂ) * ψ k z
  have hχs : ContDiff ℝ (⊤ : ℕ∞) (fun z => ((χ z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hφt : ∀ k, TestFunction univ (φ k) := fun k =>
    ⟨hχs.mul (hψs k), (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right,
      subset_univ _⟩
  -- on `Ω`, `φ k` agrees with `ψ k` near every point
  have hloc : ∀ k, ∀ z ∈ Ω, φ k =ᶠ[𝓝 z] ψ k := fun k z hz => by
    filter_upwards [isOpen_ball.mem_nhds (hΩball (subset_closure hz))] with y hy
    simp only [φ, hχ1 y hy, Complex.ofReal_one, one_mul]
  have hsq : ∀ {a : ℕ → ℝ≥0∞} {b : ℕ → ℝ≥0∞}, Tendsto b atTop (𝓝 0) → (∀ᶠ k in atTop, a k ≤ b k) →
      Tendsto a atTop (𝓝 0) := fun hb hab =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
      (Eventually.of_forall fun _ => zero_le) hab
  refine ⟨φ, hφt, ?_, fun i => ?_⟩
  · refine hsq (tendsto_mollify_L2 tendsto_stdBump_rOut hV) (Eventually.of_forall fun k => ?_)
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) (eLpNorm_mono_measure _ Measure.restrict_le_self)
    filter_upwards [ae_restrict_mem hΩm] with z hz
    simp only [Pi.sub_apply, (hloc k z hz).eq_of_nhds, ψ]
  · refine hsq (tendsto_mollify_L2 tendsto_stdBump_rOut (hGx i)) ?_
    filter_upwards [tendsto_stdBump_rOut.eventually (gt_mem_nhds hδ)] with k hk
    refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) (eLpNorm_mono_measure _ Measure.restrict_le_self)
    filter_upwards [ae_restrict_mem hΩm] with z hz
    have hball : closedBall z (stdBump k).rOut ⊆ U :=
      (closedBall_subset_closedBall hk.le).trans
        ((closedBall_subset_cthickening (subset_closure hz) δ).trans hδsub)
    simp only [Pi.sub_apply]
    rw [(hloc k z hz).fderiv_eq, fderiv_mollify_extZero hU hG (stdBump k) z hball i]

/-! ### Convergence of the Ball–Zarnescu pullbacks -/

section Collar

variable {Ω : Set ℂ} (A : BallZarnescuApprox Ω)

lemma BallZarnescuApprox.map_mem_collar {n : ℕ} {x : ℂ} (hx : x ∈ A.collar n) :
    A.map n x ∈ A.collar n := by
  by_contra h
  have h1 := A.eq_self n _ h
  have h2 : A.map n x = x := (A.map n).injective h1
  rw [h2] at h
  exact h hx

lemma eLpNorm_indicator_comp_le (hΩ : IsOpen Ω) (n : ℕ) (P : ℂ → ℂ)
    (hm : AEStronglyMeasurable ((A.collar n).indicator (fun x => P (A.map n x)))
      (volume.restrict Ω)) :
    eLpNorm ((A.collar n).indicator (fun x => P (A.map n x))) 2 (volume.restrict Ω) ≤
      A.lip * eLpNorm ((A.collar n).indicator P) 2 (volume.restrict Ω) := by
  have hf : LipschitzOnWith A.lip (A.map n) Ω := (A.lipschitzWith n).lipschitzOnWith
  have hg : LipschitzOnWith A.lip (A.map n).symm (A.map n '' Ω) :=
    (A.lipschitzWith_symm n).lipschitzOnWith
  calc _ ≤ eLpNorm (fun x => (A.collar n).indicator P (A.map n x)) 2 (volume.restrict Ω) := by
        refine eLpNorm_mono hm fun x => ?_
        by_cases hx : x ∈ A.collar n
        · rw [indicator_of_mem hx, indicator_of_mem (A.map_mem_collar hx)]
        · rw [indicator_of_notMem hx, norm_zero]; exact norm_nonneg _
    _ ≤ A.lip * eLpNorm ((A.collar n).indicator P) 2 (volume.restrict (A.map n '' Ω)) :=
        eLpNorm_comp_bilip_le hΩ A.lip_pos hf hg _
    _ ≤ _ := by
        gcongr
        exact A.subset n

lemma tendsto_eLpNorm_indicator_collar (hΩm : MeasurableSet Ω) {P : ℂ → ℂ}
    (hP : MemLp P 2 (volume.restrict Ω)) :
    Tendsto (fun n => eLpNorm ((A.collar n).indicator P) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    (hP.aestronglyMeasurable.indicator (A.collar_closed _).measurableSet)]
  simp only [ENNReal.toReal_ofNat]
  have hlim : Tendsto (fun n => ∫⁻ x in Ω, ‖(A.collar n).indicator P x‖ₑ ^ (2:ℝ)) atTop
      (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := volume.restrict Ω)
      (F := fun n x => ‖(A.collar n).indicator P x‖ₑ ^ (2:ℝ)) (f := fun _ => 0)
      (fun x => ‖P x‖ₑ ^ (2:ℝ)) (fun n => ?_) (fun n => ?_) ?_ ?_
    · simpa using this
    · exact ((hP.aestronglyMeasurable.indicator (A.collar_closed n).measurableSet).enorm.pow_const _)
    · refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ A.collar n
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx]
    · have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hP
      simpa using this.ne
    · filter_upwards [ae_restrict_mem hΩm] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [A.collar_shrink x hx] with n hn
      simp [indicator_of_notMem hn]
  have h2 : Tendsto (fun t : ℝ≥0∞ => t ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 0) := by
    have := (ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0
    simpa [ENNReal.zero_rpow_of_pos] using this
  exact h2.comp hlim

lemma aestronglyMeasurable_comp_map (hΩ : IsOpen Ω) (n : ℕ) {P : ℂ → ℂ}
    (hP : MemLp P 2 (volume.restrict Ω)) :
    MemLp (fun x => P (A.map n x)) 2 (volume.restrict Ω) :=
  memLp_comp_bilip' hΩ A.lip_pos (A.lipschitzWith n).lipschitzOnWith
    (A.lipschitzWith_symm n).lipschitzOnWith
    (hP.mono_measure (Measure.restrict_mono (A.subset n) le_rfl))

/-- A function bounded on `Ω` by `c |P ∘ f_n| + |P|` on the collar `C_n` (and vanishing off it)
tends to `0` in `L²(Ω)`. -/
theorem tendsto_collar_bound (hΩ : IsOpen Ω) {P : ℂ → ℂ} (hP : MemLp P 2 (volume.restrict Ω))
    (c : ℝ≥0) {D : ℕ → ℂ → ℂ} (hDm : ∀ n, AEStronglyMeasurable (D n) (volume.restrict Ω))
    (hD : ∀ n, ∀ x ∈ Ω, ‖D n x‖ ≤ c * ‖(A.collar n).indicator (fun y => P (A.map n y)) x‖ +
      ‖(A.collar n).indicator P x‖) :
    Tendsto (fun n => eLpNorm (D n) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
  have hlim := tendsto_eLpNorm_indicator_collar A hΩ.measurableSet hP
  have hb : Tendsto (fun n => ((c * A.lip + 1 : ℝ≥0) : ℝ≥0∞) *
      eLpNorm ((A.collar n).indicator P) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.coe_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => zero_le)
    fun n => ?_
  set a := (A.collar n).indicator (fun y => P (A.map n y))
  set b := (A.collar n).indicator P
  have hm1 : AEStronglyMeasurable a (volume.restrict Ω) :=
    (aestronglyMeasurable_comp_map A hΩ n hP).aestronglyMeasurable.indicator (A.collar_closed n).measurableSet
  have hm2 : AEStronglyMeasurable b (volume.restrict Ω) :=
    hP.aestronglyMeasurable.indicator (A.collar_closed n).measurableSet
  calc eLpNorm (D n) 2 (volume.restrict Ω)
      ≤ eLpNorm (fun x => (c : ℝ) * ‖a x‖ + ‖b x‖) 2 (volume.restrict Ω) := by
        refine eLpNorm_mono_ae (hDm n) ?_
        filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
        refine (hD n x hx).trans (le_of_eq ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ eLpNorm (fun x => (c : ℝ) * ‖a x‖) 2 (volume.restrict Ω) +
          eLpNorm (fun x => ‖b x‖) 2 (volume.restrict Ω) :=
        eLpNorm_add_le one_le_two
    _ = c * eLpNorm a 2 (volume.restrict Ω) + eLpNorm b 2 (volume.restrict Ω) := by
        have e : (fun x => (c : ℝ) * ‖a x‖) = (c : ℝ) • (fun x => ‖a x‖) := rfl
        rw [e, eLpNorm_const_smul, eLpNorm_norm _ hm1, eLpNorm_norm _ hm2]
        simp [Real.enorm_eq_ofReal]
    _ ≤ c * (A.lip * eLpNorm b 2 (volume.restrict Ω)) + eLpNorm b 2 (volume.restrict Ω) := by
        gcongr
        exact eLpNorm_indicator_comp_le A hΩ n P hm1
    _ = _ := by
        push_cast
        ring

lemma sum_coordRe_coordDir_mul (i : Fin 2) (a : Fin 2 → ℂ) :
    ∑ j, (coordRe j (coordDir i) : ℂ) * a j = a i := by
  fin_cases i <;> simp [coordRe, coordDir, Fin.sum_univ_two]

lemma chainGrad_eq_of_notMem_collar {n : ℕ} {x : ℂ} (hx : x ∉ A.collar n)
    (G : Fin 2 → ℂ → ℂ) (i : Fin 2) : chainGrad (A.map n) G i x = G i x := by
  have hev : (A.map n : ℂ → ℂ) =ᶠ[𝓝 x] id := by
    filter_upwards [(A.collar_closed n).isOpen_compl.mem_nhds hx] with y hy
    exact A.eq_self n y hy
  have hfd : fderiv ℝ (A.map n) x = ContinuousLinearMap.id ℝ ℂ := by
    rw [hev.fderiv_eq, fderiv_id]
  simp only [chainGrad, hfd, ContinuousLinearMap.id_apply, A.eq_self n x hx]
  exact sum_coordRe_coordDir_mul i _

lemma norm_chainGrad_le (n : ℕ) (G : Fin 2 → ℂ → ℂ) (i : Fin 2) (x : ℂ) :
    ‖chainGrad (A.map n) G i x‖ ≤ A.lip * (‖G 0 (A.map n x)‖ + ‖G 1 (A.map n x)‖) := by
  have hd : ‖fderiv ℝ (A.map n) x‖ ≤ A.lip := norm_fderiv_le_of_lipschitz ℝ (A.lipschitzWith n)
  have hc : ∀ j, |coordRe j (fderiv ℝ (A.map n) x (coordDir i))| ≤ A.lip := fun j =>
    (abs_coordRe_le j _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
      (by rw [norm_coordDir, mul_one]; exact hd))
  simp only [chainGrad, Fin.sum_univ_two]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have h0 := mul_le_mul_of_nonneg_right (hc 0) (norm_nonneg (G 0 (A.map n x)))
  have h1 := mul_le_mul_of_nonneg_right (hc 1) (norm_nonneg (G 1 (A.map n x)))
  linarith

/-- `v ∘ f_n → v` in `L²(Ω)`. -/
lemma tendsto_comp_map (hΩ : IsOpen Ω) (u : L2 Ω) :
    Tendsto (fun n => eLpNorm (fun z => (u : ℂ → ℂ) (A.map n z) - u z) 2 (volume.restrict Ω))
      atTop (𝓝 0) := by
  refine tendsto_collar_bound A hΩ (Lp.memLp u) 1 (fun n =>
    (aestronglyMeasurable_comp_map A hΩ n (Lp.memLp u)).aestronglyMeasurable.sub
      (Lp.aestronglyMeasurable u)) fun n x _ => ?_
  by_cases hxC : x ∈ A.collar n
  · rw [indicator_of_mem hxC, indicator_of_mem hxC, NNReal.coe_one, one_mul]
    exact norm_sub_le _ _
  · rw [A.eq_self n x hxC, sub_self, norm_zero]; positivity

/-- The chain-rule gradients of `v ∘ f_n` converge to the gradient of `v` in `L²(Ω)`. -/
lemma tendsto_chainGrad_map (hΩ : IsOpen Ω) (g : Fin 2 → L2 Ω) (i : Fin 2) :
    Tendsto (fun n => eLpNorm (fun z => chainGrad (A.map n) (fun j => (g j : ℂ → ℂ)) i z -
      g i z) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
  set P : ℂ → ℂ := fun y => ((‖(g 0 : ℂ → ℂ) y‖ + ‖(g 1 : ℂ → ℂ) y‖ : ℝ) : ℂ)
  have hP : MemLp P 2 (volume.restrict Ω) :=
    ((Lp.memLp (g 0)).norm.add (Lp.memLp (g 1)).norm).ofReal
  have hPn : ∀ y, ‖P y‖ = ‖(g 0 : ℂ → ℂ) y‖ + ‖(g 1 : ℂ → ℂ) y‖ := fun y => by
    simp only [P, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  have hDm : ∀ n, AEStronglyMeasurable (fun z => chainGrad (A.map n) (fun j => (g j : ℂ → ℂ)) i z -
      g i z) (volume.restrict Ω) := fun n => by
    refine AEStronglyMeasurable.sub ?_ (Lp.aestronglyMeasurable _)
    unfold chainGrad
    refine Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
    refine AEStronglyMeasurable.mul ?_
      (aestronglyMeasurable_comp_map A hΩ n (Lp.memLp (g j))).aestronglyMeasurable
    have hc : Measurable (coordRe j) := by
      fin_cases j
      · exact Complex.measurable_re
      · exact Complex.measurable_im
    exact (Complex.measurable_ofReal.comp
      (hc.comp (measurable_fderiv_apply_const ℝ _ _))).aestronglyMeasurable
  refine tendsto_collar_bound A hΩ hP A.lip hDm fun n x _ => ?_
  by_cases hxC : x ∈ A.collar n
  · rw [indicator_of_mem hxC, indicator_of_mem hxC, hPn, hPn]
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_chainGrad_le A n (fun j => (g j : ℂ → ℂ)) i x
    have h2 : ‖(g i : ℂ → ℂ) x‖ ≤ ‖(g 0 : ℂ → ℂ) x‖ + ‖(g 1 : ℂ → ℂ) x‖ := by
      fin_cases i
      · simp
      · simp
    linarith
  · rw [chainGrad_eq_of_notMem_collar A hxC, sub_self, norm_zero]; positivity

end Collar

/-! ### Density -/

lemma exists_seq_of_forall_eps {μ : Measure ℂ} {u : ℂ → ℂ} {g : Fin 2 → ℂ → ℂ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ φ : ℂ → ℂ, TestFunction univ φ ∧
      eLpNorm (fun z => φ z - u z) 2 μ ≤ ENNReal.ofReal ε ∧
      ∀ i, eLpNorm (fun z => fderiv ℝ φ z (coordDir i) - g i z) 2 μ ≤ ENNReal.ofReal ε) :
    ∃ φ : ℕ → ℂ → ℂ, (∀ n, TestFunction univ (φ n)) ∧
      Tendsto (fun n => eLpNorm (fun z => φ n z - u z) 2 μ) atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (φ n) z (coordDir i) - g i z) 2 μ)
        atTop (𝓝 0) := by
  choose φ hφt hφ1 hφ2 using fun n : ℕ => h (1 / ((n : ℝ) + 1)) (by positivity)
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨φ, hφt, ?_, fun i => ?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) hφ1
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) fun n => hφ2 n i

/-- Smooth compactly supported functions on `ℂ` are dense in `H¹(Ω)` for a bounded Lipschitz
domain `Ω`. -/
theorem exists_testFunction_approx {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {u : L2 Ω} {g : Fin 2 → L2 Ω} (hg : IsWeakGradient Ω u g) :
    ∃ φ : ℕ → ℂ → ℂ, (∀ n, TestFunction univ (φ n)) ∧
      Tendsto (fun n => eLpNorm (fun z => φ n z - u z) 2 (volume.restrict Ω)) atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun n => eLpNorm (fun z => fderiv ℝ (φ n) z (coordDir i) - g i z) 2
        (volume.restrict Ω)) atTop (𝓝 0) := by
  refine exists_seq_of_forall_eps fun ε hε => ?_
  have hΩ : IsOpen Ω := hL.1.1
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  obtain ⟨A⟩ := exists_ballZarnescu hb hL
  have hε2 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨n, hn1, hn2⟩ : ∃ n, eLpNorm (fun z => (u : ℂ → ℂ) (A.map n z) - u z) 2
      (volume.restrict Ω) ≤ ENNReal.ofReal (ε / 2) ∧ ∀ i,
      eLpNorm (fun z => chainGrad (A.map n) (fun j => (g j : ℂ → ℂ)) i z - g i z) 2
        (volume.restrict Ω) ≤ ENNReal.ofReal (ε / 2) := by
    have h1 := (tendsto_comp_map A hΩ u).eventually (eventually_le_nhds hε2)
    have h2 := fun i => (tendsto_chainGrad_map A hΩ g i).eventually (eventually_le_nhds hε2)
    obtain ⟨n, hn⟩ := (h1.and ((h2 0).and (h2 1))).exists
    exact ⟨n, hn.1, fun i => by fin_cases i; exacts [hn.2.1, hn.2.2]⟩
  set f := A.map n
  set U := f ⁻¹' Ω with hUdef
  have hU : IsOpen U := hΩ.preimage f.continuous
  have hΩU : closure Ω ⊆ U := fun x hx => A.closure_subset n ⟨x, hx, rfl⟩
  have hΩU' : Ω ⊆ U := subset_closure.trans hΩU
  have himg : f '' U = Ω := f.image_preimage Ω
  have hf : LipschitzOnWith A.lip f U := (A.lipschitzWith n).lipschitzOnWith
  have hfs : LipschitzOnWith A.lip f.symm Ω := (A.lipschitzWith_symm n).lipschitzOnWith
  have hum : MemLp (fun x => (u : ℂ → ℂ) (f x)) 2 (volume.restrict U) :=
    memLp_comp_bilip' hU A.lip_pos hf (by rw [himg]; exact hfs) (by rw [himg]; exact Lp.memLp u)
  set w : L2 U := hum.toLp _
  obtain ⟨G, hG, hGe⟩ := exists_isWeakGradient_comp_bilip himg hU A.lip_pos hf hfs hg
    hum.coeFn_toLp
  obtain ⟨φ, hφt, hφ1, hφ2⟩ := tendsto_approx_of_closure_subset hb hΩm hU hΩU hG
  obtain ⟨k, hk1, hk2⟩ : ∃ k, eLpNorm (fun z => φ k z - extZero U w z) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal (ε / 2) ∧ ∀ i, eLpNorm (fun z => fderiv ℝ (φ k) z (coordDir i) -
        extZero U (G i) z) 2 (volume.restrict Ω) ≤ ENNReal.ofReal (ε / 2) := by
    have h1 := hφ1.eventually (eventually_le_nhds hε2)
    have h2 := fun i => (hφ2 i).eventually (eventually_le_nhds hε2)
    obtain ⟨k, hk⟩ := (h1.and ((h2 0).and (h2 1))).exists
    exact ⟨k, hk.1, fun i => by fin_cases i; exacts [hk.2.1, hk.2.2]⟩
  have hsum : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf
  have hrestr : volume.restrict Ω ≤ volume.restrict U := Measure.restrict_mono hΩU' le_rfl
  refine ⟨φ k, hφt k, ?_, fun i => ?_⟩
  · have hae : (fun z => φ k z - (u : ℂ → ℂ) z) =ᵐ[volume.restrict Ω]
        (fun z => φ k z - extZero U w z) + (fun z => (u : ℂ → ℂ) (f z) - u z) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hΩU' hum.coeFn_toLp,
        ae_restrict_mem hΩm] with z hz hzΩ
      simp only [Pi.add_apply, extZero, indicator_of_mem (hΩU' hzΩ), w, hz]; ring
    rw [eLpNorm_congr_ae hae]
    exact (eLpNorm_add_le one_le_two).trans ((add_le_add hk1 hn1).trans hsum.le)
  · have hae : (fun z => fderiv ℝ (φ k) z (coordDir i) - (g i : ℂ → ℂ) z) =ᵐ[volume.restrict Ω]
        (fun z => fderiv ℝ (φ k) z (coordDir i) - extZero U (G i) z) +
          (fun z => chainGrad f (fun j => (g j : ℂ → ℂ)) i z - g i z) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hΩU' (hGe i),
        ae_restrict_mem hΩm] with z hz hzΩ
      simp only [Pi.add_apply, extZero, indicator_of_mem (hΩU' hzΩ), hz]; ring
    rw [eLpNorm_congr_ae hae]
    exact (eLpNorm_add_le one_le_two).trans ((add_le_add (hk2 i) (hn2 i)).trans hsum.le)

end PolyaNeumann
