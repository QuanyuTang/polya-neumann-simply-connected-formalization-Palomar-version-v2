module

public import RequestProject.HerglotzForm
public import RequestProject.PeriodicForm

/-!
# Transmutation of antiholomorphic polynomials (Lemmas 5.8, 5.9 on polynomials; Lemma 5.11)

For an antiholomorphic monomial `z̄^m` the normalized primitive is explicit,
`J^j z̄^m = m! z̄^{m+j} / (m+j)!`, so the transmutation series of the paper is
`𝒱_E z̄^m = ∑_j (-E/4)^j m! / (j! (m+j)!) z^j z̄^{m+j}` (`vekuaMonomial`).

Main results:
* `hasSum_herglotzWave_monoDensity`: the Herglotz wave with density `e^{-imφ}` is
  `∑_p α^p β^{p+m} / (p! (p+m)!)` with `α = -(ik/2) z`, `β = -(ik/2) z̄` (expansion of the plane
  wave as a product of two exponential series, integrated termwise);
* `vekuaMonomial_eq` (**Lemma 5.8**): for `k ≠ 0` the series converges and
  `𝒱_{k²} z̄^m = m! (-ik/2)^{-m} u_{e^{-im·}}`;
* `vekuaPoly_eq_herglotzWave`: the same for antiholomorphic polynomials `h = ∑ c_m z̄^m`, with a
  trigonometric-polynomial direction density; `herglotzVec_polyDensity_zero`: its initial vector
  at the origin is `(h(0)/√2) e₀`;
* `polynomial_transmutation_endpoint` (**Lemma 5.9 for polynomials**): if `γ(0) = 0`,
  `O_E^* 𝒥_E h = i (V_E^* - I) e₀ h(0)` and `(𝒱_E h) ∘ γ = h(0) O_E e₀ - i T_E 𝒥_E h`;
  in particular `𝒥_E h ∈ ker O_E^*` when `h(0) = 0` (`observationAdj_vekuaPolyConormal_eq_zero`);
* `periodicP_vekuaPoly` (**Lemmas 6.9–6.10 for polynomials**): with `n = (𝒱_E h) ∘ γ` (the
  Neumann-to-Dirichlet trace of `𝒥_E h` at a nonresonant energy) and `c_E ≠ 0`,
  `𝒫_E 𝒥_E h = 0` on `[0, L]` and `T_E^♯ 𝒥_E h = 0`; this discharges, for antiholomorphic
  polynomials, the hypotheses of `periodicP_radial` and `periodicP_of_observationAdj_eq_zero`;
* `kernel_cauchy_test` (**Lemma 5.11, compatibility part**): for bounded measurable `g` with
  `O_E^* g = 0`, the Cauchy data `(-i T_E g, g)` satisfy
  `∫₀^L (conj(g) h_a - conj(-i T_E g) g_a) = 0` for every Herglotz wave.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real Interval

noncomputable section

namespace PolyaNeumann

/-- `∫₀^{2π} e^{inφ} dφ = 2π [n = 0]` for `n ∈ ℤ`. -/
lemma integral_exp_int_mul_I (n : ℤ) :
    ∫ φ in (0 : ℝ)..(2 * π), Complex.exp ((n : ℂ) * φ * Complex.I) =
      if n = 0 then ((2 * π : ℝ) : ℂ) else 0 := by
  split_ifs with hn
  · subst hn; simp
  · have hc : (n : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
    have := integral_exp_mul_complex (a := 0) (b := 2 * π) hc
    simp only [show ∀ φ : ℝ, (n : ℂ) * φ * Complex.I = (n : ℂ) * Complex.I * φ from
      fun φ => by ring] at *
    rw [this]
    have h1 : Complex.exp ((n : ℂ) * Complex.I * ((2 * π : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I n]; congr 1; push_cast; ring
    rw [h1]; simp

/-- The plane wave as a product of two exponentials:
`e^{-ik Re(z e^{-iφ})} = exp(α e^{-iφ}) exp(β e^{iφ})` with `α = -(ik/2) z`, `β = -(ik/2) z̄`. -/
lemma planeWave_eq_exp_mul (k : ℝ) (z : ℂ) (φ : ℝ) :
    planeWave k z φ = Complex.exp (-(Complex.I * k / 2) * z * Complex.exp (-(φ * Complex.I))) *
      Complex.exp (-(Complex.I * k / 2) * conj z * Complex.exp (φ * Complex.I)) := by
  unfold planeWave
  rw [← Complex.exp_add]
  congr 1
  rw [Complex.re_eq_add_conj, map_mul, ← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring_nf

/-- The terms of the double expansion of `e^{-imφ} exp(α e^{-iφ}) exp(β e^{iφ})`. -/
def monoTerm (α β : ℂ) (m : ℕ) (pq : ℕ × ℕ) (φ : ℝ) : ℂ :=
  α ^ pq.1 * β ^ pq.2 / ((pq.1.factorial : ℂ) * pq.2.factorial) *
    Complex.exp ((((pq.2 : ℤ) - pq.1 - m : ℤ) : ℂ) * φ * Complex.I)

lemma hasSum_exp_series (w : ℂ) :
    HasSum (fun n : ℕ => w ^ n / (n.factorial : ℂ)) (Complex.exp w) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp w

lemma summable_norm_exp_series (w : ℂ) :
    Summable (fun n : ℕ => ‖w ^ n / (n.factorial : ℂ)‖) := by
  simpa [norm_pow] using Real.summable_pow_div_factorial ‖w‖

lemma hasSum_exp_mul_exp (u v : ℂ) : HasSum (fun x : ℕ × ℕ =>
      (u ^ x.1 / (x.1.factorial : ℂ)) * (v ^ x.2 / (x.2.factorial : ℂ)))
      (Complex.exp u * Complex.exp v) := by
  have hs := summable_mul_of_summable_norm (R := ℂ) (f := fun n : ℕ => u ^ n / (n.factorial : ℂ))
    (g := fun n : ℕ => v ^ n / (n.factorial : ℂ)) (summable_norm_exp_series u)
    (summable_norm_exp_series v)
  have ht := tsum_mul_tsum_of_summable_norm (R := ℂ)
    (f := fun n : ℕ => u ^ n / (n.factorial : ℂ)) (g := fun n : ℕ => v ^ n / (n.factorial : ℂ))
    (summable_norm_exp_series u) (summable_norm_exp_series v)
  rw [(hasSum_exp_series u).tsum_eq, (hasSum_exp_series v).tsum_eq] at ht
  rw [ht]
  exact hs.hasSum

lemma hasSum_monoTerm (α β : ℂ) (m : ℕ) (φ : ℝ) :
    HasSum (fun pq => monoTerm α β m pq φ)
      (Complex.exp (-((m : ℂ) * φ * Complex.I)) *
        (Complex.exp (α * Complex.exp (-(φ * Complex.I))) *
          Complex.exp (β * Complex.exp (φ * Complex.I)))) := by
  have h := (hasSum_exp_mul_exp (α * Complex.exp (-(φ * Complex.I)))
    (β * Complex.exp (φ * Complex.I))).mul_left (Complex.exp (-((m : ℂ) * φ * Complex.I)))
  convert h using 1
  funext pq
  obtain ⟨p, q⟩ := pq
  simp only [monoTerm, mul_pow, ← Complex.exp_nat_mul]
  have : Complex.exp ((((q : ℤ) - p - m : ℤ) : ℂ) * φ * Complex.I) =
      Complex.exp (-((m : ℂ) * φ * Complex.I)) * Complex.exp (p * -(φ * Complex.I)) *
        Complex.exp (q * (φ * Complex.I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [this]
  field_simp

lemma norm_monoTerm (α β : ℂ) (m : ℕ) (pq : ℕ × ℕ) (φ : ℝ) :
    ‖monoTerm α β m pq φ‖ =
      ‖α ^ pq.1 / (pq.1.factorial : ℂ)‖ * ‖β ^ pq.2 / (pq.2.factorial : ℂ)‖ := by
  rw [monoTerm, norm_mul, show (((((pq.2 : ℤ) - pq.1 - m : ℤ) : ℂ) * φ * Complex.I)) =
      ((((pq.2 : ℤ) - pq.1 - m : ℤ) * φ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one, mul_div_mul_comm, norm_mul]

lemma integral_monoTerm (α β : ℂ) (m : ℕ) (pq : ℕ × ℕ) :
    ∫ φ in (0 : ℝ)..(2 * π), monoTerm α β m pq φ =
      if pq.2 = pq.1 + m then α ^ pq.1 * β ^ pq.2 / ((pq.1.factorial : ℂ) * pq.2.factorial) *
        ((2 * π : ℝ) : ℂ) else 0 := by
  unfold monoTerm
  rw [intervalIntegral.integral_const_mul, integral_exp_int_mul_I]
  by_cases h : pq.2 = pq.1 + m
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h, mul_zero]

theorem hasSum_integral_monoTerm (α β : ℂ) (m : ℕ) :
    HasSum (fun pq => ∫ φ in (0 : ℝ)..(2 * π), monoTerm α β m pq φ)
      (∫ φ in (0 : ℝ)..(2 * π), Complex.exp (-((m : ℂ) * φ * Complex.I)) *
        (Complex.exp (α * Complex.exp (-(φ * Complex.I))) *
          Complex.exp (β * Complex.exp (φ * Complex.I)))) := by
  have hb : Summable (fun pq : ℕ × ℕ =>
      ‖α ^ pq.1 / (pq.1.factorial : ℂ)‖ * ‖β ^ pq.2 / (pq.2.factorial : ℂ)‖) :=
    summable_mul_of_summable_norm (R := ℝ) (f := fun n : ℕ => ‖α ^ n / (n.factorial : ℂ)‖)
      (g := fun n : ℕ => ‖β ^ n / (n.factorial : ℂ)‖)
      (by simpa using summable_norm_exp_series α) (by simpa using summable_norm_exp_series β)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun pq _ => ‖α ^ pq.1 / (pq.1.factorial : ℂ)‖ * ‖β ^ pq.2 / (pq.2.factorial : ℂ)‖)
    (fun pq => ?_) (fun pq => Eventually.of_forall fun φ _ => (norm_monoTerm α β m pq φ).le)
    (Eventually.of_forall fun φ _ => hb) intervalIntegrable_const
    (Eventually.of_forall fun φ _ => hasSum_monoTerm α β m φ)
  unfold monoTerm
  exact (Continuous.aestronglyMeasurable (by fun_prop))

/-- The monomial direction density `φ ↦ e^{-imφ}`. -/
def monoDensity (m : ℕ) (φ : ℝ) : ℂ := Complex.exp (-((m : ℂ) * φ * Complex.I))

/-- **Herglotz wave of a monomial density.** With `α = -(ik/2) z` and `β = -(ik/2) z̄`,
`u_{e^{-im·}}(z) = ∑_{p ≥ 0} α^p β^{p+m} / (p! (p+m)!)`. -/
theorem hasSum_herglotzWave_monoDensity (k : ℝ) (m : ℕ) (z : ℂ) :
    HasSum (fun p : ℕ => (-(Complex.I * k / 2) * z) ^ p * (-(Complex.I * k / 2) * conj z) ^ (p + m) /
      ((p.factorial : ℂ) * (p + m).factorial)) (herglotzWave k (monoDensity m) z) := by
  set α := -(Complex.I * k / 2) * z
  set β := -(Complex.I * k / 2) * conj z
  have h := (hasSum_integral_monoTerm α β m).mul_left ((2 * π : ℝ) : ℂ)⁻¹
  have hw : herglotzWave k (monoDensity m) z = ((2 * π : ℝ) : ℂ)⁻¹ *
      ∫ φ in (0 : ℝ)..(2 * π), Complex.exp (-((m : ℂ) * φ * Complex.I)) *
        (Complex.exp (α * Complex.exp (-(φ * Complex.I))) *
          Complex.exp (β * Complex.exp (φ * Complex.I))) := by
    unfold herglotzWave monoDensity
    simp only [planeWave_eq_exp_mul, α, β]
  rw [hw]
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  simp only [integral_monoTerm] at h
  rw [← (show Function.Injective (fun p : ℕ => (p, p + m)) from
    fun a b hab => (Prod.mk.inj hab).1).hasSum_iff] at h
  · convert h using 1
    funext p
    simp only [Function.comp, if_true]
    field_simp
  · rintro ⟨p, q⟩ hpq
    rw [if_neg, mul_zero]
    intro h'
    exact hpq ⟨p, by simp only at h'; rw [h']⟩

/-- The terms `(-E/4)^j m! / (j! (m+j)!) z^j z̄^{m+j}` of the transmutation `𝒱_E z̄^m`. -/
def vekuaMonoTerm (E : ℝ) (m : ℕ) (z : ℂ) (j : ℕ) : ℂ :=
  (-(E : ℂ) / 4) ^ j * m.factorial / ((j.factorial : ℂ) * (m + j).factorial) *
    z ^ j * conj z ^ (m + j)

/-- The transmutation of the antiholomorphic monomial `z̄^m`:
`𝒱_E z̄^m = ∑_{j ≥ 0} (-E/4)^j m! / (j! (m+j)!) z^j z̄^{m+j}` (the series of the paper with
`J^j z̄^m = m! z̄^{m+j} / (m+j)!`). -/
def vekuaMonomial (E : ℝ) (m : ℕ) (z : ℂ) : ℂ := ∑' j, vekuaMonoTerm E m z j

/-- **Lemma 5.8 (transmutation of antiholomorphic monomials).** For `k ≠ 0` the series
`𝒱_{k²} z̄^m` converges and equals `m! (-ik/2)^{-m}` times the Herglotz wave with direction
density `e^{-imφ}`. -/
theorem hasSum_vekuaMonoTerm {k : ℝ} (hk : k ≠ 0) (m : ℕ) (z : ℂ) :
    HasSum (vekuaMonoTerm (k ^ 2) m z)
      ((m.factorial : ℂ) * ((-(Complex.I * k / 2)) ^ m)⁻¹ * herglotzWave k (monoDensity m) z) := by
  have hw : (-(Complex.I * k / 2)) ≠ 0 := by
    have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    simp [this, Complex.I_ne_zero]
  convert (hasSum_herglotzWave_monoDensity k m z).mul_left
    ((m.factorial : ℂ) * ((-(Complex.I * k / 2)) ^ m)⁻¹) using 1
  funext j
  unfold vekuaMonoTerm
  have hsq : (-(Complex.I * k / 2)) ^ 2 = -((k ^ 2 : ℝ) : ℂ) / 4 := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [mul_pow, mul_pow, pow_add, ← hsq, ← pow_mul]
  field_simp
  ring_nf

theorem vekuaMonomial_eq {k : ℝ} (hk : k ≠ 0) (m : ℕ) (z : ℂ) :
    vekuaMonomial (k ^ 2) m z = m.factorial * ((-(Complex.I * k / 2)) ^ m)⁻¹ *
      herglotzWave k (monoDensity m) z := by
  exact (hasSum_vekuaMonoTerm hk m z).tsum_eq

/-- The Herglotz coefficients of a monomial density are Herglotz waves of monomial densities. -/
lemma herglotzCoeff_monoDensity (k : ℝ) (m n : ℕ) (z : ℂ) :
    herglotzCoeff k (monoDensity m) n z = herglotzWave k (monoDensity (m + n)) z := by
  unfold herglotzCoeff herglotzWave monoDensity
  congr 1
  refine intervalIntegral.integral_congr fun φ _ => ?_
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- At the origin the Herglotz wave of `e^{-imφ}` is `[m = 0]`. -/
lemma herglotzWave_monoDensity_zero (k : ℝ) (m : ℕ) :
    herglotzWave k (monoDensity m) 0 = if m = 0 then 1 else 0 := by
  have h := hasSum_herglotzWave_monoDensity k m 0
  refine h.unique ?_
  convert hasSum_single (f := fun p : ℕ => (-(Complex.I * k / 2) * (0 : ℂ)) ^ p *
    (-(Complex.I * k / 2) * conj (0 : ℂ)) ^ (p + m) /
      ((p.factorial : ℂ) * (p + m).factorial)) 0 ?_ using 1
  · split_ifs with hm <;> simp [hm]
  · intro p hp
    simp [hp]

/-! ### Antiholomorphic polynomials -/

/-- The antiholomorphic polynomial `h(z) = ∑_{m ∈ s} c_m z̄^m`. -/
def antiPoly (s : Finset ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ := ∑ m ∈ s, c m * conj z ^ m

/-- The transmutation `𝒱_E h = ∑_{m ∈ s} c_m 𝒱_E z̄^m` of an antiholomorphic polynomial. -/
def vekuaPoly (E : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ m ∈ s, c m * vekuaMonomial E m z

/-- The direction density `∑_{m ∈ s} c_m m! (-ik/2)^{-m} e^{-imφ}` whose Herglotz wave is
`𝒱_{k²} h`. -/
def polyDensity (k : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) (φ : ℝ) : ℂ :=
  ∑ m ∈ s, c m * ((m.factorial : ℂ) * ((-(Complex.I * k / 2)) ^ m)⁻¹) * monoDensity m φ

lemma continuous_monoDensity (m : ℕ) : Continuous (monoDensity m) := by
  unfold monoDensity; fun_prop

lemma continuous_polyDensity (k : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (polyDensity k s c) := by
  unfold polyDensity
  exact continuous_finset_sum _ fun m _ => continuous_const.mul (continuous_monoDensity m)

lemma isDirDensity_polyDensity (k : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) :
    IsDirDensity (polyDensity k s c) := by
  have hc := continuous_polyDensity k s c
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    hc.continuousOn
  refine MemLp.of_bound hc.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Eventually.of_forall fun φ hφ => hC φ (Ioc_subset_Icc_self hφ)

/-- Herglotz coefficients are linear in finite combinations of monomial densities. -/
lemma herglotzCoeff_finset_sum (k : ℝ) (s : Finset ℕ) (b : ℕ → ℂ) (n : ℤ) (z : ℂ) :
    herglotzCoeff k (fun φ => ∑ m ∈ s, b m * monoDensity m φ) n z =
      ∑ m ∈ s, b m * herglotzCoeff k (monoDensity m) n z := by
  unfold herglotzCoeff
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [intervalIntegral.integral_finset_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← mul_assoc, mul_comm (b m), mul_assoc, ← intervalIntegral.integral_const_mul (b m),
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun φ _ => by ring
  · intro m _
    exact (Continuous.intervalIntegrable (by
      have := continuous_monoDensity m
      have := continuous_planeWave k z
      fun_prop) _ _)

lemma polyDensity_eq (k : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) :
    polyDensity k s c = fun φ => ∑ m ∈ s,
      (c m * ((m.factorial : ℂ) * ((-(Complex.I * k / 2)) ^ m)⁻¹)) * monoDensity m φ := rfl

/-- **Lemma 5.8 for antiholomorphic polynomials.** For `k ≠ 0`, `𝒱_{k²} h` is the Herglotz wave
with the trigonometric-polynomial density `polyDensity k s c`. -/
theorem vekuaPoly_eq_herglotzWave {k : ℝ} (hk : k ≠ 0) (s : Finset ℕ) (c : ℕ → ℂ) :
    vekuaPoly (k ^ 2) s c = herglotzWave k (polyDensity k s c) := by
  funext z
  rw [herglotzWave_eq, polyDensity_eq, herglotzCoeff_finset_sum, vekuaPoly]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [vekuaMonomial_eq hk, ← herglotzWave_eq]
  ring

/-- The initial Herglotz vector of `𝒱_{k²} h` at the origin is `(h(0)/√2) e₀`. -/
theorem herglotzVec_polyDensity_zero {k : ℝ} (s : Finset ℕ) (c : ℕ → ℂ) :
    herglotzVec (isDirDensity_polyDensity k s c) k 0 =
      (antiPoly s c 0 / (Real.sqrt 2 : ℂ)) • basisVec 0 := by
  have hsum : ∀ n : ℕ, herglotzCoeff k (polyDensity k s c) n 0 =
      if n = 0 then antiPoly s c 0 else 0 := by
    intro n
    rw [polyDensity_eq, herglotzCoeff_finset_sum, antiPoly]
    split_ifs with hn
    · subst hn
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [herglotzCoeff_monoDensity, Nat.add_zero, herglotzWave_monoDensity_zero]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · simp [hm.ne', zero_pow hm.ne']
    · refine Finset.sum_eq_zero fun m _ => ?_
      rw [herglotzCoeff_monoDensity, herglotzWave_monoDensity_zero, if_neg (by omega), mul_zero]
  apply lp.ext
  funext n
  simp only [herglotzVec_apply, herglotzSeq, lp.coeFn_smul, Pi.smul_apply, basisVec,
    lp.single_apply, smul_eq_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := hsum 0
    push_cast at this
    simp [this]
  · have := hsum n
    simp only [if_neg hn.ne'] at this
    simp [hn.ne', this]

/-- The conormal trace `𝒥_E h = |γ'| ∂_ν (𝒱_E h) ∘ γ` of the transmutation of an antiholomorphic
polynomial (the derivative of `𝒱_E h` at `γ(θ)` in the direction `-i γ'(θ)`). -/
def vekuaPolyConormal (E : ℝ) (s : Finset ℕ) (c : ℕ → ℂ) (γ : ℝ → ℂ) (θ : ℝ) : ℂ :=
  fderiv ℝ (vekuaPoly E s c) (γ θ) (-(Complex.I * deriv γ θ))

lemma vekuaPoly_eq_herglotzWave_sqrt {E : ℝ} (hE : 0 < E) (s : Finset ℕ) (c : ℕ → ℂ) :
    vekuaPoly E s c = herglotzWave (Real.sqrt E) (polyDensity (Real.sqrt E) s c) := by
  have hk : Real.sqrt E ≠ 0 := (Real.sqrt_pos.mpr hE).ne'
  rw [← vekuaPoly_eq_herglotzWave hk, Real.sq_sqrt hE.le]

lemma vekuaPolyConormal_eq {E : ℝ} (hE : 0 < E) (s : Finset ℕ) (c : ℕ → ℂ) (γ : ℝ → ℂ) :
    vekuaPolyConormal E s c γ =
      herglotzConormal (Real.sqrt E) (polyDensity (Real.sqrt E) s c) γ := by
  funext θ
  rw [vekuaPolyConormal, herglotzConormal, vekuaPoly_eq_herglotzWave_sqrt hE]

/-- **Lemma 5.9 for antiholomorphic polynomials (transmutation endpoint identities).** Let `γ`
be a closed Lipschitz curve through the origin, `γ(0) = 0`, let `E > 0` and let `W` be the
transport at energy `E`, `V_E = W(L)`. For an antiholomorphic polynomial `h` with value
`h₀ = h(0)` at the origin,
`O_E^* 𝒥_E h = i (V_E^* - I) e₀ h₀` and `(𝒱_E h) ∘ γ = h₀ O_E e₀ - i T_E 𝒥_E h` on `[0, L]`. -/
theorem polynomial_transmutation_endpoint {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) (h0 : γ 0 = 0) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) (s : Finset ℕ) (c : ℕ → ℂ) :
    observationAdj W (vekuaPolyConormal E s c γ) =
        (Complex.I * antiPoly s c 0) •
          (ContinuousLinearMap.adjoint (W (2 * π)) - 1) (basisVec 0) ∧
      ∀ θ ∈ Icc 0 (2 * π), vekuaPoly E s c (γ θ) =
        antiPoly s c 0 * observation W (basisVec 0) θ -
          Complex.I * volterraOp W (vekuaPolyConormal E s c γ) θ := by
  set k := Real.sqrt E
  set a := polyDensity k s c
  have ha : IsDirDensity a := isDirDensity_polyDensity k s c
  have hy0 : herglotzVec ha k (γ 0) = (antiPoly s c 0 / (Real.sqrt 2 : ℂ)) • basisVec 0 := by
    rw [h0]; exact herglotzVec_polyDensity_zero s c
  have hr : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  rw [vekuaPolyConormal_eq hE, vekuaPoly_eq_herglotzWave_sqrt hE]
  refine ⟨?_, ?_⟩
  · rw [(herglotzForm_eq hK hclosed hW ha).1, hy0, map_smul, smul_smul]
    congr 1
    field_simp
  · obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable k hK
    have hy : ContinuousOn (fun s => herglotzVec ha k (γ s)) (Icc 0 (2 * π)) :=
      ((continuous_herglotzVec ha _).comp hK.continuous).continuousOn
    have ey := fun θ (_ : θ ∈ Icc 0 (2 * π)) => herglotz_driven ha hK E θ
    intro θ hθ
    have htr := driven_trace hK hW hgm hgB hy ey θ hθ
    have hw : herglotzWave k a (γ θ) =
        (Real.sqrt 2 : ℂ) * inner ℂ (basisVec 0) (herglotzVec ha k (γ θ)) := by
      simp only [basisVec, inner_single, herglotzVec_apply, herglotzSeq, if_true,
        herglotzWave_eq]
      field_simp
    rw [hw, htr, hy0]
    have hobs : observation W ((antiPoly s c 0 / (Real.sqrt 2 : ℂ)) • basisVec 0) θ =
        (antiPoly s c 0 / (Real.sqrt 2 : ℂ)) * observation W (basisVec 0) θ := by
      simp only [observation, map_smul, inner_smul_right]
    rw [hobs, ← mul_assoc, mul_div_cancel₀ _ hr]

/-- Lemma 5.14, easy inclusion, on polynomials: if `h(0) = 0` then `𝒥_E h ∈ ker O_E^*`. -/
theorem observationAdj_vekuaPolyConormal_eq_zero {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0) (h0 : γ 0 = 0) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {s : Finset ℕ} {c : ℕ → ℂ}
    (hc : antiPoly s c 0 = 0) :
    observationAdj W (vekuaPolyConormal E s c γ) = 0 := by
  rw [(polynomial_transmutation_endpoint hK hclosed h0 hE hW s c).1, hc, mul_zero, zero_smul]

/-- **Lemmas 6.9 and 6.10 for antiholomorphic polynomials (transmuted nullspace).** Let `γ` be a
closed Lipschitz curve with `γ(0) = 0`, `E > 0`, `W` the transport, and assume `c_E ≠ 0`. For every
antiholomorphic polynomial `h`, with Dirichlet trace `n = (𝒱_E h) ∘ γ` (which is `𝒩(E) 𝒥_E h` at a
nonresonant energy) and conormal trace `g = 𝒥_E h`, the corrected periodic form vanishes,
`𝒫_E g = 0` on `[0, L]`, and `T_E^♯ g = Π^c_E O_E^* g = 0`. -/
theorem periodicP_vekuaPoly {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) (h0 : γ 0 = 0) {E : ℝ} (hE : 0 < E)
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0) (s : Finset ℕ) (c : ℕ → ℂ) :
    (∀ θ ∈ Icc 0 (2 * π), periodicP W (fun θ => vekuaPoly E s c (γ θ))
      (vekuaPolyConormal E s c γ) θ = 0) ∧
      cutProj (cutC (W (2 * π)) (basisVec 0)) (observationAdj W (vekuaPolyConormal E s c γ)) =
        0 := by
  obtain ⟨hadj, hn⟩ := polynomial_transmutation_endpoint hK hclosed h0 hE hW s c
  set h₀ := antiPoly s c 0
  set g := vekuaPolyConormal E s c γ
  set C := cutC (W (2 * π)) (basisVec 0)
  set S := cutS (W (2 * π)) (basisVec 0)
  have hadj' : observationAdj W g = (Complex.I * h₀) • C := by
    rw [hadj]; rfl
  have hU := transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩
  have hBc := (cutB_transport hU (basisVec 0) hc).2
  refine ⟨fun θ hθ => ?_, ?_⟩
  · have hgm : AEStronglyMeasurable g volume ∧ ∃ B, ∀ s, ‖g s‖ ≤ B := by
      rw [show g = _ from vekuaPolyConormal_eq hE s c γ]
      exact herglotzConormal_bounded (isDirDensity_polyDensity _ s c).intervalIntegrable _ hK
    obtain ⟨hgm, B, hgB⟩ := hgm
    have hsum := volterraOp_add_adj hW.1 hgm hgB hθ
    rw [hadj'] at hsum
    have hs : S = (2 : ℂ) • basisVec 0 + C := by
      simp only [S, C, cutS, cutC]
      rw [two_smul]; abel
    rw [periodicP, periodicA, hn θ hθ, hadj', map_smul, hBc, smul_smul]
    simp only [observation, map_smul, inner_smul_right] at hsum ⊢
    rw [show cutS (W (2 * π)) (basisVec 0) = (2 : ℂ) • basisVec 0 + C from hs, map_add,
      map_smul, inner_add_right, inner_smul_right]
    linear_combination (-Complex.I) * hsum +
      2 * h₀ * inner ℂ (basisVec 0) (W θ (basisVec 0)) * Complex.I_sq
  · rw [hadj', map_smul, cutProj_eq_starProjection,
      Submodule.starProjection_orthogonal_apply_eq_zero (Submodule.mem_span_singleton_self _),
      smul_zero]

/-! ### The Cauchy test for the kernel of `O_E^*` (Lemma 5.11, compatibility part) -/

/-- The Volterra transform `T_E g` of a bounded measurable `g` is continuous on `[0, L]`. -/
lemma continuousOn_volterraOp {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B) :
    ContinuousOn (volterraOp W g) (Icc 0 (2 * π)) := by
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have h0 : (0 : ℝ) ∈ Icc 0 (2 * π) := ⟨le_rfl, hL⟩
  have hL' : (2 * π) ∈ Icc 0 (2 * π) := ⟨hL, le_rfl⟩
  have hi := intervalIntegrable_smul_of_continuousOn (continuousOn_adjoint_apply hW (basisVec 0))
    hg hgB h0 hL'
  have hP : ContinuousOn (fun θ => ∫ s in (0 : ℝ)..θ,
      g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)) (Icc 0 (2 * π)) := by
    have hI : IntegrableOn (fun s => g s • ContinuousLinearMap.adjoint (W s) (basisVec 0))
        (uIcc 0 (2 * π)) volume := by
      rw [uIcc_of_le hL]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hL).mp hi
    have := intervalIntegral.continuousOn_primitive_interval hI
    rwa [uIcc_of_le hL] at this
  have hc : ContinuousOn (fun θ => inner ℂ (basisVec 0) (W θ (∫ s in (0 : ℝ)..θ,
      g s • ContinuousLinearMap.adjoint (W s) (basisVec 0)))) (Icc 0 (2 * π)) :=
    (innerSL ℂ (basisVec 0)).continuous.comp_continuousOn (hW.clm_apply hP)
  refine hc.congr fun θ hθ => ?_
  beta_reduce
  rw [inner_transport_integral hW hg hgB θ h0 hθ]
  rfl

/-- **Lemma 5.11 (compatibility part).** Let `g` be bounded and measurable with `O_E^* g = 0`.
The driven solution `y' = C_E y - (i/√2) g e₀`, `y(0) = 0`, has trace `f₀ = √2 y₀ = -i T_E g`
(`driven_trace`), and the pair `(f₀, g)` passes the Cauchy test against every Herglotz wave:
`∫₀^L (conj(g) h_a - conj(f₀) g_a) = 0`, where `h_a = u_a ∘ γ` and `g_a` is the conormal trace. -/
theorem kernel_cauchy_test {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ s, ‖g s‖ ≤ B)
    (hO : observationAdj W g = 0) {a : ℝ → ℂ} (ha : IsDirDensity a) :
    ∫ θ in (0 : ℝ)..(2 * π), (conj (g θ) * herglotzWave (Real.sqrt E) a (γ θ) -
      conj (-(Complex.I * volterraOp W g θ)) * herglotzConormal (Real.sqrt E) a γ θ) = 0 := by
  set k := Real.sqrt E
  set ga := herglotzConormal k a γ
  set v := herglotzVec ha k (γ 0)
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  have h0 : (0 : ℝ) ∈ Icc 0 (2 * π) := ⟨le_rfl, hL⟩
  have hL' : (2 * π) ∈ Icc 0 (2 * π) := ⟨hL, le_rfl⟩
  obtain ⟨hgam, Ba, hgaB⟩ := herglotzConormal_bounded ha.intervalIntegrable k hK
  have hy : ContinuousOn (fun s => herglotzVec ha k (γ s)) (Icc 0 (2 * π)) :=
    ((continuous_herglotzVec ha _).comp hK.continuous).continuousOn
  have ey := fun θ (_ : θ ∈ Icc 0 (2 * π)) => herglotz_driven ha hK E θ
  have hr : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  -- the Dirichlet trace of the Herglotz wave
  have hha : ∀ θ ∈ Icc 0 (2 * π), herglotzWave k a (γ θ) =
      (Real.sqrt 2 : ℂ) * observation W v θ - Complex.I * volterraOp W ga θ := by
    intro θ hθ
    have htr := driven_trace hK hW hgam hgaB hy ey θ hθ
    have hw : herglotzWave k a (γ θ) =
        (Real.sqrt 2 : ℂ) * inner ℂ (basisVec 0) (herglotzVec ha k (γ θ)) := by
      simp only [basisVec, inner_single, herglotzVec_apply, herglotzSeq, if_true,
        herglotzWave_eq]
      field_simp
    rw [hw, htr]
  -- `T_E^* g = -T_E g` on `[0, L]`
  have hTT : ∀ θ ∈ Icc 0 (2 * π), volterraOpAdj W g θ = -volterraOp W g θ := by
    intro θ hθ
    have := volterraOp_add_adj hW.1 hg hgB hθ
    rw [hO, observation, map_zero, inner_zero_right] at this
    linear_combination this
  have hcg : AEStronglyMeasurable (fun s => conj (g s)) volume :=
    Complex.continuous_conj.comp_aestronglyMeasurable hg
  have hcgB : ∀ s, ‖conj (g s)‖ ≤ B := fun s => by rw [Complex.norm_conj]; exact hgB s
  have hOv : ContinuousOn (observation W v) (Icc 0 (2 * π)) :=
    (innerSL ℂ (basisVec 0)).continuous.comp_continuousOn (hW.1.clm_apply continuousOn_const)
  have hTga := continuousOn_volterraOp hW.1 hgam hgaB
  have hTg := continuousOn_volterraOp hW.1 hg hgB
  have i1 : IntervalIntegrable (fun θ => conj (g θ) * observation W v θ) volume 0 (2 * π) := by
    simpa only [smul_eq_mul] using intervalIntegrable_smul_of_continuousOn hOv hcg hcgB h0 hL'
  have i2 : IntervalIntegrable (fun θ => conj (g θ) * volterraOp W ga θ) volume 0 (2 * π) := by
    simpa only [smul_eq_mul] using intervalIntegrable_smul_of_continuousOn hTga hcg hcgB h0 hL'
  have i3 : IntervalIntegrable (fun θ => conj (volterraOp W g θ) * ga θ) volume 0 (2 * π) := by
    have := intervalIntegrable_smul_of_continuousOn
      (Complex.continuous_conj.comp_continuousOn hTg) hgam hgaB h0 hL'
    simpa only [smul_eq_mul, mul_comm, Function.comp] using this
  have hsplit : ∫ θ in (0 : ℝ)..(2 * π), (conj (g θ) * herglotzWave k a (γ θ) -
      conj (-(Complex.I * volterraOp W g θ)) * ga θ) =
      ∫ θ in (0 : ℝ)..(2 * π), ((Real.sqrt 2 : ℂ) * (conj (g θ) * observation W v θ) -
        Complex.I * (conj (g θ) * volterraOp W ga θ) -
          Complex.I * (conj (volterraOp W g θ) * ga θ)) := by
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le hL] at hθ
    rw [hha θ hθ, map_neg, map_mul, Complex.conj_I]
    ring
  rw [hsplit, intervalIntegral.integral_sub ((i1.const_mul _).sub (i2.const_mul _))
    (i3.const_mul _), intervalIntegral.integral_sub (i1.const_mul _) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, ← inner_observationAdj hW.1 hg hgB, hO, inner_zero_left,
    volterraOp_adjoint hW.1 hgam hgaB hg hgB]
  have h3 : ∫ θ in (0 : ℝ)..(2 * π), conj (volterraOp W g θ) * ga θ =
      -∫ θ in (0 : ℝ)..(2 * π), conj (volterraOpAdj W g θ) * ga θ := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le hL] at hθ
    rw [hTT θ hθ, map_neg]
    ring
  rw [h3]
  ring

end PolyaNeumann
