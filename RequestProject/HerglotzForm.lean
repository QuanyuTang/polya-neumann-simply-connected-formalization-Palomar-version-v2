module

public import RequestProject.FixedSpace
public import RequestProject.CutPhase

/-!
# The Herglotz form and the Cayley rank bound (Proposition 7.10, Lemma 8.7)

For a Herglotz wave `u_a` with conormal trace `g_a` and Dirichlet trace `h_a = u_a ∘ γ`, the
paper's boundary form `⟨g_a, 𝒜_E g_a⟩` with `𝒜_E = 2 𝒩(E) + i (T_E - T_E^*)` reads
(at a nonresonant energy, where `𝒩(E) g_a = h_a`)

  `herglotzForm W γ E a = Re ∫₀^L conj(g_a) (2 h_a + i (T_E - T_E^*) g_a)`.

Both Proposition 7.10 and Lemma 8.7 deduce a bound on the number of eigenphases of `U_E` with
large Cayley eigenvalue `cot(t/2)` from a lower bound on this form on a subspace of finite
codimension. We prove this deduction (`cayleyRankBound_of_herglotzForm_bound`):

* every vector of `ℓ²` is a Herglotz vector `y_a(z)` at any base point `z`
  (`exists_herglotzVec_eq`), and `a ↦ y_a(z)` is linear (`herglotzVec_sum`);
* the Herglotz form is `Re ⟨O_E^* g_a, √2 (y + V_E^* y)⟩` with `O_E^* g_a = √2 i (V_E^* - I) y`,
  `y = y_a(γ(0))` (`herglotzForm_eq`; the Cayley factorization of Lemma 4.17, written without
  inverting `I - V_E`); equivalently it is `-4 Im ⟨y, U_E y⟩` (`herglotzForm_eq_im`), so on
  Herglotz data the form only depends on the monodromy;
* on combinations of eigenvectors of `U_E = V_E^*` with eigenvalues `e^{it_k}` this is
  `-∑ |c_k|² cot(t_k/2)` (`re_inner_eigen_sum`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real InnerProductSpace

noncomputable section

namespace PolyaNeumann

/-- The Herglotz boundary form `Re ∫₀^L conj(g_a) (2 h_a + i (T_E - T_E^*) g_a)`, where
`g_a` is the conormal trace and `h_a = u_a ∘ γ` the Dirichlet trace of the Herglotz wave with
direction density `a` at wave number `√E`, and `T_E` is the Volterra operator of the transport
`W`. At a nonresonant energy this is `Re ⟨g_a, 𝒜_E g_a⟩`. -/
def herglotzForm (W : ℝ → Ell2 →L[ℂ] Ell2) (γ : ℝ → ℂ) (E : ℝ) (a : ℝ → ℂ) : ℝ :=
  (∫ θ in (0 : ℝ)..(2 * π), conj (herglotzConormal (Real.sqrt E) a γ θ) *
    (2 * herglotzWave (Real.sqrt E) a (γ θ) +
      Complex.I * (volterraOp W (herglotzConormal (Real.sqrt E) a γ) θ -
        volterraOpAdj W (herglotzConormal (Real.sqrt E) a γ) θ))).re

/-- Plane waves are multiplicative in the base point. -/
lemma planeWave_add (k : ℝ) (z w : ℂ) (φ : ℝ) :
    planeWave k (z + w) φ = planeWave k z φ * planeWave k w φ := by
  unfold planeWave
  rw [← Complex.exp_add]
  congr 1
  rw [add_mul, Complex.add_re]
  push_cast
  ring

/-- Moving the base point of the Herglotz coefficients into the density. -/
lemma herglotzCoeff_shift (k : ℝ) (a : ℝ → ℂ) (m : ℤ) (z : ℂ) :
    herglotzCoeff k (fun φ => a φ * planeWave k (-z) φ) m z = herglotzCoeff k a m 0 := by
  unfold herglotzCoeff
  congr 2
  funext φ
  have h := planeWave_add k (-z) z φ
  rw [neg_add_cancel] at h
  rw [mul_assoc (a φ), ← h]

/-- Every vector of `ℓ²` is the Herglotz vector `y_a(z)` of some `L²` density, at any base
point `z`. -/
theorem exists_herglotzVec_eq (k : ℝ) (z : ℂ) (v : Ell2) :
    ∃ (a : ℝ → ℂ) (ha : IsDirDensity a), herglotzVec ha k z = v := by
  obtain ⟨a₀, ha₀, hv⟩ := exists_herglotzVec_zero_eq k v
  have ha : IsDirDensity fun φ => a₀ φ * planeWave k (-z) φ :=
    ha₀.of_le (ha₀.aestronglyMeasurable.mul (continuous_planeWave k (-z)).aestronglyMeasurable)
      (Eventually.of_forall fun φ => by rw [norm_mul, norm_planeWave, mul_one])
  refine ⟨_, ha, ?_⟩
  rw [← hv]
  refine lp.ext (funext fun n => ?_)
  rw [herglotzVec_apply, herglotzVec_apply]
  unfold herglotzSeq
  simp only [herglotzCoeff_shift]

/-- Linearity of the Herglotz vector in the density. -/
theorem herglotzVec_sum {n : ℕ} (c : Fin n → ℂ) (a : Fin n → ℝ → ℂ)
    (ha : ∀ i, IsDirDensity (a i)) (hs : IsDirDensity (∑ i, c i • a i)) (k : ℝ) (z : ℂ) :
    herglotzVec hs k z = ∑ i, c i • herglotzVec (ha i) k z := by
  have hcoef : ∀ m : ℤ, herglotzCoeff k (∑ i, c i • a i) m z =
      ∑ i, c i * herglotzCoeff k (a i) m z := fun m => by
    unfold herglotzCoeff
    have hint : ∀ i ∈ Finset.univ, IntervalIntegrable (fun φ : ℝ => c i *
        (Complex.exp (-((m : ℂ) * φ * Complex.I)) * (a i φ * planeWave k z φ))) volume 0
          (2 * π) := fun i _ =>
      (intervalIntegrable_herglotz (ha i).intervalIntegrable k m z).const_mul _
    have heq : (fun φ : ℝ => Complex.exp (-((m : ℂ) * φ * Complex.I)) *
        ((∑ i, c i • a i) φ * planeWave k z φ)) = fun φ : ℝ => ∑ i, c i *
          (Complex.exp (-((m : ℂ) * φ * Complex.I)) * (a i φ * planeWave k z φ)) := by
      funext φ
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [heq, intervalIntegral.integral_finset_sum hint, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul]
    ring
  refine lp.ext (funext fun n => ?_)
  simp only [AddSubgroup.val_finset_sum]
  erw [Finset.sum_apply]
  rw [herglotzVec_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, herglotzVec_apply, smul_eq_mul]
  unfold herglotzSeq
  split_ifs
  · rw [hcoef, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => by ring
  · rw [hcoef]

/-- `e^{it} ≠ 1` for `0 < t < 2π`. -/
lemma exp_mul_I_ne_one {t : ℝ} (h0 : 0 < t) (h1 : t < 2 * π) :
    Complex.exp (t * Complex.I) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have htn : t = n * (2 * π) := by
    have := congrArg Complex.im hn
    simpa [Complex.mul_im] using this
  have hp := Real.pi_pos
  have hn1 : (0 : ℝ) < n := by
    by_contra hcon; push_neg at hcon; nlinarith
  have hn2 : (n : ℝ) < 1 := by
    by_contra hcon; push_neg at hcon; nlinarith
  have h1' : (0 : ℤ) < n := by exact_mod_cast hn1
  have h2' : n < (1 : ℤ) := by exact_mod_cast hn2
  omega

lemma sqrt_two_mul_I_ne_zero : ((Real.sqrt 2 : ℂ) * Complex.I) ≠ 0 :=
  mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne')
    Complex.I_ne_zero

/-- `cot(t/2) = i (e^{it} + 1)/(e^{it} - 1)` for `0 < t < 2π`. -/
lemma cot_half_eq {t : ℝ} (h0 : 0 < t) (h1 : t < 2 * π) :
    ((Real.cot (t / 2) : ℝ) : ℂ) = Complex.I * ((Complex.exp (t * Complex.I) + 1) /
      (Complex.exp (t * Complex.I) - 1)) := by
  have he1 := exp_mul_I_ne_one h0 h1
  set w : ℂ := Complex.exp (((t / 2 : ℝ) : ℂ) * Complex.I) with hwdef
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have hew : Complex.exp (t * Complex.I) = w * w := by
    rw [hwdef, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [hew] at he1 ⊢
  have hd2 : w * w - 1 ≠ 0 := sub_ne_zero.mpr he1
  have hd3 : w⁻¹ - w ≠ 0 := by
    rw [show w⁻¹ - w = -(w * w - 1) / w by field_simp; ring]
    exact div_ne_zero (neg_ne_zero.mpr hd2) hw0
  rw [Complex.ofReal_cot, Complex.cot_eq_cos_div_sin, Complex.cos, Complex.sin, ← hwdef,
      neg_mul, Complex.exp_neg, ← hwdef]
  rw [div_div_div_cancel_right₀ (two_ne_zero), eq_comm, mul_div_assoc',
    div_eq_div_iff hd2 (mul_ne_zero hd3 Complex.I_ne_zero)]
  field_simp
  rw [Complex.I_sq]
  ring

/-- The Herglotz form through the Cayley factorization (Lemma 4.17, without inverting
`I - V_E`): with `y = y_a(γ(0))`, `O_E^* g_a = √2 i (V_E^* - I) y` and the form is
`Re ⟨O_E^* g_a, √2 (y + V_E^* y)⟩`. -/
theorem herglotzForm_eq {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    observationAdj W (herglotzConormal (Real.sqrt E) a γ) =
        ((Real.sqrt 2 : ℂ) * Complex.I) • (ContinuousLinearMap.adjoint (W (2 * π)) - 1)
          (herglotzVec ha (Real.sqrt E) (γ 0)) ∧
      herglotzForm W γ E a =
        (⟪observationAdj W (herglotzConormal (Real.sqrt E) a γ),
          (Real.sqrt 2 : ℂ) • (herglotzVec ha (Real.sqrt E) (γ 0) +
            ContinuousLinearMap.adjoint (W (2 * π)) (herglotzVec ha (Real.sqrt E) (γ 0)))⟫_ℂ).re := by
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable (Real.sqrt E) hK
  have hy : ContinuousOn (fun s => herglotzVec ha (Real.sqrt E) (γ s)) (Icc 0 (2 * π)) :=
    ((continuous_herglotzVec ha _).comp hK.continuous).continuousOn
  have hper : herglotzVec ha (Real.sqrt E) (γ (2 * π)) =
      herglotzVec ha (Real.sqrt E) (γ 0) := by rw [hclosed]
  have ey := fun θ (_ : θ ∈ Icc 0 (2 * π)) => herglotz_driven ha hK E θ
  obtain ⟨-, hO⟩ := driven_endpoint hK hW hgm hgB hy ey hper
  refine ⟨hO, ?_⟩
  set g := herglotzConormal (Real.sqrt E) a γ with hgdef
  set V := W (2 * π) with hVdef
  set v := herglotzVec ha (Real.sqrt E) (γ 0) with hvdef
  have hpt : ∀ θ ∈ Icc 0 (2 * π), 2 * herglotzWave (Real.sqrt E) a (γ θ) +
      Complex.I * (volterraOp W g θ - volterraOpAdj W g θ) =
        observation W ((Real.sqrt 2 : ℂ) • (v + ContinuousLinearMap.adjoint V v)) θ := by
    intro θ hθ
    have htr := driven_trace hK hW hgm hgB hy ey θ hθ
    have hadd := volterraOp_add_adj hW.1 hgm hgB hθ
    rw [hO] at hadd
    have hr : (Real.sqrt 2 : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    have hw : herglotzWave (Real.sqrt E) a (γ θ) =
        (Real.sqrt 2 : ℂ) * inner ℂ (basisVec 0) (herglotzVec ha (Real.sqrt E) (γ θ)) := by
      simp only [basisVec, inner_single, herglotzVec_apply, herglotzSeq, if_true,
        herglotzWave_eq]
      field_simp
    rw [hw]
    simp only [observation, map_smul, map_add, map_sub, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, inner_smul_right, inner_add_right, inner_sub_right]
      at htr hadd ⊢
    linear_combination 2 * htr - Complex.I * hadd +
      ((Real.sqrt 2 : ℂ) * (inner ℂ (basisVec 0) ((W θ) v) -
        inner ℂ (basisVec 0) ((W θ) ((ContinuousLinearMap.adjoint V) v)))) * Complex.I_sq
  unfold herglotzForm
  rw [← hgdef]
  have hL : (0 : ℝ) ≤ 2 * π := by positivity
  rw [intervalIntegral.integral_congr (g := fun θ => conj (g θ) *
      observation W ((Real.sqrt 2 : ℂ) • (v + ContinuousLinearMap.adjoint V v)) θ)
      (fun θ hθ => by
        rw [uIcc_of_le hL] at hθ
        simp only [hpt θ hθ]),
    ← inner_observationAdj hW.1 hgm hgB]

/-- On Herglotz data the form depends only on the monodromy `U_E = V_E^*`:
`herglotzForm W γ E a = -4 Im ⟨y, U_E y⟩` with `y = y_a(γ(0))`. -/
theorem herglotzForm_eq_im {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W)
    {a : ℝ → ℂ} (ha : IsDirDensity a) :
    herglotzForm W γ E a = -4 * (⟪herglotzVec ha (Real.sqrt E) (γ 0),
      monodromy W (herglotzVec ha (Real.sqrt E) (γ 0))⟫_ℂ).im := by
  obtain ⟨hO, hF⟩ := herglotzForm_eq hK hclosed hW ha
  rw [hF, hO]
  set y := herglotzVec ha (Real.sqrt E) (γ 0)
  have hU : monodromy W ∈ unitary (Ell2 →L[ℂ] Ell2) := by
    rw [monodromy, ← ContinuousLinearMap.star_eq_adjoint]
    exact Unitary.star_mem (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩)
  have hnorm : ⟪monodromy W y, monodromy W y⟫_ℂ = ⟪y, y⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply,
      ← ContinuousLinearMap.star_eq_adjoint, (Unitary.mem_iff.mp hU).1,
      ContinuousLinearMap.one_apply]
  change (⟪((Real.sqrt 2 : ℂ) * Complex.I) • (monodromy W - 1) y,
    (Real.sqrt 2 : ℂ) • (y + monodromy W y)⟫_ℂ).re = _
  rw [inner_smul_left, inner_smul_right, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, inner_sub_left, inner_add_right, inner_add_right, hnorm,
    ← inner_conj_symm (monodromy W y) y]
  set w := ⟪y, monodromy W y⟫_ℂ
  have h2 : ((Real.sqrt 2 : ℂ)) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  have e : -(((Real.sqrt 2 : ℂ)) * Complex.I) * ((Real.sqrt 2 : ℂ) *
      (conj w + ⟪y, y⟫_ℂ - (⟪y, y⟫_ℂ + w))) = -(2 * Complex.I) * (conj w - w) := by
    linear_combination (-(Complex.I) * (conj w - w)) * h2
  rw [show ((Real.sqrt 2 : ℂ)) * -Complex.I = -(((Real.sqrt 2 : ℂ)) * Complex.I) by ring, e]
  simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

/-- On combinations of eigenvectors of `U = V^*` with eigenvalues `e^{it_k}`, the Cayley pairing
is `-∑ |c_k|² cot(t_k/2)`. -/
theorem re_inner_eigen_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H →L[ℂ] H) {n : ℕ} (v : Fin n → H) (hv : Orthonormal ℂ v) (t : Fin n → ℝ)
    (ht : ∀ k, 0 < t k ∧ t k < 2 * π) (hU : ∀ k, U (v k) = Complex.exp (t k * Complex.I) • v k)
    (c : Fin n → ℂ) :
    (⟪∑ k, c k • v k, (Real.sqrt 2 : ℂ) •
        (∑ k, c k • (((Real.sqrt 2 : ℂ) * Complex.I) *
            (Complex.exp (t k * Complex.I) - 1))⁻¹ • v k +
          U (∑ k, c k • (((Real.sqrt 2 : ℂ) * Complex.I) *
            (Complex.exp (t k * Complex.I) - 1))⁻¹ • v k))⟫_ℂ).re =
      -∑ k, ‖c k‖ ^ 2 * Real.cot (t k / 2) := by
  set s : ℂ := (Real.sqrt 2 : ℂ) * Complex.I with hs
  set μ : Fin n → ℂ := fun k => Complex.exp (t k * Complex.I) with hμ
  have hsum : (Real.sqrt 2 : ℂ) • (∑ k, c k • (s * (μ k - 1))⁻¹ • v k +
      U (∑ k, c k • (s * (μ k - 1))⁻¹ • v k)) =
      ∑ k, ((Real.sqrt 2 : ℂ) * (c k * (s * (μ k - 1))⁻¹ * (1 + μ k))) • v k := by
    rw [map_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, hU k]
    simp only [μ]
    module
  rw [hsum, hv.inner_sum c _ Finset.univ, Complex.re_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcot := cot_half_eq (ht k).1 (ht k).2
  have hμ1 : μ k - 1 ≠ 0 := sub_ne_zero.mpr (exp_mul_I_ne_one (ht k).1 (ht k).2)
  have hr : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hc : conj (c k) * c k = ((‖c k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']; push_cast; ring
  have key : conj (c k) * ((Real.sqrt 2 : ℂ) * (c k * (s * (μ k - 1))⁻¹ * (1 + μ k))) =
      ((-(‖c k‖ ^ 2 * Real.cot (t k / 2)) : ℝ) : ℂ) := by
    have e1 : conj (c k) * ((Real.sqrt 2 : ℂ) * (c k * (s * (μ k - 1))⁻¹ * (1 + μ k))) =
        (conj (c k) * c k) * (-(Complex.I * ((μ k + 1) / (μ k - 1)))) := by
      rw [hs]
      field_simp
      rw [Complex.I_sq]
      ring
    rw [e1, hc, ← hcot]
    push_cast
    ring
  rw [key, Complex.ofReal_re]

/-- **Proposition 7.10 / Lemma 8.7 (Cayley rank bound from a lower bound on the Herglotz
form).** For a closed Lipschitz curve and a transport `W` at energy `E`, suppose that
`herglotzForm W γ E a ≥ -A₁ ‖O_E^* g_a‖²` for every `L²` density `a` in the kernel of a linear
map `L : (ℝ → ℂ) → ℂ^m`. Then for `A ≥ A₁`, every orthonormal family of eigenvectors of the
monodromy `U_E` with eigenvalues `e^{it}`, `0 < t < 2π`, `cot(t/2) > A`, has at most `m`
members. -/
theorem cayleyRankBound_of_herglotzForm_bound {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ (2 * π) = γ 0) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) {m : ℕ} (A₁ A : ℝ) (hA : A₁ ≤ A)
    (L : (ℝ → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hbound : ∀ a (_ : IsDirDensity a), L a = 0 →
      -(A₁ * ‖observationAdj W (herglotzConormal (Real.sqrt E) a γ)‖ ^ 2) ≤
        herglotzForm W γ E a) :
    CayleyRankBound (monodromy W) A m := by
  classical
  intro n v t hv ht hUv hcot
  by_contra hlt
  push_neg at hlt
  set s : ℂ := (Real.sqrt 2 : ℂ) * Complex.I with hs
  set μ : Fin n → ℂ := fun k => Complex.exp (t k * Complex.I) with hμ
  set y : Fin n → Ell2 := fun k => (s * (μ k - 1))⁻¹ • v k with hydef
  have hlift : ∀ k, ∃ (a : ℝ → ℂ) (ha : IsDirDensity a),
      herglotzVec ha (Real.sqrt E) (γ 0) = y k := fun k => exists_herglotzVec_eq _ _ _
  choose as has hasy using hlift
  let φ : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) := L ∘ₗ Fintype.linearCombination ℂ as
  have hker : LinearMap.ker φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hlt)
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  set a : ℝ → ℂ := ∑ k, c k • as k with hadef
  have ha : IsDirDensity a := memLp_finset_sum' _ fun k _ => (has k).const_smul (c k)
  have hLa : L a = 0 := by
    simpa [φ, Fintype.linearCombination_apply, hadef] using hc
  obtain ⟨hO, hF⟩ := herglotzForm_eq hK hclosed hW ha
  have hy : herglotzVec ha (Real.sqrt E) (γ 0) = ∑ k, c k • y k := by
    rw [herglotzVec_sum c as has ha]
    simp only [hasy]
  have hμ1 : ∀ k, μ k - 1 ≠ 0 := fun k =>
    sub_ne_zero.mpr (exp_mul_I_ne_one (ht k).1 (ht k).2)
  have hs0 : s ≠ 0 := sqrt_two_mul_I_ne_zero
  have hx : observationAdj W (herglotzConormal (Real.sqrt E) a γ) = ∑ k, c k • v k := by
    rw [hO, hy, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_comm, hydef]
    simp only [map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    have hU := hUv k
    rw [monodromy] at hU
    have e : Complex.exp (t k * Complex.I) • v k - v k =
        (Complex.exp (t k * Complex.I) - 1) • v k := by rw [sub_smul, one_smul]
    rw [hU, e, smul_smul, smul_smul]
    rw [smul_smul]
    refine congrArg (fun r : ℂ => r • v k) ?_
    have h1 := hμ1 k
    simp only [hμ] at h1 ⊢
    rw [← hs]
    field_simp
  have hb := hbound a ha hLa
  rw [hF, hx, hy] at hb
  have hre := re_inner_eigen_sum (monodromy W) v hv t ht hUv c
  simp only [monodromy] at hre
  rw [hre] at hb
  have hn : ‖∑ k, c k • v k‖ ^ 2 = ∑ k, ‖c k‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hv.inner_sum c c Finset.univ]
    simp [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]
  rw [hn] at hb
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hc0 (funext hall)
  have hlt2 : A * ∑ k, ‖c k‖ ^ 2 < ∑ k, ‖c k‖ ^ 2 * Real.cot (t k / 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum
    · intro i _
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hcot i).le (by positivity)
    · exact ⟨j, Finset.mem_univ _, by rw [mul_comm]; exact mul_lt_mul_of_pos_left (hcot j) (by positivity)⟩
  have hnn : 0 ≤ ∑ k, ‖c k‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  nlinarith [mul_le_mul_of_nonneg_right hA hnn]

end PolyaNeumann
