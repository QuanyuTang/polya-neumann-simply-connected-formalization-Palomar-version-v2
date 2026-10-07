module

public import RequestProject.NeumannOperator
public import RequestProject.NeumannMultiplicity
public import RequestProject.FiniteRankCompletion
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Ordered spectrum of the genuine Neumann resolvent

All trial-space dimensions and orthogonality below are over ℂ. The ordered
spectral values are defined using actual eigenvector equations, independently
of the variational values in `Defs`.
-/

@[expose] public section

open Set Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace PolyaNeumann.CompactSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_eigenvector_of_mem_spectrum {T : H →L[ℂ] H} (hT : IsCompactOperator T)
    {k : ℂ} (hk : k ∈ spectrum ℂ T) (hk0 : k ≠ 0) :
    ∃ v : H, v ≠ 0 ∧ T v = k • v := by
  let C : H →L[ℂ] H := (-k⁻¹) • T
  have hC : IsCompactOperator C := hT.smul _
  have hrel : algebraMap ℂ (H →L[ℂ] H) k - T = k • ((1 : H →L[ℂ] H) + C) := by
    dsimp [C]
    rw [smul_add, smul_smul, mul_neg, mul_inv_cancel₀ hk0, neg_one_smul,
      Algebra.algebraMap_eq_smul_one, sub_eq_add_neg]
  by_contra hno
  push_neg at hno
  have hinj : Function.Injective ⇑((1 : H →L[ℂ] H) + C) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hv0
    apply hno v hv0
    have h1 : v + C v = 0 := by simpa using hv
    change v + (-k⁻¹) • T v = 0 at h1
    have h2 : k • (v + (-k⁻¹) • T v) = 0 := by rw [h1, smul_zero]
    rw [smul_add, smul_smul, mul_neg, mul_inv_cancel₀ hk0, neg_one_smul] at h2
    exact (eq_of_sub_eq_zero (by rw [← h2]; abel)).symm
  have hsurj := (injective_iff_surjective_one_add hC).mp hinj
  have hunit : IsUnit ((1 : H →L[ℂ] H) + C) := isUnit_of_bijective _ ⟨hinj, hsurj⟩
  apply hk
  show IsUnit _
  rw [hrel, Algebra.smul_def]
  exact ((IsUnit.mk0 k hk0).map (algebraMap ℂ (H →L[ℂ] H))).mul hunit

/-- A nonzero compact positive complex operator attains its norm at a unit
eigenvector. Positivity rules out a negative extremal eigenvalue. -/
theorem exists_top_eigenvector {T : H →L[ℂ] H} (hT : IsCompactOperator T)
    (hP : T.IsPositive) (hT0 : T ≠ 0) :
    ∃ x : H, ‖x‖ = 1 ∧ T x = (‖T‖ : ℂ) • x ∧
      ∀ y : H, (⟪T y, y⟫_ℂ).re ≤ ‖T‖ * ‖y‖ ^ 2 := by
  haveI : Nontrivial H := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    letI : Subsingleton H := h
    exact hT0 (ContinuousLinearMap.ext fun x => Subsingleton.elim _ _)
  obtain ⟨k, hk, hkn⟩ := spectrum.exists_nnnorm_eq_spectralRadius T
  have hRadius : spectralRadius ℂ T = (‖T‖₊ : ENNReal) :=
    hP.isSelfAdjoint.spectralRadius_eq_nnnorm
  have hknNN : ‖k‖₊ = ‖T‖₊ := ENNReal.coe_inj.mp (hkn.trans hRadius)
  have hkn' : ‖k‖ = ‖T‖ := congrArg NNReal.toReal hknNN
  have hk0 : k ≠ 0 := by
    intro hk0
    rw [hk0, norm_zero, eq_comm, norm_eq_zero] at hkn'
    exact hT0 hkn'
  obtain ⟨v, hv0, hv⟩ := exists_eigenvector_of_mem_spectrum hT hk hk0
  have hkreal : k = (k.re : ℂ) := hP.isSelfAdjoint.mem_spectrum_eq_re hk
  have hkpos : 0 ≤ k.re := by
    have hp := hP.re_inner_nonneg_left v
    rw [hv, inner_smul_left, hkreal, inner_self_eq_norm_sq_to_K] at hp
    have hp' : 0 ≤ k.re * ‖v‖ ^ 2 := by
      simpa [RCLike.re_eq_complex_re, pow_two, Complex.mul_re] using hp
    exact nonneg_of_mul_nonneg_left hp' (sq_pos_of_pos (norm_pos_iff.mpr hv0))
  have hkeq : k = (‖T‖ : ℂ) := by
    rw [hkreal] at hkn'
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hkpos] at hkn'
    rw [hkreal, hkn']
  let x : H := (‖v‖⁻¹ : ℂ) • v
  refine ⟨x, ?_, ?_, fun y => ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
  · dsimp [x]
    rw [map_smul, hv, hkeq]
    exact smul_comm _ _ _
  · calc
      (⟪T y, y⟫_ℂ).re ≤ ‖T y‖ * ‖y‖ := re_inner_le_norm (𝕜 := ℂ) (T y) y
      _ ≤ ‖T‖ * ‖y‖ * ‖y‖ := by gcongr; exact T.le_opNorm _
      _ = ‖T‖ * ‖y‖ ^ 2 := by ring

omit [CompleteSpace H] in
theorem exists_nonzero_orthogonal (hInfinite : ¬ Module.Finite ℂ H)
    (e : ℕ → H) (n : ℕ) :
    ∃ x : H, x ≠ 0 ∧ ∀ i < n, ⟪e i, x⟫_ℂ = 0 := by
  let coordinates : H →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun x i => ⟪e i, x⟫_ℂ
      map_add' := by intro x y; ext i; simp [inner_add_right]
      map_smul' := by intro c x; ext i; simp [inner_smul_right] }
  have hker : LinearMap.ker coordinates ≠ ⊥ := by
    intro hker
    exact hInfinite
      (FiniteDimensional.of_injective coordinates (LinearMap.ker_eq_bot.mp hker))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨x, hx0, fun i hi => ?_⟩
  have h := congrFun (LinearMap.mem_ker.mp hx) (⟨i, hi⟩ : Fin n)
  exact h

/-- Successive actual eigenpairs, with maximality on the preceding orthogonal
complement. Dimensions are complex dimensions throughout. -/
structure PositiveEigenFamily (T : H →L[ℂ] H) (n : ℕ) where
  vectors : ℕ → H
  values : ℕ → ℝ
  orthogonal : ∀ i < n, ∀ l < n,
    ⟪vectors i, vectors l⟫_ℂ = if i = l then 1 else 0
  eigenvector : ∀ i < n, T (vectors i) = (values i : ℂ) • vectors i
  positive : ∀ i < n, 0 < values i
  maximal : ∀ i < n, ∀ x,
    (∀ l < i, ⟪vectors l, x⟫_ℂ = 0) →
      (⟪T x, x⟫_ℂ).re ≤ values i * ‖x‖ ^ 2

namespace PositiveEigenFamily

variable {T : H →L[ℂ] H} {n : ℕ}

omit [CompleteSpace H] in
theorem norm_sq_eq_one (f : PositiveEigenFamily T n) {i : ℕ} (hi : i < n) :
    ‖f.vectors i‖ ^ 2 = 1 := by
  have h := congrArg Complex.re (f.orthogonal i hi i hi)
  simpa [inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re] using h

omit [CompleteSpace H] in
theorem orthonormal (f : PositiveEigenFamily T n) :
    Orthonormal ℂ (fun i : Fin n => f.vectors i) := by
  rw [orthonormal_iff_ite]
  intro i l
  simpa only [Fin.ext_iff] using f.orthogonal i i.isLt l l.isLt

omit [CompleteSpace H] in
theorem value_le (f : PositiveEigenFamily T n) {i j : ℕ}
    (hi : i < n) (hj : j < n) (hij : i ≤ j) : f.values j ≤ f.values i := by
  have h := f.maximal i hi (f.vectors j) (fun l hl => by
    rw [f.orthogonal l (hl.trans hi) j hj, if_neg (lt_of_lt_of_le hl hij).ne])
  rw [f.eigenvector j hj, inner_smul_left, f.orthogonal j hj j hj, if_pos rfl,
    f.norm_sq_eq_one hj] at h
  simpa using h

end PositiveEigenFamily

/-- Strict positivity and infinite complex dimension ensure the successive
construction never stops. -/
theorem exists_positive_eigenfamily {T : H →L[ℂ] H}
    (hCompact : IsCompactOperator T) (hP : T.IsPositive)
    (hStrict : ∀ x : H, x ≠ 0 → 0 < (⟪T x, x⟫_ℂ).re)
    (hInfinite : ¬ Module.Finite ℂ H) (n : ℕ) :
    Nonempty (PositiveEigenFamily T n) := by
  classical
  induction n with
  | zero =>
    exact ⟨{ vectors := fun _ => 0
             values := fun _ => 0
             orthogonal := by simp
             eigenvector := by simp
             positive := by simp
             maximal := by simp }⟩
  | succ n ih =>
    obtain ⟨f⟩ := ih
    let Q : H →L[ℂ] H := 1 - ∑ l ∈ Finset.range n,
      (innerSL ℂ (f.vectors l)).smulRight (f.vectors l)
    have hQapp : ∀ x, Q x = x - ∑ l ∈ Finset.range n,
        ⟪f.vectors l, x⟫_ℂ • f.vectors l := by
      intro x
      simp [Q]
    have hQorth : ∀ x, ∀ k < n, ⟪f.vectors k, Q x⟫_ℂ = 0 := by
      intro x k hk
      rw [hQapp, inner_sub_right, inner_sum]
      simp_rw [inner_smul_right]
      rw [Finset.sum_eq_single k]
      · rw [f.orthogonal k hk k hk]; simp
      · intro l hl hlk
        rw [f.orthogonal k hk l (Finset.mem_range.mp hl), if_neg (Ne.symm hlk), mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr hk) h
    have hQfix : ∀ x, (∀ l < n, ⟪f.vectors l, x⟫_ℂ = 0) → Q x = x := by
      intro x hx
      rw [hQapp, Finset.sum_eq_zero (fun l hl => by
        rw [hx l (Finset.mem_range.mp hl), zero_smul]), sub_zero]
    have hTe : ∀ x, ∀ k < n, ⟪f.vectors k, T (Q x)⟫_ℂ = 0 := by
      intro x k hk
      calc
        ⟪f.vectors k, T (Q x)⟫_ℂ = ⟪T (f.vectors k), Q x⟫_ℂ :=
          (hP.inner_left_eq_inner_right _ _).symm
        _ = 0 := by rw [f.eigenvector k hk, inner_smul_left, hQorth x k hk, mul_zero]
    let T' : H →L[ℂ] H := T.comp Q
    have hsub : ∀ y, y - Q y = ∑ l ∈ Finset.range n,
        ⟪f.vectors l, y⟫_ℂ • f.vectors l := by
      intro y; rw [hQapp]; abel
    have hperp : ∀ x y, ⟪T (Q x), y - Q y⟫_ℂ = 0 := by
      intro x y
      rw [hsub, inner_sum]
      apply Finset.sum_eq_zero
      intro l hl
      rw [inner_smul_right, (inner_eq_zero_symm).mpr (hTe x l (Finset.mem_range.mp hl)),
        mul_zero]
    have hTq : ∀ x y, ⟪T' x, y⟫_ℂ = ⟪T (Q x), Q y⟫_ℂ := by
      intro x y
      have hy : y = Q y + (y - Q y) := by abel
      change ⟪T (Q x), y⟫_ℂ = _
      conv_lhs => rw [hy]
      rw [inner_add_right, hperp, add_zero]
    have hSym' : T'.IsSymmetric := by
      intro x y
      calc
        ⟪T' x, y⟫_ℂ = ⟪T (Q x), Q y⟫_ℂ := hTq x y
        _ = ⟪Q x, T (Q y)⟫_ℂ := hP.isSymmetric _ _
        _ = ⟪x, T' y⟫_ℂ := by
          rw [← inner_conj_symm x (T' y), hTq y x, inner_conj_symm]
    have hP' : T'.IsPositive := ⟨hSym', fun x => by
      change 0 ≤ (⟪T' x, x⟫_ℂ).re
      rw [hTq]
      exact hP.re_inner_nonneg_left _⟩
    have hCompact' : IsCompactOperator T' := hCompact.comp_clm Q
    obtain ⟨y, hy0, hy⟩ := exists_nonzero_orthogonal hInfinite f.vectors n
    have hT'0 : T' ≠ 0 := by
      intro hz
      have hTy : T' y = T y := by dsimp [T']; rw [hQfix y hy]
      have hTy0 : T y = 0 := by rw [← hTy, hz]; rfl
      have h := hStrict y hy0
      rw [hTy0, inner_zero_left, Complex.zero_re] at h
      exact lt_irrefl 0 h
    obtain ⟨x, hx1, hTx, hmax⟩ := exists_top_eigenvector hCompact' hP' hT'0
    have hM : 0 < ‖T'‖ := norm_pos_iff.mpr hT'0
    have hxperp : ∀ k < n, ⟪f.vectors k, x⟫_ℂ = 0 := by
      intro k hk
      have hx : x = ((‖T'‖ : ℂ)⁻¹) • T' x := by
        rw [hTx, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hM.ne'), one_smul]
      rw [hx, inner_smul_right]
      change (‖T'‖ : ℂ)⁻¹ * ⟪f.vectors k, T (Q x)⟫_ℂ = 0
      rw [hTe x k hk, mul_zero]
    have hQx : Q x = x := hQfix x hxperp
    refine ⟨{ vectors := Function.update f.vectors n x
              values := Function.update f.values n ‖T'‖
              orthogonal := ?_
              eigenvector := ?_
              positive := ?_
              maximal := ?_ }⟩
    · intro i hi l hl
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | rfl
      · rw [Function.update_of_ne hi'.ne, Function.update_of_ne hl'.ne]
        exact f.orthogonal i hi' l hl'
      · rw [Function.update_of_ne hi'.ne, Function.update_self, hxperp i hi', if_neg hi'.ne]
      · rw [Function.update_self, Function.update_of_ne hl'.ne, ← inner_conj_symm,
          hxperp l hl', map_zero, if_neg hl'.ne']
      · rw [Function.update_self, inner_self_eq_norm_sq_to_K, hx1]
        simp
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · rw [Function.update_of_ne hi'.ne, Function.update_of_ne hi'.ne]
        exact f.eigenvector i hi'
      · rw [Function.update_self, Function.update_self]
        simpa only [T', ContinuousLinearMap.comp_apply, hQx] using hTx
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
      · rw [Function.update_of_ne hi'.ne]; exact f.positive i hi'
      · rw [Function.update_self]; exact hM
    · intro i hi z hz
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hEq
      · rw [Function.update_of_ne hi'.ne]
        exact f.maximal i hi' z fun l hl => by
          have h := hz l hl
          rwa [Function.update_of_ne (hl.trans hi').ne] at h
      · subst i
        rw [Function.update_self]
        have hz' : ∀ l < n, ⟪f.vectors l, z⟫_ℂ = 0 := fun l hl => by
          have h := hz l hl
          rwa [Function.update_of_ne hl.ne] at h
        simpa only [T', ContinuousLinearMap.comp_apply, hQfix z hz'] using hmax z

/-- Actual orthonormal eigenvectors above a positive threshold. -/
def SpectralThreshold (T : H →L[ℂ] H) (j : ℕ) : Set ℝ :=
  {s | 0 < s ∧ ∃ e : Fin j → H, Orthonormal ℂ e ∧
    ∃ ν : Fin j → ℝ, ∀ i, T (e i) = (ν i : ℂ) • e i ∧ s ≤ ν i}

def spectralEigenvalue (T : H →L[ℂ] H) (j : ℕ) : ℝ :=
  sSup (SpectralThreshold T j)

omit [CompleteSpace H] in
theorem norm_sq_sum_orthonormal {n : ℕ} {e : Fin n → H} (he : Orthonormal ℂ e)
    (c : Fin n → ℂ) : ‖∑ i, c i • e i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
  have h := congrArg Complex.re (he.inner_sum c c Finset.univ)
  simpa [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    pow_two, Complex.mul_re] using h

omit [CompleteSpace H] in
theorem quadratic_sum_eigenvectors {T : H →L[ℂ] H} {n : ℕ}
    {e : Fin n → H} (he : Orthonormal ℂ e) (ν : Fin n → ℝ)
    (hEigen : ∀ i, T (e i) = (ν i : ℂ) • e i) (c : Fin n → ℂ) :
    (⟪T (∑ i, c i • e i), ∑ i, c i • e i⟫_ℂ).re = ∑ i, ν i * ‖c i‖ ^ 2 := by
  have h : ⟪T (∑ i, c i • e i), ∑ i, c i • e i⟫_ℂ =
      ∑ i, ((ν i * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [map_sum, sum_inner]
    simp_rw [map_smul, hEigen, smul_smul, inner_smul_left, he.inner_right_fintype c]
    apply Finset.sum_congr rfl
    intro i _
    calc
      conj (c i * (ν i : ℂ)) * c i = (ν i : ℂ) * (conj (c i) * c i) := by
        rw [map_mul, Complex.conj_ofReal]; ring
      _ = ((ν i * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_mul]
  rw [h, Complex.re_sum]
  simp [pow_two, Complex.mul_re]

omit [CompleteSpace H] in
theorem quadratic_lower_on_eigenspan {T : H →L[ℂ] H} {n : ℕ}
    {e : Fin n → H} (he : Orthonormal ℂ e) (ν : Fin n → ℝ)
    (hEigen : ∀ i, T (e i) = (ν i : ℂ) • e i) {s : ℝ} (hs : ∀ i, s ≤ ν i)
    {x : H} (hx : x ∈ Submodule.span ℂ (Set.range e)) :
    s * ‖x‖ ^ 2 ≤ (⟪T x, x⟫_ℂ).re := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  rw [← hc, norm_sq_sum_orthonormal he c, quadratic_sum_eigenvectors he ν hEigen c,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hs i) (sq_nonneg _)

namespace PositiveEigenFamily

variable {T : H →L[ℂ] H} {j : ℕ}

omit [CompleteSpace H] in
theorem threshold_le_last (f : PositiveEigenFamily T j) (hj : 0 < j)
    {s : ℝ} (hs : s ∈ SpectralThreshold T j) : s ≤ f.values (j - 1) := by
  obtain ⟨_, e, he, ν, hν⟩ := hs
  let W : Submodule ℂ H := Submodule.span ℂ (Set.range e)
  have hWdim : Module.finrank ℂ W = j := by
    rw [finrank_span_eq_card he.linearIndependent, Fintype.card_fin]
  letI : Module.Finite ℂ W := Module.finite_of_finrank_pos (by rw [hWdim]; exact hj)
  let coordinates : W →ₗ[ℂ] (Fin (j - 1) → ℂ) :=
    { toFun := fun x i => ⟪f.vectors i, (x : H)⟫_ℂ
      map_add' := by intro x y; ext i; simp [inner_add_right]
      map_smul' := by intro c x; ext i; simp [inner_smul_right] }
  have hker : LinearMap.ker coordinates ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp [hWdim]; omega)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hx0' : (x : H) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hxorth : ∀ l < j - 1, ⟪f.vectors l, (x : H)⟫_ℂ = 0 := by
    intro l hl
    have h := congrFun (LinearMap.mem_ker.mp hx) (⟨l, hl⟩ : Fin (j - 1))
    exact h
  have hLower : s * ‖(x : H)‖ ^ 2 ≤ (⟪T (x : H), (x : H)⟫_ℂ).re :=
    quadratic_lower_on_eigenspan he ν (fun i => (hν i).1) (fun i => (hν i).2) x.property
  have hUpper := f.maximal (j - 1) (by omega) (x : H) hxorth
  exact le_of_mul_le_mul_right (hLower.trans hUpper) (sq_pos_of_pos (norm_pos_iff.mpr hx0'))

omit [CompleteSpace H] in
theorem last_mem_threshold (f : PositiveEigenFamily T j) (hj : 0 < j) :
    f.values (j - 1) ∈ SpectralThreshold T j := by
  refine ⟨f.positive (j - 1) (by omega), (fun i : Fin j => f.vectors i), f.orthonormal,
    (fun i : Fin j => f.values i), fun i => ⟨f.eigenvector i i.isLt, ?_⟩⟩
  exact f.value_le i.isLt (by omega) (by omega)

omit [CompleteSpace H] in
theorem spectralEigenvalue_eq_last (f : PositiveEigenFamily T j) (hj : 0 < j) :
    spectralEigenvalue T j = f.values (j - 1) := by
  apply le_antisymm
  · exact csSup_le ⟨_, f.last_mem_threshold hj⟩ (fun s hs => f.threshold_le_last hj hs)
  · exact le_csSup ⟨f.values (j - 1), fun s hs => f.threshold_le_last hj hs⟩
      (f.last_mem_threshold hj)

omit [CompleteSpace H] in
theorem spectralEigenvalue_at_index {n : ℕ} (f : PositiveEigenFamily T n)
    {i : ℕ} (hi : i < n) : spectralEigenvalue T (i + 1) = f.values i := by
  let g : PositiveEigenFamily T (i + 1) :=
    { vectors := f.vectors
      values := f.values
      orthogonal := fun k hk l hl => f.orthogonal k (by omega) l (by omega)
      eigenvector := fun k hk => f.eigenvector k (by omega)
      positive := fun k hk => f.positive k (by omega)
      maximal := fun k hk x hx => f.maximal k (by omega) x hx }
  simpa only [Nat.add_sub_cancel, g] using g.spectralEigenvalue_eq_last (by omega)

end PositiveEigenFamily

theorem spectralEigenvalue_pos {T : H →L[ℂ] H}
    (hCompact : IsCompactOperator T) (hP : T.IsPositive)
    (hStrict : ∀ x : H, x ≠ 0 → 0 < (⟪T x, x⟫_ℂ).re)
    (hInfinite : ¬ Module.Finite ℂ H) {j : ℕ} (hj : 0 < j) :
    0 < spectralEigenvalue T j := by
  obtain ⟨f⟩ := exists_positive_eigenfamily hCompact hP hStrict hInfinite j
  rw [f.spectralEigenvalue_eq_last hj]
  exact f.positive (j - 1) (by omega)

omit [CompleteSpace H] in
/-- Compactness bounds the size of complex orthonormal families in a fixed set. -/
theorem orthonormal_card_bound_of_compact {K : Set H} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ {j : ℕ} {e : Fin j → H}, Orthonormal ℂ e →
      (∀ i, e i ∈ K) → j ≤ N := by
  classical
  obtain ⟨t, _, ht, hcover⟩ := hK.finite_cover_balls (by norm_num : (0 : ℝ) < 1 / 2)
  letI : Fintype t := ht.fintype
  refine ⟨Fintype.card t, ?_⟩
  intro j e he heK
  have hcenter : ∀ i : Fin j, ∃ y : t, dist (e i) (y : H) < 1 / 2 := by
    intro i
    obtain ⟨y, hy, hball⟩ := Set.mem_iUnion₂.mp (hcover (heK i))
    exact ⟨⟨y, hy⟩, Metric.mem_ball.mp hball⟩
  choose g hg using hcenter
  have hgInjective : Function.Injective g := by
    intro i l hil
    by_contra hne
    have hleft := hg i
    have hright : dist (g i : H) (e l) < 1 / 2 := by
      rw [hil, dist_comm]
      exact hg l
    have hdist : dist (e i) (e l) < 1 := by
      have htriangle := dist_triangle (e i) (g i : H) (e l)
      linarith
    have hsquared : dist (e i) (e l) ^ 2 = 2 := by
      rw [dist_eq_norm, norm_sub_sq (𝕜 := ℂ), he.norm_eq_one i,
        he.norm_eq_one l, he.inner_eq_zero hne]
      norm_num
    nlinarith [(dist_nonneg : 0 ≤ dist (e i) (e l))]
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective g hgInjective

omit [CompleteSpace H] in
/-- Only finitely many complex orthogonal eigenvectors can lie above a positive threshold. -/
theorem spectralThreshold_card_bound {T : H →L[ℂ] H}
    (hCompact : IsCompactOperator T) {s : ℝ} (hs : 0 < s) :
    ∃ N : ℕ, ∀ j : ℕ, s ∈ SpectralThreshold T j → j ≤ N := by
  classical
  obtain ⟨K, hK, hTK⟩ := IsCompactOperator.image_closedBall_subset_compact
    (f := T.toLinearMap) hCompact (1 / s)
  obtain ⟨N, hN⟩ := orthonormal_card_bound_of_compact hK
  refine ⟨N, ?_⟩
  intro j hj
  obtain ⟨_, e, he, ν, hν⟩ := hj
  apply hN he
  intro i
  have hνPos : 0 < ν i := hs.trans_le (hν i).2
  apply hTK
  refine ⟨((ν i)⁻¹ : ℂ) • e i, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hνPos, he.norm_eq_one i, mul_one]
    simpa only [one_div] using one_div_le_one_div_of_le hs (hν i).2
  · change T (((ν i)⁻¹ : ℂ) • e i) = e i
    rw [map_smul, (hν i).1, smul_smul]
    have hν0 : (ν i : ℂ) ≠ 0 := by exact_mod_cast hνPos.ne'
    rw [inv_mul_cancel₀ hν0, one_smul]

/-- The independently ordered resolvent eigenvalues tend to zero. -/
theorem eventually_spectralEigenvalue_lt {T : H →L[ℂ] H}
    (hCompact : IsCompactOperator T) (hP : T.IsPositive)
    (hStrict : ∀ x : H, x ≠ 0 → 0 < (⟪T x, x⟫_ℂ).re)
    (hInfinite : ¬ Module.Finite ℂ H) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ j : ℕ in atTop, spectralEigenvalue T j < s := by
  obtain ⟨N, hN⟩ := spectralThreshold_card_bound hCompact hs
  refine eventually_atTop.2 ⟨N + 1, ?_⟩
  intro j hj
  obtain ⟨f⟩ := exists_positive_eigenfamily hCompact hP hStrict hInfinite j
  have hjPos : 0 < j := by omega
  by_contra hlt
  have hsLast : s ≤ f.values (j - 1) := by
    have hle := le_of_not_gt hlt
    rwa [f.spectralEigenvalue_eq_last hjPos] at hle
  have hsThreshold : s ∈ SpectralThreshold T j := by
    obtain ⟨_, e, he, ν, hν⟩ := f.last_mem_threshold hjPos
    exact ⟨hs, e, he, ν, fun i => ⟨(hν i).1, hsLast.trans (hν i).2⟩⟩
  have := hN j hsThreshold
  omega

theorem spectralEigenvalue_tendsto_zero {T : H →L[ℂ] H}
    (hCompact : IsCompactOperator T) (hP : T.IsPositive)
    (hStrict : ∀ x : H, x ≠ 0 → 0 < (⟪T x, x⟫_ℂ).re)
    (hInfinite : ¬ Module.Finite ℂ H) :
    Tendsto (spectralEigenvalue T) atTop (𝓝 (0 : ℝ)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with j hj
    exact ha.trans (spectralEigenvalue_pos hCompact hP hStrict hInfinite (by omega))
  · intro b hb
    exact eventually_spectralEigenvalue_lt hCompact hP hStrict hInfinite hb

/-- Actual positive eigenvectors of the compact operator, including every eigenspace. -/
def positiveEigenvectors (T : H →L[ℂ] H) : Set H :=
  {u | ∃ eigenCoefficient : ℝ, 0 < eigenCoefficient ∧ T u = (eigenCoefficient : ℂ) • u}

theorem eq_zero_of_orthogonal_to_positive_eigenvectors {T : H →L[ℂ] H}
    (hCompact : IsCompactOperator T) (hP : T.IsPositive)
    (hStrict : ∀ x : H, x ≠ 0 → 0 < (⟪T x, x⟫_ℂ).re)
    (hInfinite : ¬ Module.Finite ℂ H) {x : H}
    (hx : ∀ v ∈ positiveEigenvectors T, ⟪v, x⟫_ℂ = 0) : x = 0 := by
  by_contra hx0
  have hq : 0 < (⟪T x, x⟫_ℂ).re := hStrict x hx0
  have hnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
  let s : ℝ := (⟪T x, x⟫_ℂ).re / (2 * ‖x‖ ^ 2)
  have hs : 0 < s := div_pos hq (mul_pos (by norm_num) hnorm)
  obtain ⟨n, hn, hnPos⟩ := ((eventually_spectralEigenvalue_lt
    hCompact hP hStrict hInfinite hs).and (eventually_ge_atTop (1 : ℕ))).exists
  obtain ⟨f⟩ := exists_positive_eigenfamily hCompact hP hStrict hInfinite n
  have horth : ∀ i < n - 1, ⟪f.vectors i, x⟫_ℂ = 0 := by
    intro i hi
    exact hx _ ⟨f.values i, f.positive i (by omega), f.eigenvector i (by omega)⟩
  have hbound := f.maximal (n - 1) (by omega) x horth
  have hn' : f.values (n - 1) < s := by
    rwa [f.spectralEigenvalue_eq_last (by omega)] at hn
  have hsEq : s * (2 * ‖x‖ ^ 2) = (⟪T x, x⟫_ℂ).re :=
    div_mul_cancel₀ _ (mul_pos (by norm_num) hnorm).ne'
  have hstrictBound := mul_lt_mul_of_pos_right hn' hnorm
  nlinarith

/-- The genuine compact eigenvectors are complete in the complex Hilbert space. -/
theorem dense_span_positiveEigenvectors {T : H →L[ℂ] H}
    (hCompact : IsCompactOperator T) (hP : T.IsPositive)
    (hStrict : ∀ x : H, x ≠ 0 → 0 < (⟪T x, x⟫_ℂ).re)
    (hInfinite : ¬ Module.Finite ℂ H) :
    Dense (Submodule.span ℂ (positiveEigenvectors T) : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  rw [Submodule.eq_bot_iff]
  intro x hx
  exact eq_zero_of_orthogonal_to_positive_eigenvectors hCompact hP hStrict hInfinite
    fun v hv => Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span hv) hx

end PolyaNeumann.CompactSpectral

namespace PolyaNeumann

theorem L2_infinite_of_isOpen {Ω : Set ℂ} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ¬ Module.Finite ℂ (L2 Ω) := by
  intro hFinite
  letI : Module.Finite ℂ (L2 Ω) := hFinite
  let d := Module.finrank ℂ (L2 Ω)
  have htop : neumannEigenvalue Ω d = ⊤ := by
    unfold neumannEigenvalue
    apply iInf₂_eq_top.mpr
    intro S hS
    have hle := Submodule.finrank_le S
    rw [hS] at hle
    exact False.elim (by dsimp [d] at hle; omega)
  exact (neumannEigenvalue_lt_top_of_isOpen hΩ hne d).ne htop

/-- Numbered values of the actual resolvent spectrum; Neumann indices start
at zero, so the reciprocal resolvent index is `j + 1`. -/
def spectralNeumannEigenvalue (Ω : Set ℂ) (j : ℕ) : ℝ :=
  (CompactSpectral.spectralEigenvalue (neumannResolvent Ω) (j + 1))⁻¹ - 1

theorem exists_positive_neumann_eigenfamily {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (n : ℕ) :
    Nonempty (CompactSpectral.PositiveEigenFamily (neumannResolvent Ω) n) :=
  CompactSpectral.exists_positive_eigenfamily (neumannResolvent_compact hb hL)
    (neumannResolvent_isPositive Ω) (neumannResolvent_strictPositive hL.1.1)
    (L2_infinite_of_isOpen hL.1.1 hL.1.2.nonempty) n

/-- The genuine H¹ norm is exactly mass plus weak-gradient energy. -/
theorem h1Vector_norm_sq {Ω : Set ℂ} {u : L2 Ω} {g : Fin 2 → L2 Ω}
    (hg : IsWeakGradient Ω u g) :
    ‖h1Vector hg‖ ^ 2 = ‖u‖ ^ 2 + ∑ i, ‖g i‖ ^ 2 := by
  simpa only [h1Value_h1Vector, h1Gradient_h1Vector] using h1_norm_sq Ω (h1Vector hg)

theorem exists_grad_of_rayleigh_ne_top {Ω : Set ℂ} {u : L2 Ω}
    (hR : rayleigh Ω u ≠ ⊤) : ∃ g, IsWeakGradient Ω u g := by
  by_contra hno
  have htop : neumannEnergy Ω u = ⊤ := by
    unfold neumannEnergy
    apply iInf₂_eq_top.mpr
    intro g hg
    exact False.elim (hno ⟨g, hg⟩)
  exact hR (by unfold rayleigh; rw [htop, ENNReal.top_div_of_ne_top (by simp)])

/-- Maximality of a resolvent eigenfamily gives the original Neumann
Rayleigh lower bound, by Cauchy–Schwarz in the actual H¹ space. -/
theorem neumann_rayleigh_lower_of_orthogonality {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {j : ℕ} (f : CompactSpectral.PositiveEigenFamily (neumannResolvent Ω) (j + 1))
    {u : L2 Ω} (hu0 : u ≠ 0) (horth : ∀ i < j, ⟪f.vectors i, u⟫_ℂ = 0) :
    ENNReal.ofReal ((f.values j)⁻¹ - 1) ≤ rayleigh Ω u := by
  by_cases hR : rayleigh Ω u = ⊤
  · rw [hR]; exact le_top
  obtain ⟨g, hg⟩ := exists_grad_of_rayleigh_ne_top hR
  let v := h1Vector hg
  let a := ContinuousLinearMap.adjoint (h1Value Ω) u
  have hU : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu0)
  have heigenCoefficient : 0 < f.values j := f.positive j (by omega)
  have hc : ‖u‖ ^ 2 ≤ ‖v‖ * ‖a‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) v a
    rw [ContinuousLinearMap.adjoint_inner_right, h1Value_h1Vector,
      inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_eq_complex_ofReal,
      Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at h
    exact h
  have ha : ‖a‖ ^ 2 ≤ f.values j * ‖u‖ ^ 2 := by
    have h := f.maximal j (by omega) u horth
    rw [neumannResolvent_inner, inner_self_eq_norm_sq_to_K] at h
    simpa [a, pow_two, Complex.mul_re] using h
  have hc2 : (‖u‖ ^ 2) ^ 2 ≤ ‖v‖ ^ 2 * ‖a‖ ^ 2 := by
    have h := pow_le_pow_left₀ (sq_nonneg ‖u‖) hc 2
    simpa only [mul_pow] using h
  have hUV : ‖u‖ ^ 2 ≤ ‖v‖ ^ 2 * f.values j := by
    have h := hc2.trans (mul_le_mul_of_nonneg_left ha (sq_nonneg ‖v‖))
    have h' : (‖u‖ ^ 2) * (‖u‖ ^ 2) ≤ (‖v‖ ^ 2 * f.values j) * (‖u‖ ^ 2) := by
      convert h using 1 <;> ring
    exact le_of_mul_le_mul_right h' hU
  have hV : (f.values j)⁻¹ * ‖u‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← div_eq_inv_mul, div_le_iff₀ heigenCoefficient]
    simpa only [mul_comm] using hUV
  have hnorm : ‖v‖ ^ 2 = ‖u‖ ^ 2 + ∑ i, ‖g i‖ ^ 2 := h1Vector_norm_sq hg
  have hq : ((f.values j)⁻¹ - 1) * ‖u‖ ^ 2 ≤ ∑ i, ‖g i‖ ^ 2 := by
    rw [hnorm] at hV
    nlinarith
  rw [rayleigh_eq_ofReal hΩ hu0 hg]
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ hU]
  exact hq

/-- The dimension argument takes place directly in the original L² trial
space, with complex dimensions; it does not assume spectral identification. -/
theorem neumannEigenvalue_lower_of_eigenfamily {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {j : ℕ} (f : CompactSpectral.PositiveEigenFamily (neumannResolvent Ω) (j + 1)) :
    ENNReal.ofReal ((f.values j)⁻¹ - 1) ≤ neumannEigenvalue Ω j := by
  unfold neumannEigenvalue
  refine le_iInf₂ fun S hS => ?_
  letI : Module.Finite ℂ S := Module.finite_of_finrank_pos (by rw [hS]; omega)
  let coordinates : S →ₗ[ℂ] (Fin j → ℂ) :=
    { toFun := fun u i => ⟪f.vectors i, (u : L2 Ω)⟫_ℂ
      map_add' := by intro x y; ext i; simp [inner_add_right]
      map_smul' := by intro c x; ext i; simp [inner_smul_right] }
  have hker : LinearMap.ker coordinates ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp [hS])
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hu0' : (u : L2 Ω) ≠ 0 := fun h => hu0 (Subtype.ext h)
  have horth : ∀ i < j, ⟪f.vectors i, (u : L2 Ω)⟫_ℂ = 0 := by
    intro i hi
    have h := congrFun (LinearMap.mem_ker.mp hu) (⟨i, hi⟩ : Fin j)
    exact h
  exact (neumann_rayleigh_lower_of_orthogonality hΩ f hu0' horth).trans
    (le_iSup₂_of_le (u : L2 Ω) u.property (le_iSup (fun _ : (u : L2 Ω) ≠ 0 =>
      rayleigh Ω (u : L2 Ω)) hu0'))

theorem rayleigh_eq_operator {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (u : (neumannOperator Ω).domain) (hu0 : (u : L2 Ω) ≠ 0) :
    rayleigh Ω (u : L2 Ω) =
      ENNReal.ofReal ((⟪(u : L2 Ω), neumannOperator Ω u⟫_ℂ).re / ‖(u : L2 Ω)‖ ^ 2) := by
  obtain ⟨g, hg, hw⟩ := (neumannOperator_weak_representation hΩ (u : L2 Ω)
    (neumannOperator Ω u)).mp ⟨u.property, rfl⟩
  have h := congrArg Complex.re (hw (u : L2 Ω) g hg)
  have h' : ∑ i, ‖g i‖ ^ 2 = (⟪(u : L2 Ω), neumannOperator Ω u⟫_ℂ).re := by
    simpa [pow_two, Complex.mul_re] using h
  rw [rayleigh_eq_ofReal hΩ hu0 hg, h']

theorem neumann_operator_eigenpair_of_resolvent {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {eigenCoefficient : ℝ} (heigenCoefficient : 0 < eigenCoefficient) {u : L2 Ω} (hu : neumannResolvent Ω u = (eigenCoefficient : ℂ) • u) :
    ∃ hd : u ∈ (neumannOperator Ω).domain,
      neumannOperator Ω ⟨u, hd⟩ = ((eigenCoefficient⁻¹ - 1 : ℝ) : ℂ) • u := by
  have hparam : ((eigenCoefficient⁻¹ - 1 : ℝ) : ℂ) + 1 = (eigenCoefficient : ℂ)⁻¹ := by
    push_cast
    ring
  apply (neumannOperator_eigen_iff_resolvent hΩ _ (by
    rw [hparam]; exact inv_ne_zero (by exact_mod_cast heigenCoefficient.ne')) u).mpr
  rw [hparam, inv_inv]
  exact hu

/-- The span of the actual first `j + 1` eigenvectors yields the original
complex Neumann min–max upper bound. -/
theorem neumannEigenvalue_upper_of_eigenfamily {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {j : ℕ} (f : CompactSpectral.PositiveEigenFamily (neumannResolvent Ω) (j + 1)) :
    neumannEigenvalue Ω j ≤ ENNReal.ofReal ((f.values j)⁻¹ - 1) := by
  classical
  let e : Fin (j + 1) → L2 Ω := fun i => f.vectors i
  let E : Fin (j + 1) → ℝ := fun i => (f.values i)⁻¹ - 1
  have he : Orthonormal ℂ e := f.orthonormal
  have heig : ∀ i : Fin (j + 1), ∃ hu : e i ∈ (neumannOperator Ω).domain,
      neumannOperator Ω ⟨e i, hu⟩ = (E i : ℂ) • e i := fun i =>
    neumann_operator_eigenpair_of_resolvent hΩ (f.positive i i.isLt) (f.eigenvector i i.isLt)
  choose hd hEigen using heig
  let ed : Fin (j + 1) → (neumannOperator Ω).domain := fun i => ⟨e i, hd i⟩
  have hEbound : ∀ i : Fin (j + 1), E i ≤ (f.values j)⁻¹ - 1 := by
    intro i
    have h := one_div_le_one_div_of_le (f.positive j (by omega))
      (f.value_le i.isLt (by omega) (by omega))
    dsimp [E]
    simpa only [one_div] using sub_le_sub_right h 1
  let S : Submodule ℂ (L2 Ω) := Submodule.span ℂ (Set.range e)
  have hS : Module.finrank ℂ S = j + 1 := by
    rw [finrank_span_eq_card he.linearIndependent, Fintype.card_fin]
  unfold neumannEigenvalue
  refine (iInf₂_le S hS).trans (iSup₂_le fun u hu => iSup_le fun hu0 => ?_)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hu
  let v : (neumannOperator Ω).domain := ∑ i, c i • ed i
  have hvsum : (v : L2 Ω) = ∑ i, c i • e i := by simp [v, ed]
  have hv : (v : L2 Ω) = u := by simpa only [v, Submodule.coe_sum, Submodule.coe_smul] using hc
  have hAv : neumannOperator Ω v = ∑ i, (c i * (E i : ℂ)) • e i := by
    change (neumannOperator Ω).toFun (∑ i, c i • ed i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    change c i • neumannOperator Ω ⟨e i, hd i⟩ = _
    rw [hEigen i, smul_smul]
  have hquadratic : (⟪(v : L2 Ω), neumannOperator Ω v⟫_ℂ).re =
      ∑ i, E i * ‖c i‖ ^ 2 := by
    rw [hAv, inner_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_right]
    have hcoeff : ⟪(v : L2 Ω), e i⟫_ℂ = conj (c i) := by
      rw [hvsum]
      exact he.inner_left_fintype c i
    rw [hcoeff]
    have heq : (c i * (E i : ℂ)) * conj (c i) = ((E i * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
      calc
        (c i * (E i : ℂ)) * conj (c i) = (E i : ℂ) * (conj (c i) * c i) := by ring
        _ = _ := by
          rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_mul]
    rw [heq, Complex.ofReal_re]
  have hnorm : ‖(v : L2 Ω)‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    rw [hvsum]
    exact CompactSpectral.norm_sq_sum_orthonormal he c
  have hq : (⟪(v : L2 Ω), neumannOperator Ω v⟫_ℂ).re ≤
      ((f.values j)⁻¹ - 1) * ‖(v : L2 Ω)‖ ^ 2 := by
    rw [hquadratic, hnorm, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hEbound i) (sq_nonneg _)
  have hv0 : (v : L2 Ω) ≠ 0 := by simpa only [hv] using hu0
  rw [← hv, rayleigh_eq_operator hΩ v hv0]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hv0))]
  exact hq

/-- Identification with the ordered spectrum of the actual shifted form
resolvent, proved using the original complex min–max definition. -/
theorem neumannEigenvalue_eq_spectral {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (j : ℕ) :
    neumannEigenvalue Ω j = ENNReal.ofReal (spectralNeumannEigenvalue Ω j) := by
  obtain ⟨f⟩ := exists_positive_neumann_eigenfamily hb hL (j + 1)
  have heigenCoefficient : CompactSpectral.spectralEigenvalue (neumannResolvent Ω) (j + 1) = f.values j := by
    simpa using f.spectralEigenvalue_eq_last (by omega : 0 < j + 1)
  rw [spectralNeumannEigenvalue, heigenCoefficient]
  exact le_antisymm (neumannEigenvalue_upper_of_eigenfamily hL.1.1 f)
    (neumannEigenvalue_lower_of_eigenfamily hL.1.1 f)

theorem spectralNeumannEigenvalue_nonneg {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (j : ℕ) : 0 ≤ spectralNeumannEigenvalue Ω j := by
  obtain ⟨f⟩ := exists_positive_neumann_eigenfamily hb hL (j + 1)
  obtain ⟨hu, hAu⟩ := neumann_operator_eigenpair_of_resolvent hL.1.1
    (f.positive j (by omega)) (f.eigenvector j (by omega))
  have h := neumannOperator_nonneg hL.1.1 ⟨f.vectors j, hu⟩
  rw [hAu, inner_smul_right, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
    RCLike.ofReal_eq_complex_ofReal,
    f.norm_sq_eq_one (by omega)] at h
  have heigenCoefficient : CompactSpectral.spectralEigenvalue (neumannResolvent Ω) (j + 1) = f.values j := by
    simpa using f.spectralEigenvalue_eq_last (by omega : 0 < j + 1)
  rw [spectralNeumannEigenvalue, heigenCoefficient]
  simpa using h

theorem neumannEigenvalue_toReal_eq_spectral {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (j : ℕ) :
    (neumannEigenvalue Ω j).toReal = spectralNeumannEigenvalue Ω j := by
  rw [neumannEigenvalue_eq_spectral hb hL j,
    ENNReal.toReal_ofReal (spectralNeumannEigenvalue_nonneg hb hL j)]

/-- Every original numbered min–max value is an eigenvalue of the actual
densely defined, self-adjoint Neumann Laplacian, with a normalized eigenvector. -/
theorem neumannEigenvalue_has_operator_eigenvector {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (j : ℕ) :
    ∃ u : (neumannOperator Ω).domain, ‖(u : L2 Ω)‖ = 1 ∧
      neumannOperator Ω u = ((neumannEigenvalue Ω j).toReal : ℂ) • (u : L2 Ω) := by
  obtain ⟨f⟩ := exists_positive_neumann_eigenfamily hb hL (j + 1)
  obtain ⟨hu, hAu⟩ := neumann_operator_eigenpair_of_resolvent hL.1.1
    (f.positive j (by omega)) (f.eigenvector j (by omega))
  refine ⟨⟨f.vectors j, hu⟩, ?_, ?_⟩
  · have h := f.norm_sq_eq_one (by omega : j < j + 1)
    nlinarith [norm_nonneg (f.vectors j)]
  · have heigenCoefficient : CompactSpectral.spectralEigenvalue (neumannResolvent Ω) (j + 1) = f.values j := by
      simpa using f.spectralEigenvalue_eq_last (by omega : 0 < j + 1)
    rw [neumannEigenvalue_toReal_eq_spectral hb hL j, spectralNeumannEigenvalue, heigenCoefficient]
    exact hAu

theorem neumannEigenvalue_toReal_eq_family {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {n : ℕ}
    (f : CompactSpectral.PositiveEigenFamily (neumannResolvent Ω) n)
    {j : ℕ} (hj : j < n) :
    (neumannEigenvalue Ω j).toReal = (f.values j)⁻¹ - 1 := by
  rw [neumannEigenvalue_toReal_eq_spectral hb hL j, spectralNeumannEigenvalue,
    f.spectralEigenvalue_at_index hj]

/-- The converse multiplicity bound: repeated numbered values give linearly
independent actual eigenfunctions over ℂ. -/
theorem neumannEigenvalue_multiplicity_le_finrank {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    {E : ℝ} (hE : 0 ≤ E) :
    {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard ≤
      (Module.finrank ℂ (neumannEigenspace Ω E) : ℕ∞) := by
  classical
  let S : Set ℕ := {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}
  have hlt : ENNReal.ofReal E < ENNReal.ofReal (E + 1) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hE).mpr (by linarith)
  have hS : S.Finite :=
    (finite_setOf_neumannEigenvalue_lt hb hL ENNReal.ofReal_ne_top).subset
      (fun j hj => by
        change neumannEigenvalue Ω j = ENNReal.ofReal E at hj
        change neumannEigenvalue Ω j < ENNReal.ofReal (E + 1)
        rw [hj]
        exact hlt)
  letI : Fintype S := hS.fintype
  obtain ⟨N, hN⟩ := hS.bddAbove
  obtain ⟨f⟩ := exists_positive_neumann_eigenfamily hb hL (N + 1)
  have hidx : ∀ j : S, (j : ℕ) < N + 1 := fun j => Nat.lt_succ_of_le (hN j.property)
  have hmem : ∀ j : S, f.vectors j ∈ neumannEigenspace Ω E := by
    intro j
    obtain ⟨hu, hAu⟩ := neumann_operator_eigenpair_of_resolvent hL.1.1
      (f.positive j (hidx j)) (f.eigenvector j (hidx j))
    have hvalue : (f.values j)⁻¹ - 1 = E := by
      rw [← neumannEigenvalue_toReal_eq_family hb hL f (hidx j)]
      rw [j.property, ENNReal.toReal_ofReal hE]
    rw [← neumannOperatorEigenspace_eq hL.1.1 E, mem_neumannOperatorEigenspace_iff]
    exact ⟨hu, by simpa only [hvalue] using hAu⟩
  have hON : Orthonormal ℂ (fun j : S => f.vectors j) := by
    rw [orthonormal_iff_ite]
    intro i k
    simpa only [Subtype.ext_iff] using f.orthogonal i (hidx i) k (hidx k)
  letI : FiniteDimensional ℂ (neumannEigenspace Ω E) :=
    finiteDimensional_neumannEigenspace hb hL E
  have hcard : Fintype.card S ≤ Module.finrank ℂ (neumannEigenspace Ω E) :=
    (hON.codRestrict (neumannEigenspace Ω E) hmem).linearIndependent.fintype_card_le_finrank
  simpa only [Set.coe_fintypeCard] using (ENat.coe_le_coe.mpr hcard)

/-- Exact complex multiplicity identification with the weak and actual
operator eigenspaces. -/
theorem neumannEigenvalue_multiplicity_eq {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    (Module.finrank ℂ (neumannEigenspace Ω E) : ℕ∞) =
      {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard :=
  le_antisymm (finrank_neumannEigenspace_le hb hL hE)
    (neumannEigenvalue_multiplicity_le_finrank hb hL hE)

theorem neumannOperator_multiplicity_eq {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    (Module.finrank ℂ (neumannOperatorEigenspace Ω E) : ℕ∞) =
      {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard := by
  rw [neumannOperatorEigenspace_eq hL.1.1]
  exact neumannEigenvalue_multiplicity_eq hb hL hE

/-- Every genuine real operator eigenvalue appears among the original numbered values. -/
theorem neumannOperator_eigenvalue_is_indexed {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E)
    {u : L2 Ω} (hu0 : u ≠ 0) (hu : u ∈ neumannOperatorEigenspace Ω E) :
    ∃ j : ℕ, neumannEigenvalue Ω j = ENNReal.ofReal E := by
  letI : FiniteDimensional ℂ (neumannEigenspace Ω E) :=
    finiteDimensional_neumannEigenspace hb hL E
  have hmem : u ∈ neumannEigenspace Ω E := by
    rwa [neumannOperatorEigenspace_eq hL.1.1] at hu
  have hdim : 0 < Module.finrank ℂ (neumannEigenspace Ω E) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨u, hmem⟩, fun h => hu0 (congrArg Subtype.val h)⟩
  have hcard : 0 < {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard := by
    rw [← neumannEigenvalue_multiplicity_eq hb hL hE]
    exact_mod_cast hdim
  exact Set.encard_pos.mp hcard

/-- There are no additional genuine complex point eigenvalues: each is a
real, nonnegative value in the original variational sequence. -/
theorem neumannOperator_complex_eigenvalue_iff_indexed {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) (c : ℂ) :
    (∃ u : (neumannOperator Ω).domain, (u : L2 Ω) ≠ 0 ∧
      neumannOperator Ω u = c • (u : L2 Ω)) ↔
      ∃ j : ℕ, c = ((neumannEigenvalue Ω j).toReal : ℂ) := by
  constructor
  · rintro ⟨u, hu0, hAu⟩
    obtain ⟨hc, hnonneg⟩ := neumannOperator_eigenvalue_real_nonneg hL.1.1 u hu0 hAu
    have hmem : (u : L2 Ω) ∈ neumannOperatorEigenspace Ω c.re :=
      (mem_neumannOperatorEigenspace_iff Ω c.re _).mpr
        ⟨u.property, hAu.trans (congrArg (fun z : ℂ => z • (u : L2 Ω)) hc)⟩
    obtain ⟨j, hj⟩ := neumannOperator_eigenvalue_is_indexed hb hL hnonneg hu0 hmem
    refine ⟨j, ?_⟩
    rw [hj, ENNReal.toReal_ofReal hnonneg]
    exact hc
  · rintro ⟨j, rfl⟩
    obtain ⟨u, hnorm, hAu⟩ := neumannEigenvalue_has_operator_eigenvector hb hL j
    refine ⟨u, ?_, hAu⟩
    intro hu0
    rw [hu0, norm_zero] at hnorm
    norm_num at hnorm

/-- All actual eigenspaces indexed by the original Neumann min–max sequence. -/
def neumannIndexedEigenvectors (Ω : Set ℂ) : Set (L2 Ω) :=
  {u | ∃ j : ℕ, u ∈ neumannOperatorEigenspace Ω (neumannEigenvalue Ω j).toReal}

/-- Completeness is proved using compactness of the true form resolvent and
strict positivity; it is not included as a hypothesis in the spectral bridge. -/
theorem dense_span_neumannIndexedEigenvectors {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) :
    Dense (Submodule.span ℂ (neumannIndexedEigenvectors Ω) : Set (L2 Ω)) := by
  apply (CompactSpectral.dense_span_positiveEigenvectors
    (neumannResolvent_compact hb hL) (neumannResolvent_isPositive Ω)
    (neumannResolvent_strictPositive hL.1.1)
    (L2_infinite_of_isOpen hL.1.1 hL.1.2.nonempty)).mono
  apply Submodule.span_mono
  intro u hu
  obtain ⟨eigenCoefficient, heigenCoefficient, hKu⟩ := hu
  obtain ⟨hd, hAu⟩ := neumann_operator_eigenpair_of_resolvent hL.1.1 heigenCoefficient hKu
  by_cases hu0 : u = 0
  · exact ⟨0, by rw [hu0]; exact Submodule.zero_mem _⟩
  · obtain ⟨j, hj⟩ := (neumannOperator_complex_eigenvalue_iff_indexed hb hL
      ((eigenCoefficient⁻¹ - 1 : ℝ) : ℂ)).mp ⟨⟨u, hd⟩, hu0, hAu⟩
    exact ⟨j, (mem_neumannOperatorEigenspace_iff Ω _ u).mpr ⟨hd, by rwa [hj] at hAu⟩⟩

/-- A regular spectral parameter means that `A - c I` has a bounded,
everywhere defined two-sided inverse. This is the usual resolvent definition
for a densely defined closed operator. -/
def NeumannRegularValue (Ω : Set ℂ) (c : ℂ) : Prop :=
  ∃ R : L2 Ω →L[ℂ] L2 Ω,
    (∀ f : L2 Ω, ∃ hf : R f ∈ (neumannOperator Ω).domain,
      neumannOperator Ω ⟨R f, hf⟩ - c • R f = f) ∧
    ∀ u : (neumannOperator Ω).domain,
      R (neumannOperator Ω u - c • (u : L2 Ω)) = (u : L2 Ω)

/-- The spectrum of the genuine unbounded Neumann operator, defined through
bounded resolvents and independently of the variational sequence. -/
def neumannOperatorSpectrum (Ω : Set ℂ) : Set ℂ :=
  {c | ¬ NeumannRegularValue Ω c}

theorem not_neumannRegularValue_of_eigenvector {Ω : Set ℂ} {c : ℂ}
    (u : (neumannOperator Ω).domain) (hu0 : (u : L2 Ω) ≠ 0)
    (hAu : neumannOperator Ω u = c • (u : L2 Ω)) :
    ¬ NeumannRegularValue Ω c := by
  rintro ⟨R, _, hR⟩
  have h := hR u
  rw [hAu, sub_self, map_zero] at h
  exact hu0 h.symm

/-- The Fredholm alternative applied to `I - (c + 1) K` supplies the
actual bounded inverse at every non-eigenvalue parameter. -/
theorem neumannRegularValue_of_not_eigenvalue {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {c : ℂ}
    (hNo : ¬ ∃ u : (neumannOperator Ω).domain, (u : L2 Ω) ≠ 0 ∧
      neumannOperator Ω u = c • (u : L2 Ω)) : NeumannRegularValue Ω c := by
  let C : L2 Ω →L[ℂ] L2 Ω := (-(c + 1)) • neumannResolvent Ω
  let F : L2 Ω →L[ℂ] L2 Ω := 1 + C
  have hF : ∀ x, F x = x - (c + 1) • neumannResolvent Ω x := by
    intro x
    simp only [F, C, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply, sub_eq_add_neg, neg_smul, id_eq]
  have hC : IsCompactOperator C := by
    have hCcoe : (C : L2 Ω → L2 Ω) = (-(c + 1)) • (neumannResolvent Ω : L2 Ω → L2 Ω) := by
      funext x
      simp only [C, ContinuousLinearMap.smul_apply, Pi.smul_apply]
    rw [hCcoe]
    exact (neumannResolvent_compact hb hL).smul (-(c + 1))
  have hinj : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    apply hNo
    have hxEq : x = (c + 1) • neumannResolvent Ω x := by
      rw [hF] at hx
      exact sub_eq_zero.mp hx
    refine ⟨neumannOperatorVector Ω x, ?_, ?_⟩
    · intro hu0
      exact hx0 ((neumannResolvent_injective hL.1.1).eq_iff.mp (by simpa using hu0))
    · rw [neumannOperator_apply_vector hL.1.1, neumannOperatorVector_coe]
      calc
        x - neumannResolvent Ω x = (c + 1) • neumannResolvent Ω x - neumannResolvent Ω x :=
          congrArg (fun y => y - neumannResolvent Ω x) hxEq
        _ = c • neumannResolvent Ω x := by
          rw [add_smul, one_smul, add_sub_cancel_right]
  have hsurj : Function.Surjective F := (injective_iff_surjective_one_add hC).mp hinj
  let e : L2 Ω ≃L[ℂ] L2 Ω := ContinuousLinearEquiv.ofBijective F
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  have he : ∀ x, e x = F x := fun x => rfl
  let R : L2 Ω →L[ℂ] L2 Ω := (neumannResolvent Ω).comp e.symm.toContinuousLinearMap
  refine ⟨R, ?_, ?_⟩
  · intro f
    have hd : R f ∈ (neumannOperator Ω).domain := by
      rw [neumannOperator_domain]
      exact ⟨e.symm f, rfl⟩
    refine ⟨hd, ?_⟩
    have hv : (⟨R f, hd⟩ : (neumannOperator Ω).domain) =
        neumannOperatorVector Ω (e.symm f) := Subtype.ext rfl
    rw [hv, neumannOperator_apply_vector hL.1.1]
    calc
      e.symm f - neumannResolvent Ω (e.symm f) - c • neumannResolvent Ω (e.symm f) =
          F (e.symm f) := by rw [hF, add_smul, one_smul]; abel
      _ = f := by rw [← he]; exact e.apply_symm_apply f
  · intro u
    have hFu : F (neumannOperator Ω u + (u : L2 Ω)) =
        neumannOperator Ω u - c • (u : L2 Ω) := by
      rw [hF, neumannResolvent_operator hL.1.1, add_smul, one_smul]
      abel
    change neumannResolvent Ω (e.symm (neumannOperator Ω u - c • (u : L2 Ω))) = _
    rw [← hFu, ← he, e.symm_apply_apply]
    exact neumannResolvent_operator hL.1.1 u

/-- The entire spectrum, with no continuous spectral remainder, is precisely
the original numbered Neumann min–max sequence. -/
theorem neumannOperatorSpectrum_eq_range {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) :
    neumannOperatorSpectrum Ω =
      Set.range (fun j : ℕ => ((neumannEigenvalue Ω j).toReal : ℂ)) := by
  ext c
  change (¬ NeumannRegularValue Ω c) ↔ ∃ j : ℕ, ((neumannEigenvalue Ω j).toReal : ℂ) = c
  constructor
  · intro hc
    have hEigen : ∃ u : (neumannOperator Ω).domain, (u : L2 Ω) ≠ 0 ∧
        neumannOperator Ω u = c • (u : L2 Ω) := by
      by_contra hNo
      exact hc (neumannRegularValue_of_not_eigenvalue hb hL hNo)
    obtain ⟨j, hj⟩ := (neumannOperator_complex_eigenvalue_iff_indexed hb hL c).mp hEigen
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨u, hnorm, hAu⟩ := neumannEigenvalue_has_operator_eigenvector hb hL j
    apply not_neumannRegularValue_of_eigenvector u _ hAu
    intro hu0
    rw [hu0, norm_zero] at hnorm
    norm_num at hnorm

end PolyaNeumann

end
