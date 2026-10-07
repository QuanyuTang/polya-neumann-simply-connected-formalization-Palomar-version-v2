module

public import RequestProject.TraceBound
public import RequestProject.NormAttained

/-!
# Spectral expansion of a unitary operator with compact `U - I`

For a unitary operator `U` on a complex Hilbert space with `U - I` compact, we list the
eigenvalues `z ≠ 1` with multiplicity through an orthonormal family of eigenvectors
`eigVec U p` (`p = (z, j)`, `j < mult(z)`), show that this family is complete in the sense that
every vector orthogonal to it is fixed by `U`, and deduce the expansion
`(U^k - I) x = ∑_p (z_p^k - 1) ⟨e_p, x⟩ e_p`. As a consequence, if `∑_p |z_p - 1| < ∞`, the
diagonal sum of `U^k - I` in any Hilbert basis is `∑_p (z_p^k - 1)`.
-/

@[expose] public section

open Filter
open scoped ComplexConjugate Topology

noncomputable section

namespace PolyaNeumann

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The index set listing the eigenvalues `z ≠ 1` of `U` with multiplicity. -/
abbrev EigIdx (U : H →L[ℂ] H) : Type := Σ z : {z : ℂ // z ≠ 1}, Fin (eigenMult U z)

/-- An orthonormal basis of each eigenspace, glued together: the eigenvector `e_p`. -/
def eigVec (U : H →L[ℂ] H) (p : EigIdx U) : H :=
  haveI : FiniteDimensional ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) (p.1 : ℂ)) :=
    Module.finite_of_finrank_pos (Fin.pos p.2)
  ((stdOrthonormalBasis ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) (p.1 : ℂ))) p.2 : H)

omit [CompleteSpace H] in
lemma eigVec_mem (U : H →L[ℂ] H) (p : EigIdx U) :
    eigVec U p ∈ Module.End.eigenspace (U : H →ₗ[ℂ] H) (p.1 : ℂ) := by
  unfold eigVec
  exact Submodule.coe_mem _

omit [CompleteSpace H] in
lemma eigVec_eigen (U : H →L[ℂ] H) (p : EigIdx U) :
    U (eigVec U p) = (p.1 : ℂ) • eigVec U p :=
  Module.End.mem_eigenspace_iff.mp (eigVec_mem U p)

lemma orthonormal_eigVec {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H)) :
    Orthonormal ℂ (eigVec U) := by
  rw [orthonormal_iff_ite]
  rintro ⟨⟨z, hz⟩, k⟩ ⟨⟨z', hz'⟩, k'⟩
  by_cases hzz : z = z'
  · subst hzz
    haveI : FiniteDimensional ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z) :=
      Module.finite_of_finrank_pos (Fin.pos k)
    have := (orthonormal_iff_ite.mp
      (stdOrthonormalBasis ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z)).orthonormal) k k'
    simp only [eigVec]
    rw [← Submodule.coe_inner, this]
    congr 1
    exact propext ⟨fun h => by subst h; rfl, fun h => by cases h; rfl⟩
  · have hv : eigVec U ⟨⟨z, hz⟩, k⟩ ≠ 0 := by
      haveI : FiniteDimensional ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z) :=
        Module.finite_of_finrank_pos (Fin.pos k)
      have := (stdOrthonormalBasis ℂ
        (Module.End.eigenspace (U : H →ₗ[ℂ] H) z)).orthonormal.ne_zero k
      simpa [eigVec] using this
    have hz1 : ‖(z : ℂ)‖ = 1 := norm_eq_one_of_eigen hU hv (eigVec_eigen U _)
    rw [inner_eq_zero_of_eigen_unitary hU (eigVec_eigen U _) (eigVec_eigen U ⟨⟨z', hz'⟩, k'⟩)
      (fun h => hzz h) hz1, if_neg]
    intro h; apply hzz; exact congrArg (fun p : EigIdx U => (p.1 : ℂ)) h

lemma norm_eigVal {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H)) (p : EigIdx U) :
    ‖(p.1 : ℂ)‖ = 1 :=
  norm_eq_one_of_eigen hU ((orthonormal_eigVec hU).ne_zero p) (eigVec_eigen U p)

omit [CompleteSpace H] in
/-- An eigenvector for `z ≠ 1` orthogonal to all `e_p` vanishes. -/
lemma eq_zero_of_eigen_of_orth {U : H →L[ℂ] H} (hC : IsCompactOperator ⇑(U - 1)) {z : ℂ}
    (hz : z ≠ 1) {v : H} (hv : U v = z • v) (horth : ∀ p : EigIdx U, inner ℂ (eigVec U p) v = 0) :
    v = 0 := by
  haveI := finiteDimensional_eigenspace hC hz
  set b := stdOrthonormalBasis ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z)
  have hvm : v ∈ Module.End.eigenspace (U : H →ₗ[ℂ] H) z := Module.End.mem_eigenspace_iff.mpr hv
  have h := b.sum_repr' ⟨v, hvm⟩
  have h0 : ∀ j, inner ℂ (b j) (⟨v, hvm⟩ : Module.End.eigenspace (U : H →ₗ[ℂ] H) z) = 0 := by
    intro j
    rw [Submodule.coe_inner]
    exact horth ⟨⟨z, hz⟩, j⟩
  simp only [h0, zero_smul, Finset.sum_const_zero] at h
  exact congrArg Subtype.val h.symm

/-- The adjoint of a unitary operator acts on an eigenvector by the conjugate eigenvalue. -/
lemma star_apply_of_eigen {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H)) {z : ℂ} {v : H}
    (hz : ‖z‖ = 1) (hv : U v = z • v) : star U v = conj z • v := by
  have h1 : star U (U v) = v := by
    rw [← ContinuousLinearMap.mul_apply, Unitary.star_mul_self_of_mem hU,
      ContinuousLinearMap.one_apply]
  rw [hv, map_smul] at h1
  have hzc : conj z * z = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  calc star U v = (conj z * z) • star U v := by rw [hzc, one_smul]
    _ = conj z • v := by rw [mul_smul, h1]

/-- **Completeness of the eigenvector family.** If `U` is unitary and `U - I` is compact, every
vector orthogonal to all eigenvectors `e_p` (eigenvalues `≠ 1`) is fixed by `U`. -/
theorem eigVec_complete {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) {v : H} (hv : ∀ p, inner ℂ (eigVec U p) v = 0) :
    U v = v := by
  set K : Submodule ℂ H := (Submodule.span ℂ (Set.range (eigVec U)))ᗮ with hKdef
  have memK : ∀ w, w ∈ K ↔ ∀ p, inner ℂ (eigVec U p) w = 0 := by
    intro w
    rw [hKdef, Submodule.mem_orthogonal]
    constructor
    · intro h p
      exact h _ (Submodule.subset_span ⟨p, rfl⟩)
    · intro h u hu
      induction hu using Submodule.span_induction with
      | mem x hx => obtain ⟨p, rfl⟩ := hx; exact h p
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
  have hstar_e : ∀ p, star U (eigVec U p) = conj (p.1 : ℂ) • eigVec U p := fun p =>
    star_apply_of_eigen hU (norm_eigVal hU p) (eigVec_eigen U p)
  have hUK : ∀ w ∈ K, U w ∈ K := by
    intro w hw
    rw [memK] at hw ⊢
    intro p
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint, hstar_e,
      inner_smul_left, hw, mul_zero]
  have hUsK : ∀ w ∈ K, star U w ∈ K := by
    intro w hw
    rw [memK] at hw ⊢
    intro p
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      eigVec_eigen, inner_smul_left, hw p, mul_zero]
  set P := K.starProjection with hPdef
  -- `P` commutes with any operator `A` such that `A` and `A^*` preserve `K`
  have hcomm : ∀ A : H →L[ℂ] H, (∀ w ∈ K, A w ∈ K) → (∀ w ∈ K, star A w ∈ K) →
      P * A = A * P := by
    intro A hA hAs
    ext x
    simp only [ContinuousLinearMap.mul_apply]
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hA _ (K.starProjection_apply_mem x))
      (fun w hw => ?_)
    rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint]
    exact Submodule.inner_left_of_mem_orthogonal (hAs w hw)
      (Submodule.sub_starProjection_mem_orthogonal x)
  have hPU : P * U = U * P := hcomm U hUK hUsK
  have hPUs : P * star U = star U * P := hcomm (star U) hUsK (by simpa using hUK)
  have hPs : star P = P :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr K.starProjection_isSymmetric
  have hPP : P * P = P := by
    ext x
    simp only [ContinuousLinearMap.mul_apply, hPdef]
    exact Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem x)
  set T : H →L[ℂ] H := (U - 1) * P with hTdef
  have hPA : P * (U - 1) = (U - 1) * P := by rw [mul_sub, sub_mul, hPU, mul_one, one_mul]
  have hPAs : P * (star U - 1) = (star U - 1) * P := by
    rw [mul_sub, sub_mul, hPUs, mul_one, one_mul]
  have hN : (star U - 1) * (U - 1) = (U - 1) * (star U - 1) := by
    have h1 := Unitary.star_mul_self_of_mem hU
    have h2 := Unitary.mul_star_self_of_mem hU
    simp only [sub_mul, mul_sub, h1, h2, one_mul, mul_one]
    abel
  have hTn : IsStarNormal T := by
    constructor
    have e1 : star T * T = (star U - 1) * (U - 1) * P := by
      rw [hTdef, star_mul, hPs, star_sub, star_one]
      calc P * (star U - 1) * ((U - 1) * P) = (star U - 1) * P * ((U - 1) * P) := by rw [hPAs]
        _ = (star U - 1) * (P * (U - 1)) * P := by simp only [mul_assoc]
        _ = (star U - 1) * ((U - 1) * P) * P := by rw [hPA]
        _ = (star U - 1) * (U - 1) * (P * P) := by simp only [mul_assoc]
        _ = (star U - 1) * (U - 1) * P := by rw [hPP]
    have e2 : T * star T = (U - 1) * (star U - 1) * P := by
      rw [hTdef, star_mul, hPs, star_sub, star_one]
      calc (U - 1) * P * (P * (star U - 1)) = (U - 1) * ((P * P) * (star U - 1)) := by
              simp only [mul_assoc]
        _ = (U - 1) * ((star U - 1) * P) := by rw [hPP, hPAs]
        _ = (U - 1) * (star U - 1) * P := by rw [mul_assoc]
    rw [Commute, SemiconjBy, e1, e2, hN]
  have hTc : IsCompactOperator T := hC.comp_clm P
  by_cases hT0 : T = 0
  · have hPv : P v = v := Submodule.starProjection_eq_self_iff.mpr ((memK v).mpr hv)
    have : T v = 0 := by rw [hT0]; rfl
    rw [hTdef, ContinuousLinearMap.mul_apply, hPv, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, sub_eq_zero] at this
    exact this
  · exfalso
    haveI : Nontrivial H := by
      by_contra hH
      rw [not_nontrivial_iff_subsingleton] at hH
      exact hT0 (ContinuousLinearMap.ext fun x => Subsingleton.elim _ _)
    obtain ⟨k, hk, hkn⟩ := spectrum.exists_nnnorm_eq_spectralRadius T
    rw [IsStarNormal.spectralRadius_eq_nnnorm, ENNReal.coe_inj] at hkn
    have hkn' : ‖k‖ = ‖T‖ := congrArg NNReal.toReal hkn
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [norm_zero, eq_comm, norm_eq_zero] at hkn'
      exact hT0 hkn'
    obtain ⟨w, hw0, hw⟩ := exists_eigenvector_of_mem_spectrum hTc hk hk0
    have hTK : T w ∈ K := by
      rw [hTdef, ContinuousLinearMap.mul_apply]
      have : (U - 1) (P w) = P ((U - 1) w) := by
        rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, mul_sub, sub_mul,
          hPU, mul_one, one_mul]
      rw [this]
      exact K.starProjection_apply_mem _
    have hwK : w ∈ K := by
      have : w = k⁻¹ • T w := by rw [hw, smul_smul, inv_mul_cancel₀ hk0, one_smul]
      rw [this]
      exact K.smul_mem _ hTK
    have hPw : P w = w := Submodule.starProjection_eq_self_iff.mpr hwK
    have hUw : U w = (1 + k) • w := by
      rw [hTdef, ContinuousLinearMap.mul_apply, hPw, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.one_apply] at hw
      rw [add_smul, one_smul, ← hw]; abel
    have hk1 : (1 + k) ≠ 1 := by intro h; apply hk0; linear_combination h
    exact hw0 (eq_zero_of_eigen_of_orth hC hk1 hUw ((memK w).mp hwK))

/-- The orthogonal series `∑_p ⟨e_p, x⟩ e_p` is summable. -/
lemma summable_inner_smul_eigVec {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H)) (x : H) :
    Summable (fun p => inner ℂ (eigVec U p) x • eigVec U p) :=
  ((orthonormal_eigVec hU).orthogonalFamily.summable_iff_norm_sq_summable
    (fun p => inner ℂ (eigVec U p) x)).mpr ((orthonormal_eigVec hU).inner_products_summable x)

/-- **Spectral expansion.** For `U` unitary with `U - I` compact and every `k`,
`(U^k - I) x = ∑_p (z_p^k - 1) ⟨e_p, x⟩ e_p`. -/
theorem hasSum_pow_sub_one_apply {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) (k : ℕ) (x : H) :
    HasSum (fun p : EigIdx U => (((p.1 : ℂ) ^ k - 1) * inner ℂ (eigVec U p) x) • eigVec U p)
      ((U ^ k - 1) x) := by
  have he := orthonormal_eigVec hU
  set s := ∑' p, inner ℂ (eigVec U p) x • eigVec U p with hs
  have hsum := (summable_inner_smul_eigVec hU x).hasSum
  have horth : ∀ q, inner ℂ (eigVec U q) (x - s) = 0 := by
    intro q
    have h1 := hsum.mapL (innerSL ℂ (eigVec U q))
    simp only [innerSL_apply_apply, inner_smul_right] at h1
    have h2 : HasSum (fun p => inner ℂ (eigVec U p) x * inner ℂ (eigVec U q) (eigVec U p))
        (inner ℂ (eigVec U q) x) := by
      have : (fun p => inner ℂ (eigVec U p) x * inner ℂ (eigVec U q) (eigVec U p)) =
          fun p => if p = q then inner ℂ (eigVec U q) x else 0 := by
        funext p
        rw [orthonormal_iff_ite.mp he q p]
        by_cases h : p = q
        · subst h; simp
        · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
      rw [this]
      exact hasSum_ite_eq q _
    rw [inner_sub_right, h1.unique h2, sub_self]
  have hfix : ∀ n : ℕ, (U ^ n) (x - s) = x - s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, eigVec_complete hU hC horth]
  have hpow : ∀ (n : ℕ) (p : EigIdx U), (U ^ n) (eigVec U p) = ((p.1 : ℂ) ^ n) • eigVec U p := by
    intro n p
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, eigVec_eigen, smul_smul,
        pow_succ', mul_comm]
  have h1 : (U ^ k - 1) x = (U ^ k - 1) s := by
    have := hfix k
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply]
    rw [map_sub] at this
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact this
  rw [h1]
  have := hsum.mapL (U ^ k - 1)
  convert this using 1
  funext p
  rw [map_smul, ContinuousLinearMap.sub_apply, hpow, ContinuousLinearMap.one_apply, smul_sub,
    smul_smul, sub_mul, one_mul, sub_smul, mul_comm]

/-- The quadratic form of `U^k - I`: `⟨y, (U^k - I) x⟩ = ∑_p (z_p^k - 1) ⟨e_p, x⟩ ⟨y, e_p⟩`. -/
theorem hasSum_inner_pow_sub_one {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) (k : ℕ) (x y : H) :
    HasSum (fun p : EigIdx U => ((p.1 : ℂ) ^ k - 1) * inner ℂ (eigVec U p) x *
      inner ℂ y (eigVec U p)) (inner ℂ y ((U ^ k - 1) x)) := by
  have := (hasSum_pow_sub_one_apply hU hC k x).mapL (innerSL ℂ y)
  simpa only [innerSL_apply_apply, inner_smul_right] using this

/-- **Trace of `U^k - I`.** If `∑_p |z_p^k - 1| < ∞`, the diagonal sum of `U^k - I` in any
Hilbert basis is `∑_p (z_p^k - 1)`. -/
theorem hasSum_trace_pow_sub_one {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) {ι : Type*} (b : HilbertBasis ι ℂ H) (k : ℕ)
    (hs : Summable (fun p : EigIdx U => ‖(p.1 : ℂ) ^ k - 1‖)) :
    HasSum (fun n => inner ℂ (b n) ((U ^ k - 1) (b n)))
      (∑' p : EigIdx U, ((p.1 : ℂ) ^ k - 1)) := by
  have he := orthonormal_eigVec hU
  set F : EigIdx U × ι → ℂ := fun q => ((q.1.1 : ℂ) ^ k - 1) * inner ℂ (eigVec U q.1) (b q.2) *
    inner ℂ (b q.2) (eigVec U q.1) with hF
  have hfib : ∀ p : EigIdx U, HasSum (fun n => F (p, n)) ((p.1 : ℂ) ^ k - 1) := by
    intro p
    have := (b.hasSum_inner_mul_inner (eigVec U p) (eigVec U p)).mul_left ((p.1 : ℂ) ^ k - 1)
    rw [inner_self_eq_norm_sq_to_K, he.1 p, RCLike.ofReal_one, one_pow, mul_one] at this
    simpa only [hF, mul_assoc] using this
  have hnorm : ∀ q, ‖F q‖ = ‖(q.1.1 : ℂ) ^ k - 1‖ * ‖inner ℂ (b q.2) (eigVec U q.1)‖ ^ 2 := by
    intro q
    rw [hF]
    simp only [norm_mul]
    rw [← inner_conj_symm, RCLike.norm_conj]
    ring
  have hfibn : ∀ p : EigIdx U, HasSum (fun n => ‖F (p, n)‖) ‖(p.1 : ℂ) ^ k - 1‖ := by
    intro p
    simp only [hnorm]
    have h1 := (b.hasSum_inner_mul_inner (eigVec U p) (eigVec U p))
    rw [inner_self_eq_norm_sq_to_K, he.1 p] at h1
    have h2 : HasSum (fun n => ‖inner ℂ (b n) (eigVec U p)‖ ^ 2) 1 := by
      have := Complex.hasSum_re h1
      convert this using 1
      · funext n
        rw [← inner_conj_symm (b n) (eigVec U p), RCLike.norm_conj, Complex.mul_conj,
          Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      · simp
    simpa using h2.mul_left ‖(p.1 : ℂ) ^ k - 1‖
  have hFs : Summable F := by
    refine Summable.of_norm ?_
    rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    exact ⟨fun p => (hfibn p).summable, by simpa only [(hfibn _).tsum_eq] using hs⟩
  have hA := hFs.hasSum
  have h1 : HasSum (fun p : EigIdx U => ((p.1 : ℂ) ^ k - 1)) (∑' q, F q) :=
    hA.prod_fiberwise hfib
  have hn : ∀ n, HasSum (fun p => F (p, n)) (inner ℂ (b n) ((U ^ k - 1) (b n))) := fun n =>
    hasSum_inner_pow_sub_one hU hC k (b n) (b n)
  have hA' : HasSum (F ∘ Prod.swap) (∑' q, F q) :=
    (Equiv.prodComm ι (EigIdx U)).hasSum_iff.mpr hA
  have h2 := hA'.prod_fiberwise (fun n => hn n)
  rw [h1.tsum_eq]
  exact h2

end PolyaNeumann

end
