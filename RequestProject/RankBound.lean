module

public import RequestProject.Coercivity

/-!
# Uniform Cayley bound and resonance rank (Lemmas 7.8, 7.9 and Proposition 7.10)

This file formalizes the functional-analytic core of the end of Section 7 of the paper.

* **Lemma 7.8 (reduced lower bound)** `reduced_lower_bound`: if `E ↦ R_E` and `E ↦ S_E` are
  operator-norm continuous at `E₀`, `R_{E₀} = α I + C` with `α > 0`, `C` compact, and `S_{E₀}`
  is injective, then there is `A₀ > 0` with `Re ⟨z, R_E z⟩ ≥ -A₀ ‖S_E z‖²` for all `E` near `E₀`.
  (In the paper `R_E` is the reduced form on the subspace `Z`, on which its pole vanishes, so
  only its regular part enters.)
* **Lemma 7.9 (boundary lower bound with finitely many conditions)** `boundary_lower_bound`:
  the algebraic deduction of `Re ⟨g, 𝒜_E g⟩ ≥ -(A₀ + b) ‖O_E^* g‖²` on `{g : L_E g = 0}` from
  the decomposition identities and the reduced lower bound, where `‖B_E‖ ≤ b`.
* **Proposition 7.10 (uniform Cayley bound and resonance rank)**
  `finrank_le_of_boundary_bound`, `card_le_of_boundary_bound`: under the boundary lower bound
  with `m` linear conditions and the Cayley factorization `⟨g, 𝒜_E g⟩ = -⟨x, K_E x⟩`,
  `x = O_E^* g`, every orthonormal family of eigenvectors of `K_E` with eigenvalues `> A ≥ A₁`
  lying in the range of `O_E^*` has at most `m` members; for `m = 0` there are none.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open InnerProductSpace ContinuousLinearMap Filter Topology Module
open scoped InnerProductSpace

/-! ### Lemma 7.8 -/

section Reduced

variable {Z Y : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [CompleteSpace Z]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- **Lemma 7.8 (reduced lower bound).** Let `E ↦ R_E : Z → Z` and `E ↦ S_E : Z → Y` be
operator-norm continuous at `E₀`, with `R_{E₀} = α I + C` (`α > 0`, `C` compact) and `S_{E₀}`
injective. Then there is `A₀ > 0` such that for all `E` near `E₀`,
`Re ⟨z, R_E z⟩ ≥ -A₀ ‖S_E z‖²` for every `z`. -/
theorem reduced_lower_bound (α : ℝ) (hα : 0 < α) (C : Z →L[ℂ] Z) (hC : IsCompactOperator C)
    (R : ℝ → Z →L[ℂ] Z) (S : ℝ → Z →L[ℂ] Y) (E₀ : ℝ) (hR : ContinuousAt R E₀)
    (hS : ContinuousAt S E₀) (hR₀ : R E₀ = (α : ℂ) • ContinuousLinearMap.id ℂ Z + C)
    (hinj : Function.Injective (S E₀)) :
    ∃ A₀ > 0, ∀ᶠ E in 𝓝 E₀, ∀ z : Z, -(A₀ * ‖S E z‖ ^ 2) ≤ (⟪z, R E z⟫_ℂ).re := by
  obtain ⟨A, hA, ε, hε, δ, hδ, h⟩ := compact_perturbation_coercive_nhds α hα C hC (S E₀) hinj
  refine ⟨A, hA, ?_⟩
  have h1 : ∀ᶠ E in 𝓝 E₀, ‖R E - R E₀‖ < δ := by
    have := (hR.sub_const (R E₀)).norm
    simp only [sub_self, norm_zero] at this
    exact this.eventually (gt_mem_nhds hδ)
  have h2 : ∀ᶠ E in 𝓝 E₀, ‖S E - S E₀‖ < δ := by
    have := (hS.sub_const (S E₀)).norm
    simp only [sub_self, norm_zero] at this
    exact this.eventually (gt_mem_nhds hδ)
  filter_upwards [h1, h2] with E hE1 hE2 z
  rw [hR₀] at hE1
  have := h (R E) (S E) hE1 hE2 z
  have : 0 ≤ ε / 2 * ‖z‖ ^ 2 := by positivity
  linarith

end Reduced

/-! ### Lemma 7.9 -/

section Boundary

variable {G X W : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- **Lemma 7.9 (boundary lower bound with finitely many conditions).** Let `G` carry the
form `𝒜 = 𝒫 - O B O^*`, i.e. `Re ⟨g, 𝒜 g⟩ = Re ⟨g, 𝒫 g⟩ - Re ⟨O^* g, B O^* g⟩`. Suppose `g`
decomposes with a component `z(g) ∈ W` (the `z` of `Λ^{-1/2} g = Ĵ a + R z`) such that
`Re ⟨g, 𝒫 g⟩ = Re ⟨z(g), 𝓡 z(g)⟩` and `T^♯ g = 𝓢 z(g) = Π (O^* g)` with `‖Π‖ ≤ 1`. If the
reduced bound `Re ⟨z, 𝓡 z⟩ ≥ -A₀ ‖𝓢 z‖²` holds on `Z = ker ℓ` (`ℓ : W → ℂ^m`) and
`‖B‖ ≤ b`, then with `L g = ℓ (z(g))`,
`Re ⟨g, 𝒜 g⟩ ≥ -(A₀ + b) ‖O^* g‖²` whenever `L g = 0`. -/
theorem boundary_lower_bound {m : ℕ} (Aop Pop : G →L[ℂ] G) (B : X →L[ℂ] X)
    (Oadj : G →L[ℂ] X) (Pi : X →L[ℂ] X) (hPi : ‖Pi‖ ≤ 1) (zc : G →ₗ[ℂ] W)
    (Rr : W →L[ℂ] W) (Sr : W →L[ℂ] X) (ℓ : W →ₗ[ℂ] (Fin m → ℂ)) (A₀ b : ℝ) (hA₀ : 0 ≤ A₀)
    (hb : ‖B‖ ≤ b)
    (hA : ∀ g, (⟪g, Aop g⟫_ℂ).re = (⟪g, Pop g⟫_ℂ).re - (⟪Oadj g, B (Oadj g)⟫_ℂ).re)
    (hP : ∀ g, (⟪g, Pop g⟫_ℂ).re = (⟪zc g, Rr (zc g)⟫_ℂ).re)
    (hT : ∀ g, Sr (zc g) = Pi (Oadj g))
    (hred : ∀ z, ℓ z = 0 → -(A₀ * ‖Sr z‖ ^ 2) ≤ (⟪z, Rr z⟫_ℂ).re) :
    ∀ g, ℓ (zc g) = 0 → -((A₀ + b) * ‖Oadj g‖ ^ 2) ≤ (⟪g, Aop g⟫_ℂ).re := by
  intro g hg
  have h1 := hred _ hg
  rw [hT, ← hP] at h1
  have h2 : ‖Pi (Oadj g)‖ ≤ ‖Oadj g‖ :=
    (Pi.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right hPi (norm_nonneg _))
  have h3 : ‖Pi (Oadj g)‖ ^ 2 ≤ ‖Oadj g‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h4 : (⟪Oadj g, B (Oadj g)⟫_ℂ).re ≤ b * ‖Oadj g‖ ^ 2 := by
    calc (⟪Oadj g, B (Oadj g)⟫_ℂ).re ≤ ‖⟪Oadj g, B (Oadj g)⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖Oadj g‖ * ‖B (Oadj g)‖ := norm_inner_le_norm _ _
      _ ≤ ‖Oadj g‖ * (‖B‖ * ‖Oadj g‖) := by gcongr; exact B.le_opNorm _
      _ ≤ ‖Oadj g‖ * (b * ‖Oadj g‖) := by gcongr
      _ = b * ‖Oadj g‖ ^ 2 := by ring
  rw [hA]
  nlinarith [mul_le_mul_of_nonneg_left h3 hA₀]

end Boundary

/-! ### Proposition 7.10 -/

section Rank

variable {G X : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- **Proposition 7.10, counting argument.** Let `q` be a real form on `G` satisfying the
boundary lower bound `q g ≥ -A₁ ‖O^* g‖²` on the kernel of a linear map `L : G → ℂ^m`, and
suppose that on a subspace `H ⊆ G` (the Herglotz traces) the factorization `q g = -k (O^* g)`
holds. Then every finite-dimensional subspace `V ⊆ O^*(H)` on which `k x > A ‖x‖²` for
`x ≠ 0`, with `A ≥ A₁`, has dimension at most `m`. -/
theorem finrank_le_of_boundary_bound {m : ℕ} (q : G → ℝ) (Oadj : G →ₗ[ℂ] X)
    (L : G →ₗ[ℂ] (Fin m → ℂ)) (A₁ A : ℝ) (hA : A₁ ≤ A)
    (hbound : ∀ g, L g = 0 → -(A₁ * ‖Oadj g‖ ^ 2) ≤ q g)
    (k : X → ℝ) (Hg : Submodule ℂ G) (hfac : ∀ g ∈ Hg, q g = -k (Oadj g))
    (V : Submodule ℂ X) [FiniteDimensional ℂ V] (hV : V ≤ Hg.map Oadj)
    (hpos : ∀ x ∈ V, x ≠ 0 → A * ‖x‖ ^ 2 < k x) :
    finrank ℂ V ≤ m := by
  by_contra hlt
  push_neg at hlt
  set n := finrank ℂ V
  let bV := Module.finBasis ℂ V
  have hlift : ∀ i : Fin n, ∃ g ∈ Hg, Oadj g = (bV i : X) := fun i => by
    obtain ⟨g, hg, hgx⟩ := Submodule.mem_map.mp (hV (bV i).2)
    exact ⟨g, hg, hgx⟩
  choose gs hgsH hgs using hlift
  let φ : (Fin n → ℂ) →ₗ[ℂ] G := Fintype.linearCombination ℂ gs
  have hker : LinearMap.ker (L ∘ₗ φ) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hlt)
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker, LinearMap.comp_apply] at hc
  set g := φ c with hgdef
  have hgH : g ∈ Hg := by
    simp only [hgdef, φ, Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hgsH i)
  have hx : Oadj g = ((∑ i, c i • bV i : V) : X) := by
    simp [hgdef, φ, Fintype.linearCombination_apply, map_sum, hgs]
  have hxV : Oadj g ∈ V := by rw [hx]; exact Submodule.coe_mem _
  have hx0 : Oadj g ≠ 0 := by
    rw [hx]
    intro h0
    apply hc0
    have h1 : (∑ i, c i • bV i : V) = 0 := Subtype.ext h0
    exact funext (Fintype.linearIndependent_iff.mp bV.linearIndependent c h1)
  have hk := hpos _ hxV hx0
  have hq := hbound g hc
  rw [hfac g hgH] at hq
  have hn : 0 < ‖Oadj g‖ ^ 2 := by positivity
  nlinarith

/-- **Proposition 7.10 (resonance rank bound).** Let `K` be a linear operator (possibly
unbounded) on `X`, let `𝒜` satisfy the boundary lower bound
`Re ⟨g, 𝒜 g⟩ ≥ -A₁ ‖O^* g‖²` whenever `L g = 0`, `L : G → ℂ^m`, and suppose the Cayley
factorization holds on a subspace `H ⊆ G`: `O^* g ∈ Dom K` and
`Re ⟨g, 𝒜 g⟩ = -Re ⟨O^* g, K O^* g⟩` for `g ∈ H`. Then every orthonormal family
`(e_i)` of eigenvectors of `K` with eigenvalues `λ_i > A ≥ A₁`, all lying in `O^*(H)`, has at
most `m` members. In particular (`m = 0`) no such eigenvector exists, i.e. `K ≤ A`
on eigenvectors. -/
theorem card_le_of_boundary_bound {m : ℕ} {ι : Type*} [Fintype ι] (Aop : G →L[ℂ] G)
    (Oadj : G →ₗ[ℂ] X) (L : G →ₗ[ℂ] (Fin m → ℂ)) (A₁ A : ℝ) (hA : A₁ ≤ A)
    (hbound : ∀ g, L g = 0 → -(A₁ * ‖Oadj g‖ ^ 2) ≤ (⟪g, Aop g⟫_ℂ).re)
    (K : X →ₗ.[ℂ] X) (Hg : Submodule ℂ G)
    (hdom : ∀ g ∈ Hg, Oadj g ∈ K.domain)
    (hfac : ∀ g (hg : g ∈ Hg),
      (⟪g, Aop g⟫_ℂ).re = -(⟪Oadj g, K ⟨Oadj g, hdom g hg⟩⟫_ℂ).re)
    (e : ι → X) (he : Orthonormal ℂ e) (ev : ι → ℝ) (hev : ∀ i, A < ev i)
    (heK : ∀ i, ∃ h : e i ∈ K.domain, K ⟨e i, h⟩ = (ev i : ℂ) • e i)
    (hran : ∀ i, ∃ g ∈ Hg, Oadj g = e i) :
    Fintype.card ι ≤ m := by
  classical
  set V := Submodule.span ℂ (Set.range e)
  let k : X → ℝ := fun x => if h : x ∈ K.domain then (⟪x, K ⟨x, h⟩⟫_ℂ).re else 0
  -- every combination of the eigenvectors is in the domain, with the expected image
  have hKsum : ∀ c : ι → ℂ, ∃ h : (∑ i, c i • e i) ∈ K.domain,
      K ⟨∑ i, c i • e i, h⟩ = ∑ i, (c i * ev i) • e i := by
    intro c
    choose hd hK using heK
    have hmem : (∑ i, c i • e i) ∈ K.domain :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hd i)
    refine ⟨hmem, ?_⟩
    have he' : (⟨∑ i, c i • e i, hmem⟩ : K.domain) = ∑ i, c i • (⟨e i, hd i⟩ : K.domain) := by
      ext; simp
    rw [he']
    change K.toFun _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    change c i • K ⟨e i, hd i⟩ = _
    rw [hK i, smul_smul]
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
  have hcard := finrank_span_eq_card he.linearIndependent
  rw [← hcard]
  refine finrank_le_of_boundary_bound (fun g => (⟪g, Aop g⟫_ℂ).re) Oadj L A₁ A hA hbound k Hg
    (fun g hg => by simp only [k, dif_pos (hdom g hg)]; exact hfac g hg) V ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨g, hg, hge⟩ := hran i
    exact Submodule.mem_map.mpr ⟨g, hg, hge⟩
  · intro x hx hx0
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
    obtain ⟨hmem, hK⟩ := hKsum c
    simp only [k, dif_pos hmem, hK]
    rw [he.inner_sum c (fun i => c i * ev i) Finset.univ]
    have hn : ‖∑ i, c i • e i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), he.inner_sum c c Finset.univ]
      simp [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]
    rw [hn, Complex.re_sum, Finset.mul_sum]
    have hterm : ∀ i, ((starRingEnd ℂ) (c i) * (c i * (ev i : ℂ))).re = ev i * ‖c i‖ ^ 2 := by
      intro i
      rw [← mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      simp only [← Complex.ofReal_mul, Complex.ofReal_re]
      ring
    simp only [hterm]
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hx0 (by simp [hall])
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_right (hev i).le (by positivity)
    · exact ⟨j, Finset.mem_univ _, mul_lt_mul_of_pos_right (hev j) (by positivity)⟩

/-- **Proposition 7.10, nonresonant case (`m = 0`).** If the boundary lower bound
`Re ⟨g, 𝒜 g⟩ ≥ -A₁ ‖O^* g‖²` holds without conditions and the Cayley factorization holds on
`H`, then `K` has no eigenvector in `O^*(H)` with eigenvalue `> A ≥ A₁`. -/
theorem no_eigenvector_of_boundary_bound (Aop : G →L[ℂ] G) (Oadj : G →ₗ[ℂ] X) (A₁ A : ℝ)
    (hA : A₁ ≤ A) (hbound : ∀ g, -(A₁ * ‖Oadj g‖ ^ 2) ≤ (⟪g, Aop g⟫_ℂ).re)
    (K : X →ₗ.[ℂ] X) (Hg : Submodule ℂ G) (hdom : ∀ g ∈ Hg, Oadj g ∈ K.domain)
    (hfac : ∀ g (hg : g ∈ Hg),
      (⟪g, Aop g⟫_ℂ).re = -(⟪Oadj g, K ⟨Oadj g, hdom g hg⟩⟫_ℂ).re)
    (x : X) (hx : x ∈ K.domain) (hx0 : x ≠ 0) (ev : ℝ) (hKx : K ⟨x, hx⟩ = (ev : ℂ) • x)
    (hran : ∃ g ∈ Hg, Oadj g = x) : ev ≤ A := by
  by_contra hlt
  push_neg at hlt
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  set e : Unit → X := fun _ => (‖x‖⁻¹ : ℂ) • x
  have he : Orthonormal ℂ e := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [e, Subsingleton.elim i j, if_true, inner_self_eq_norm_sq_to_K, norm_smul]
    simp [hn]
  have hdomx : ∀ i, e i ∈ K.domain := fun _ => Submodule.smul_mem _ _ hx
  have := card_le_of_boundary_bound (m := 0) Aop Oadj 0 A₁ A hA (fun g _ => hbound g) K Hg hdom
    hfac e he (fun _ => ev) (fun _ => hlt)
    (fun i => ⟨hdomx i, by
      have h1 : (⟨e i, hdomx i⟩ : K.domain) = (‖x‖⁻¹ : ℂ) • ⟨x, hx⟩ := rfl
      rw [h1, LinearPMap.map_smul, hKx, smul_comm]⟩)
    (fun _ => by
      obtain ⟨g, hg, hgx⟩ := hran
      exact ⟨(‖x‖⁻¹ : ℂ) • g, Hg.smul_mem _ hg, by rw [map_smul, hgx]⟩)
  simp at this

end Rank

end PolyaNeumann
