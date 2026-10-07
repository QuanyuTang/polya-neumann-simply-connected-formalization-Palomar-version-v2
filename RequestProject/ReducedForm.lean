module

public import RequestProject.RankBound
public import RequestProject.FiniteRankCompletion
public import RequestProject.SobolevMultiplier

/-!
# Reduced forms of Section 7 (Lemmas 7.4, 7.5, 7.8 and the chart reduction of Lemma 7.9)

This file formalizes the functional-analytic deductions of Lemmas 7.4–7.9 of the paper
(numbered as in `RankBound.lean`) that sit between the chart of Lemma 7.3 (`exists_fixed_complement`) and the boundary lower bound.
The analytic inputs (the nullspace identities of Lemma 6.12, the pole structure of Lemma 6.5,
the regular part of Lemma 6.7, and the injectivity of Lemma 7.5) are hypotheses here.

Throughout, `H = H₀ ⊕ H₀ᗮ` is a Hilbert space (in the paper `L²(𝕋)` with `H₀` the nonpositive
modes), `J E : H₀ → H` is the normalized conormal transmutation `Ĵ_E`, `R : H₀ᗮ → H` is the
fixed complement and `𝔅_E = J E ∘ Π₀ + R ∘ Π₁` is the chart of Lemma 7.3.

* **Lemma 7.4 (regularity and dimension of the reduction), dimension part**
  (`linearIndependent_adjoint_of_surjective`): if `𝔅_{E₀}` is surjective and `w₁, …, w_m` are linearly independent vectors annihilating `ran Ĵ_{E₀}`, then
  `η_j = R^* w_j` are linearly independent.
* **Lemma 7.4, pole part** (`inner_pole_add_eq_of_orthogonal`): the reduced pole
  `-2/(E-E₀) ∑ η_j ⟨η_j, ·⟩` vanishes identically on `Z = {z : ⟨η_j, z⟩ = 0}`.
* **Lemma 7.5 (injectivity after reduction), last step** (`chart_range_inter_eq_zero`): if
  `𝔅_{E₀}` is injective and `R z ∈ ran Ĵ_{E₀}`, then `z = 0`.
* **Lemma 7.5, Sobolev bootstrap** (`sobolev_bootstrap`): a fixed point of a map gaining `δ`
  derivatives lies in every `H^{nδ}`.
* **Lemma 7.8 (reduced lower bound) on `Z`** (`reduced_lower_bound_subspace`): the coercivity
  argument applied on a closed subspace `Z`.
* **Lemma 7.9, chart reduction** (`chart_reduced_boundary_bound`): from the chart, the nullspace
  identities and the pole structure, `Re ⟨y, P̂_E y⟩ ≥ -A₀ ‖Ŝ_E y‖²` on the kernel of a linear
  map `ℓ_E : H → ℂ^m`, uniformly for `E ≠ E₀` near `E₀`; with the splitting
  `𝒜_E = P̂_E - O_E B_E O_E^*` and `Ŝ_E = Π_E O_E^*` this gives
  `Re ⟨y, 𝒜_E y⟩ ≥ -A₁ ‖O_E^* y‖²` on `ker ℓ_E` (`chart_boundary_lower_bound`).
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open InnerProductSpace ContinuousLinearMap Filter Topology Module
open scoped InnerProductSpace

/-! ### Lemma 7.4, dimension part -/

section Dimension

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

omit [CompleteSpace A] in
/-- **Lemma 7.4 (linear independence of `η_j`).** Let `(a, z) ↦ Ĵ a + R z` be surjective onto
`H`, and let `w₁, …, w_m ∈ H` be linearly independent and orthogonal to `ran Ĵ` (in the paper
`w_j = Λ^{1/2} h_j`, orthogonal to `ran Ĵ_{E₀}` by Green's identity). Then the vectors
`η_j = R^* w_j` are linearly independent. -/
theorem linearIndependent_adjoint_of_surjective {m : ℕ} (J₀ : A →L[ℂ] H) (R : B →L[ℂ] H)
    (hsurj : ∀ y : H, ∃ a z, J₀ a + R z = y) (w : Fin m → H) (hw : LinearIndependent ℂ w)
    (hann : ∀ j a, ⟪w j, J₀ a⟫_ℂ = 0) :
    LinearIndependent ℂ (fun j => adjoint R (w j)) := by
  rw [Fintype.linearIndependent_iff] at hw ⊢
  intro g hg
  apply hw g
  set v := ∑ i, g i • w i with hv
  have hRv : adjoint R v = 0 := by
    simpa [v, map_sum, map_smul] using hg
  have hall : ∀ y, ⟪v, y⟫_ℂ = 0 := by
    intro y
    obtain ⟨a, z, hy⟩ := hsurj y
    rw [← hy, inner_add_right]
    have h1 : ⟪v, J₀ a⟫_ℂ = 0 := by
      simp only [v, sum_inner, inner_smul_left, hann, mul_zero, Finset.sum_const_zero]
    have h2 : ⟪v, R z⟫_ℂ = 0 := by
      rw [← adjoint_inner_left, hRv, inner_zero_left]
    rw [h1, h2, add_zero]
  exact inner_self_eq_zero.1 (hall v)

end Dimension

/-! ### Lemma 7.4, pole part, and Lemma 7.5 -/

section Pole

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- **Lemma 7.4 (the reduced pole vanishes on `Z`).** If `⟨η_j, z⟩ = 0` for all `j`, then for
every scalar `c` (in the paper `c = -2/(E - E₀)`) and every operator `T`,
`⟨z, (c ∑ η_j ⟨η_j, ·⟩ + T) z⟩ = ⟨z, T z⟩`. -/
theorem inner_pole_add_eq_of_orthogonal {m : ℕ} (η : Fin m → W) (c : ℂ) (T : W →L[ℂ] W)
    (z : W) (hz : ∀ j, ⟪η j, z⟫_ℂ = 0) :
    ⟪z, (c • ∑ j, rankOne ℂ (η j) (η j) + T) z⟫_ℂ = ⟪z, T z⟫_ℂ := by
  simp [rankOne_apply, hz]

end Pole

section Chart

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (H₀ : Submodule ℂ H) [H₀.HasOrthogonalProjection]

omit [CompleteSpace H] in
/-- **Lemma 7.5, last step.** If the chart `𝔅 = Ĵ Π₀ + R Π₁` is injective and `R z = Ĵ a`
for some `z ∈ H₀ᗮ`, `a ∈ H₀`, then `z = 0` (and `a = 0`). -/
theorem chart_range_inter_eq_zero (J₀ : H₀ →L[ℂ] H) (R : H₀ᗮ →L[ℂ] H)
    (hinj : Function.Injective (J₀ ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection))
    (a : H₀) (z : H₀ᗮ) (h : R z = J₀ a) : z = 0 ∧ a = 0 := by
  set x : H := (z : H) - (a : H) with hx
  have hz0 : H₀.orthogonalProjection (z : H) = 0 :=
    (Submodule.orthogonalProjection_eq_zero_iff).2 z.2
  have ha0 : H₀ᗮ.orthogonalProjection (a : H) = 0 :=
    (Submodule.orthogonalProjection_eq_zero_iff (K := H₀ᗮ)).2
      (Submodule.le_orthogonal_orthogonal H₀ a.2)
  have haa : H₀.orthogonalProjection (a : H) = a :=
    Submodule.orthogonalProjection_mem_subspace_eq_self a
  have hzz : H₀ᗮ.orthogonalProjection (z : H) = z :=
    Submodule.orthogonalProjection_mem_subspace_eq_self z
  have hP0 : H₀.orthogonalProjection x = -a := by
    rw [hx, map_sub, hz0, haa, zero_sub]
  have hP1 : H₀ᗮ.orthogonalProjection x = z := by
    rw [hx, map_sub, ha0, hzz, sub_zero]
  have hBx : (J₀ ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection) x = 0 := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, hP0, hP1,
      map_neg, h, neg_add_cancel]
  have hx0 : x = 0 := hinj (hBx.trans (map_zero _).symm)
  have hz : z = 0 := by rw [← hP1, hx0, map_zero]
  refine ⟨hz, ?_⟩
  have := hP0
  rw [hx0, map_zero] at this
  exact neg_eq_zero.1 this.symm

end Chart

/-! ### Lemma 7.5, Sobolev bootstrap -/

/-- **Lemma 7.5 (Sobolev bootstrap).** Let `Φ` map `H^s` into `H^{s+δ}` for every `s ≥ 0`.
A fixed point `z = Φ z` in `L² = H⁰` lies in `H^{nδ}` for every `n`. (In the paper,
`Φ = -Π_Z C / 4` with `δ = 1/4`, and two steps give `z ∈ H^{1/2}`.) -/
theorem sobolev_bootstrap {δ : ℝ} (hδ : 0 ≤ δ) (Φ : (ℤ → ℂ) → (ℤ → ℂ))
    (hΦ : ∀ s, 0 ≤ s → ∀ f, IsSobolevSeq s f → IsSobolevSeq (s + δ) (Φ f)) (z : ℤ → ℂ)
    (hz : IsSobolevSeq 0 z) (hfix : Φ z = z) : ∀ n : ℕ, IsSobolevSeq (n * δ) z := by
  intro n
  induction n with
  | zero => simpa using hz
  | succ n ih =>
    have := hΦ (n * δ) (by positivity) z ih
    rw [hfix] at this
    convert this using 1
    push_cast
    ring

/-! ### Lemma 7.8 on a closed subspace -/

section Reduced

variable {W Y : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

omit [CompleteSpace W] in
/-- **Lemma 7.8 (reduced lower bound) on the fixed space `Z`.** Let `Z ⊆ W` be a closed
subspace. Let `E ↦ R_E : W → W` and `E ↦ S_E : W → Y` be operator-norm continuous at `E₀`,
with `R_{E₀} = α I + C` (`α > 0`, `C` compact) and `S_{E₀}` injective on `Z`. Then there is
`A₀ > 0` such that for all `E` near `E₀`, `Re ⟨z, R_E z⟩ ≥ -A₀ ‖S_E z‖²` for every `z ∈ Z`.
(The compression `Π_Z R_{E₀}|_Z` is `α I` plus a compact operator on `Z`.) -/
theorem reduced_lower_bound_subspace (Z : Submodule ℂ W) [CompleteSpace Z] (α : ℝ) (hα : 0 < α)
    (C : W →L[ℂ] W) (hC : IsCompactOperator C) (R : ℝ → W →L[ℂ] W) (S : ℝ → W →L[ℂ] Y)
    (E₀ : ℝ) (hR : ContinuousAt R E₀) (hS : ContinuousAt S E₀)
    (hR₀ : R E₀ = (α : ℂ) • ContinuousLinearMap.id ℂ W + C)
    (hinj : ∀ z ∈ Z, S E₀ z = 0 → z = 0) :
    ∃ A₀ > 0, ∀ᶠ E in 𝓝 E₀, ∀ z ∈ Z, -(A₀ * ‖S E z‖ ^ 2) ≤ (⟪z, R E z⟫_ℂ).re := by
  set ι := Z.subtypeL
  set Pz := Z.orthogonalProjection
  set R' : ℝ → Z →L[ℂ] Z := fun E => Pz ∘L R E ∘L ι with hR'
  set S' : ℝ → Z →L[ℂ] Y := fun E => S E ∘L ι with hS'
  have hPzι : Pz ∘L ι = ContinuousLinearMap.id ℂ Z := by
    ext1 z
    exact Submodule.orthogonalProjection_mem_subspace_eq_self z
  have hR'c : ContinuousAt R' E₀ :=
    continuousAt_const.clm_comp (hR.clm_comp continuousAt_const)
  have hS'c : ContinuousAt S' E₀ := hS.clm_comp continuousAt_const
  have hR'0 : R' E₀ = (α : ℂ) • ContinuousLinearMap.id ℂ Z + Pz ∘L C ∘L ι := by
    simp only [hR', hR₀, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.id_comp, hPzι]
  have hC' : IsCompactOperator (Pz ∘L C ∘L ι) :=
    (hC.comp_clm ι).clm_comp Pz
  have hinj' : Function.Injective (S' E₀) := by
    intro z₁ z₂ h12
    have h0 : S E₀ ((z₁ : W) - z₂) = 0 := by
      rw [map_sub, sub_eq_zero]; exact h12
    exact Subtype.ext (sub_eq_zero.1 (hinj _ (Z.sub_mem z₁.2 z₂.2) h0))
  obtain ⟨A₀, hA₀, hev⟩ := reduced_lower_bound α hα (Pz ∘L C ∘L ι) hC' R' S' E₀ hR'c hS'c hR'0 hinj'
  refine ⟨A₀, hA₀, ?_⟩
  filter_upwards [hev] with E hE z hz
  have := hE ⟨z, hz⟩
  have e1 : (⟪(⟨z, hz⟩ : Z), R' E ⟨z, hz⟩⟫_ℂ) = ⟪z, R E z⟫_ℂ := by
    simp [hR', Pz, ι]
  have e2 : S' E ⟨z, hz⟩ = S E z := rfl
  rwa [e1, e2] at this

end Reduced

/-! ### Lemma 7.9, chart reduction -/

section Boundary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (H₀ : Submodule ℂ H) [H₀.HasOrthogonalProjection]
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- **Lemma 7.9 (boundary lower bound with finitely many conditions), chart reduction.**
Data (all on the normalized space `H`, where the paper writes `y = Λ^{-1/2} g`):
* the chart `𝔅_E = Ĵ_E Π₀ + R Π₁` of Lemma 7.3, invertible for `E ∈ U`;
* the normalized periodic form `P̂_E` (self-adjoint) and projected observation `Ŝ_E`, with the
  nullspace identities `P̂_E Ĵ_E = 0`, `Ŝ_E Ĵ_E = 0` of Lemma 6.12;
* the pole structure `P̂_E = -2/(E-E₀) ∑ w_j ⟨w_j, ·⟩ + P̂_reg(E)` of Lemma 6.5 for `E ≠ E₀`,
  with `P̂_reg` and `Ŝ` operator-norm continuous at `E₀`;
* the regular part `R^* P̂_reg(E₀) R = α I + C` with `α > 0`, `C` compact (Lemma 7.4);
* injectivity of `Ŝ_{E₀} R` on `Z = {z : ⟨R^* w_j, z⟩ = 0}` (Lemma 7.5).

Then there are `A₀ > 0` and a neighbourhood `V` of `E₀` such that for every `E ∈ V`, `E ≠ E₀`,
there is a linear map `ℓ_E : H → ℂ^m` with `Re ⟨y, P̂_E y⟩ ≥ -A₀ ‖Ŝ_E y‖²` whenever
`ℓ_E y = 0`. (Here `ℓ_E y = (⟨η_j, z⟩)_j` where `y = Ĵ_E a + R z`.) -/
theorem chart_reduced_boundary_bound {m : ℕ} (J : ℝ → H₀ →L[ℂ] H) (R : H₀ᗮ →L[ℂ] H)
    (E₀ : ℝ) (U : Set ℝ)
    (hunit : ∀ E ∈ U, IsUnit (J E ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection))
    (P Preg : ℝ → H →L[ℂ] H) (S : ℝ → H →L[ℂ] Y) (w : Fin m → H)
    (hsa : ∀ E ∈ U, E ≠ E₀ → IsSelfAdjoint (P E))
    (hnullP : ∀ E ∈ U, E ≠ E₀ → P E ∘L J E = 0) (hnullS : ∀ E ∈ U, S E ∘L J E = 0)
    (hpole : ∀ E ∈ U, E ≠ E₀ →
      P E = ((-2 / (E - E₀) : ℝ) : ℂ) • ∑ j, rankOne ℂ (w j) (w j) + Preg E)
    (hPreg : ContinuousAt Preg E₀) (hS : ContinuousAt S E₀)
    (α : ℝ) (hα : 0 < α) (C : H₀ᗮ →L[ℂ] H₀ᗮ) (hC : IsCompactOperator C)
    (hreg : adjoint R ∘L Preg E₀ ∘L R = (α : ℂ) • ContinuousLinearMap.id ℂ H₀ᗮ + C)
    (hinj : ∀ z : H₀ᗮ, (∀ j, ⟪adjoint R (w j), z⟫_ℂ = 0) → S E₀ (R z) = 0 → z = 0) :
    ∃ A₀ > 0, ∃ V ∈ 𝓝 E₀, ∀ E ∈ V, E ∈ U → E ≠ E₀ →
      ∃ ℓ : H →ₗ[ℂ] (Fin m → ℂ), ∀ y, ℓ y = 0 →
        -(A₀ * ‖S E y‖ ^ 2) ≤ (⟪y, P E y⟫_ℂ).re := by
  set η : Fin m → H₀ᗮ := fun j => adjoint R (w j) with hη
  set Z : Submodule ℂ H₀ᗮ := (Submodule.span ℂ (Set.range η))ᗮ with hZ
  have hmemZ : ∀ z, z ∈ Z ↔ ∀ j, ⟪η j, z⟫_ℂ = 0 := by
    intro z
    constructor
    · intro hz j
      exact (Submodule.mem_orthogonal _ _).1 hz _ (Submodule.subset_span ⟨j, rfl⟩)
    · intro h
      rw [Submodule.mem_orthogonal]
      intro u hu
      induction hu using Submodule.span_induction with
      | mem x hx => obtain ⟨j, rfl⟩ := hx; exact h j
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
  obtain ⟨A₀, hA₀, hev⟩ := reduced_lower_bound_subspace Z α hα C hC
    (fun E => adjoint R ∘L Preg E ∘L R) (fun E => S E ∘L R) E₀
    (continuousAt_const.clm_comp (hPreg.clm_comp continuousAt_const))
    (hS.clm_comp continuousAt_const) hreg (fun z hz h0 => hinj z ((hmemZ z).1 hz) h0)
  refine ⟨A₀, hA₀, _, hev, ?_⟩
  intro E hE hEU hne
  obtain ⟨u, hu⟩ := hunit E hEU
  set zc : H →L[ℂ] H₀ᗮ := H₀ᗮ.orthogonalProjection ∘L (↑u⁻¹ : H →L[ℂ] H) with hzc
  refine ⟨LinearMap.pi fun j => (((innerSL ℂ (η j)) ∘L zc : H →L[ℂ] ℂ) : H →ₗ[ℂ] ℂ), ?_⟩
  intro y hy
  set x := (↑u⁻¹ : H →L[ℂ] H) y with hx
  set a := H₀.orthogonalProjection x with ha
  set z := H₀ᗮ.orthogonalProjection x with hz
  have hzj : ∀ j, ⟪η j, z⟫_ℂ = 0 := by
    intro j
    exact congrFun hy j
  have hyx : y = J E a + R z := by
    have h1 : (u : H →L[ℂ] H) x = y := by
      rw [hx, ← ContinuousLinearMap.mul_apply, Units.mul_inv, ContinuousLinearMap.one_apply]
    rw [← h1, hu]
    rfl
  have hSy : S E y = S E (R z) := by
    have := congrArg (fun T => T a) (hnullS E hEU)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at this
    rw [hyx, map_add, this, zero_add]
  have hPJa : P E (J E a) = 0 := by
    have := congrArg (fun T => T a) (hnullP E hEU hne)
    simpa using this
  have hPy : ⟪y, P E y⟫_ℂ = ⟪R z, P E (R z)⟫_ℂ := by
    rw [hyx, map_add, hPJa, zero_add, inner_add_left]
    have : ⟪J E a, P E (R z)⟫_ℂ = 0 := by
      rw [← (hsa E hEU hne).adjoint_eq, adjoint_inner_right, hPJa, inner_zero_left]
    rw [this, zero_add]
  have hwR : ∀ j, ⟪w j, R z⟫_ℂ = 0 := by
    intro j
    rw [← adjoint_inner_left]
    exact hzj j
  have hpz : ⟪R z, P E (R z)⟫_ℂ = ⟪z, (adjoint R ∘L Preg E ∘L R) z⟫_ℂ := by
    rw [hpole E hEU hne, inner_pole_add_eq_of_orthogonal w _ _ _ hwR,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, adjoint_inner_right]
  have hb := hE z ((hmemZ z).2 hzj)
  rw [hPy, hpz, hSy]
  exact hb

/-- **Lemma 7.9 (boundary lower bound with finitely many conditions)**, abstract form. In the
setting of `chart_reduced_boundary_bound`, let `𝒜_E` be a form with
`Re ⟨y, 𝒜_E y⟩ = Re ⟨y, P̂_E y⟩ - Re ⟨x, B_E x⟩` for `x = O_E^* y`, where `‖B_E‖ ≤ b`, and
suppose the projected observation factors as `Ŝ_E = Π_E O_E^*` with `‖Π_E‖ ≤ 1`. Then there are
`A₁` and a neighbourhood `V` of `E₀` such that for every `E ∈ V ∩ U`, `E ≠ E₀`, there is a
linear map `ℓ_E : H → ℂ^m` with `Re ⟨y, 𝒜_E y⟩ ≥ -A₁ ‖O_E^* y‖²` whenever `ℓ_E y = 0`. -/
theorem chart_boundary_lower_bound {m : ℕ} {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] (J : ℝ → H₀ →L[ℂ] H) (R : H₀ᗮ →L[ℂ] H)
    (E₀ : ℝ) (U : Set ℝ)
    (hunit : ∀ E ∈ U, IsUnit (J E ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection))
    (P Preg : ℝ → H →L[ℂ] H) (S : ℝ → H →L[ℂ] Y) (w : Fin m → H)
    (hsa : ∀ E ∈ U, E ≠ E₀ → IsSelfAdjoint (P E))
    (hnullP : ∀ E ∈ U, E ≠ E₀ → P E ∘L J E = 0) (hnullS : ∀ E ∈ U, S E ∘L J E = 0)
    (hpole : ∀ E ∈ U, E ≠ E₀ →
      P E = ((-2 / (E - E₀) : ℝ) : ℂ) • ∑ j, rankOne ℂ (w j) (w j) + Preg E)
    (hPreg : ContinuousAt Preg E₀) (hS : ContinuousAt S E₀)
    (α : ℝ) (hα : 0 < α) (C : H₀ᗮ →L[ℂ] H₀ᗮ) (hC : IsCompactOperator C)
    (hreg : adjoint R ∘L Preg E₀ ∘L R = (α : ℂ) • ContinuousLinearMap.id ℂ H₀ᗮ + C)
    (hinj : ∀ z : H₀ᗮ, (∀ j, ⟪adjoint R (w j), z⟫_ℂ = 0) → S E₀ (R z) = 0 → z = 0)
    (Aop : ℝ → H →L[ℂ] H) (Oadj : ℝ → H →L[ℂ] X) (B : ℝ → X →L[ℂ] X)
    (Pi : ℝ → X →L[ℂ] Y) (b : ℝ)
    (hA : ∀ E ∈ U, E ≠ E₀ → ∀ y, (⟪y, Aop E y⟫_ℂ).re =
      (⟪y, P E y⟫_ℂ).re - (⟪Oadj E y, B E (Oadj E y)⟫_ℂ).re)
    (hB : ∀ E ∈ U, ‖B E‖ ≤ b) (hPi : ∀ E ∈ U, ‖Pi E‖ ≤ 1)
    (hSO : ∀ E ∈ U, S E = Pi E ∘L Oadj E) :
    ∃ A₁, ∃ V ∈ 𝓝 E₀, ∀ E ∈ V, E ∈ U → E ≠ E₀ →
      ∃ ℓ : H →ₗ[ℂ] (Fin m → ℂ), ∀ y, ℓ y = 0 →
        -(A₁ * ‖Oadj E y‖ ^ 2) ≤ (⟪y, Aop E y⟫_ℂ).re := by
  obtain ⟨A₀, hA₀, V, hV, h⟩ := chart_reduced_boundary_bound H₀ J R E₀ U hunit P Preg S w hsa
    hnullP hnullS hpole hPreg hS α hα C hC hreg hinj
  refine ⟨A₀ + b, V, hV, fun E hE hEU hne => ?_⟩
  obtain ⟨ℓ, hℓ⟩ := h E hE hEU hne
  refine ⟨ℓ, fun y hy => ?_⟩
  have h1 := hℓ y hy
  have h2 : ‖S E y‖ ≤ ‖Oadj E y‖ := by
    rw [hSO E hEU, ContinuousLinearMap.comp_apply]
    calc ‖Pi E (Oadj E y)‖ ≤ ‖Pi E‖ * ‖Oadj E y‖ := (Pi E).le_opNorm _
      _ ≤ 1 * ‖Oadj E y‖ := by gcongr; exact hPi E hEU
      _ = ‖Oadj E y‖ := one_mul _
  have h3 : ‖S E y‖ ^ 2 ≤ ‖Oadj E y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h4 : (⟪Oadj E y, B E (Oadj E y)⟫_ℂ).re ≤ b * ‖Oadj E y‖ ^ 2 := by
    calc (⟪Oadj E y, B E (Oadj E y)⟫_ℂ).re ≤ ‖⟪Oadj E y, B E (Oadj E y)⟫_ℂ‖ :=
          Complex.re_le_norm _
      _ ≤ ‖Oadj E y‖ * ‖B E (Oadj E y)‖ := norm_inner_le_norm _ _
      _ ≤ ‖Oadj E y‖ * (‖B E‖ * ‖Oadj E y‖) := by gcongr; exact (B E).le_opNorm _
      _ ≤ ‖Oadj E y‖ * (b * ‖Oadj E y‖) := by gcongr; exact hB E hEU
      _ = b * ‖Oadj E y‖ ^ 2 := by ring
  rw [hA E hEU hne]
  nlinarith [mul_le_mul_of_nonneg_left h3 hA₀.le]

end Boundary

end PolyaNeumann
