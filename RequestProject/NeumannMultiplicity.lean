module

public import RequestProject.NeumannEigenspace
public import RequestProject.WeakCompact
public import RequestProject.Spectrum

/-!
# Discreteness of the Neumann spectrum and multiplicities

For a bounded Lipschitz domain `Ω`:

* `finite_setOf_neumannEigenvalue_lt`: for every finite `E`, only finitely many min–max values
  `μ_j(Ω)` lie below `E` (Lemmas 3.3 and 3.4: `μ_j → ∞`, `N_N(E) < ∞`). A sequence of
  orthonormal functions of bounded Rayleigh quotient would be bounded in `H¹(Ω)`, contradicting
  Rellich compactness.
* `finrank_neumannEigenspace_le`: the dimension of the eigenspace `ker(A_N − E)` is at most the
  number of indices `j` with `μ_j(Ω) = E`. The span of a min–max subspace for the eigenvalues
  below `E` and of the eigenspace has Rayleigh quotient at most `E`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace PolyaNeumann

/-- Given subspaces `S n` of dimension `n + 1`, there is an orthonormal sequence with
`u n ∈ S n`. -/
lemma exists_orthonormal_seq_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S : ℕ → Submodule ℂ H) (hS : ∀ n, Module.finrank ℂ (S n) = n + 1) :
    ∃ u : ℕ → H, Orthonormal ℂ u ∧ ∀ n, u n ∈ S n := by
  have pick : ∀ n (v : Fin n → H), ∃ u ∈ S n, ‖u‖ = 1 ∧ ∀ i, ⟪v i, u⟫_ℂ = 0 := by
    intro n v
    let f : S n →ₗ[ℂ] (Fin n → ℂ) :=
      { toFun := fun u i => ⟪v i, (u : H)⟫_ℂ
        map_add' := fun x y => by
          ext i
          exact inner_add_right _ _ _
        map_smul' := fun c x => by
          ext i
          exact inner_smul_right _ _ _ }
    haveI : FiniteDimensional ℂ (S n) := Module.finite_of_finrank_pos (by rw [hS]; omega)
    have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp [hS n])
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hw0' : (w : H) ≠ 0 := fun h => hw0 (Subtype.ext h)
    refine ⟨(‖(w : H)‖⁻¹ : ℂ) • (w : H), (S n).smul_mem _ w.2, ?_, fun i => ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0')]
    · have := congrFun (LinearMap.mem_ker.mp hw) i
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
      rw [inner_smul_right, this, mul_zero]
  choose p hpS hp1 hpo using pick
  let T : (n : ℕ) → Fin n → H := fun n =>
    Nat.rec (motive := fun n => Fin n → H) Fin.elim0 (fun n t => Fin.snoc t (p n t)) n
  have hT : ∀ n, T (n + 1) = Fin.snoc (T n) (p n (T n)) := fun n => rfl
  let u : ℕ → H := fun n => p n (T n)
  have hTu : ∀ n (i : Fin n), T n i = u i := by
    intro n
    induction n with
    | zero => intro i; exact i.elim0
    | succ n ih =>
      intro i
      rw [hT]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [u]
      · simp [ih j]
  refine ⟨u, ⟨fun n => hp1 n _, fun i j hij => ?_⟩, fun n => hpS n _⟩
  rcases lt_or_gt_of_ne hij with h | h
  · have := hpo j (T j) ⟨i, h⟩
    rwa [hTu] at this
  · have := hpo i (T i) ⟨j, h⟩
    rw [hTu] at this
    rw [← inner_conj_symm, this, map_zero]

/-- A unit vector of Rayleigh quotient below a finite level `E` has a weak gradient with
`‖gᵢ‖² ≤ E`. -/
lemma exists_grad_of_rayleigh_lt {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : L2 Ω} (hu : ‖u‖ = 1)
    {E : ENNReal} (hE : E ≠ ⊤) (h : rayleigh Ω u < E) :
    ∃ g, IsWeakGradient Ω u g ∧ ∀ i, ‖g i‖ ≤ Real.sqrt E.toReal := by
  have hn : (‖u‖₊ : ENNReal) = 1 := by
    rw [← ENNReal.coe_one]; congr 1; exact Subtype.ext hu
  unfold rayleigh at h
  rw [hn, one_pow, div_one] at h
  have hne : neumannEnergy Ω u ≠ ⊤ := (h.trans_le le_top).ne
  have hH : ∃ g, IsWeakGradient Ω u g := by
    by_contra hno
    push_neg at hno
    apply hne
    unfold neumannEnergy
    exact iInf₂_eq_top.mpr fun g hg => absurd hg (hno g)
  obtain ⟨g, hg⟩ := hH
  refine ⟨g, hg, fun i => ?_⟩
  rw [neumannEnergy_eq_of_isWeakGradient hΩ hg] at h
  have hi : (‖g i‖₊ : ENNReal) ^ 2 ≤ E :=
    (Finset.single_le_sum (f := fun j => (‖g j‖₊ : ENNReal) ^ 2) (fun _ _ => zero_le)
      (Finset.mem_univ i)).trans h.le
  have hi' : ‖g i‖ ^ 2 ≤ E.toReal := by
    have := ENNReal.toReal_mono hE hi
    simpa [ENNReal.toReal_pow] using this
  exact Real.le_sqrt_of_sq_le hi'

/-- **Discreteness of the Neumann spectrum.** On a bounded Lipschitz domain only finitely many
min–max values lie below any finite level. -/
theorem finite_setOf_neumannEigenvalue_lt {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ENNReal} (hE : E ≠ ⊤) :
    {j : ℕ | neumannEigenvalue Ω j < E}.Finite := by
  by_contra hinf
  have hall : ∀ j, neumannEigenvalue Ω j < E := by
    intro j
    obtain ⟨i, hi, hji⟩ := Set.Infinite.exists_gt hinf j
    exact (neumannEigenvalue_monotone Ω hji.le).trans_lt hi
  have hS : ∀ n, ∃ S : Submodule ℂ (L2 Ω), Module.finrank ℂ S = n + 1 ∧
      ∀ u ∈ S, u ≠ 0 → rayleigh Ω u < E := by
    intro n
    have h := hall n
    unfold neumannEigenvalue at h
    obtain ⟨S, h1⟩ := iInf_lt_iff.mp h
    obtain ⟨hS, h2⟩ := iInf_lt_iff.mp h1
    refine ⟨S, hS, fun u hu hu0 => lt_of_le_of_lt ?_ h2⟩
    exact le_iSup₂_of_le u hu (le_iSup (fun _ : u ≠ 0 => rayleigh Ω u) hu0)
  choose S hSd hSr using hS
  obtain ⟨u, hu, huS⟩ := exists_orthonormal_seq_mem S hSd
  have hgrad : ∀ n, ∃ g, IsWeakGradient Ω (u n) g ∧ ∀ i, ‖g i‖ ≤ Real.sqrt E.toReal :=
    fun n => exists_grad_of_rayleigh_lt hL.1.1 (hu.1 n) hE
      (hSr n _ (huS n) (hu.ne_zero n))
  choose g hg hgb using hgrad
  obtain ⟨φ, hφ, v, hv⟩ := rellich_compact hb hL u g hg (max 1 (Real.sqrt E.toReal))
    (fun n => (hu.1 n).le.trans (le_max_left _ _)) (fun n i => (hgb n i).trans (le_max_right _ _))
  have hcauchy := hv.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy 1 one_pos
  have h1 := hN (N + 1) (by omega) N le_rfl
  rw [dist_eq_norm] at h1
  simp only [Function.comp] at h1
  have hne : φ (N + 1) ≠ φ N := hφ.injective.ne (by omega)
  have h2 : ‖u (φ (N + 1)) - u (φ N)‖ ^ 2 = 2 := by
    rw [@norm_sub_sq ℂ, hu.1, hu.1, hu.2 hne]; simp; norm_num
  nlinarith [norm_nonneg (u (φ (N + 1)) - u (φ N))]

/-- The Rayleigh quotient of a nonzero `u` with weak gradient `g` is `∑ ‖gᵢ‖² / ‖u‖²`. -/
lemma rayleigh_eq_ofReal {Ω : Set ℂ} (hΩ : IsOpen Ω) {u : L2 Ω} (hu : u ≠ 0)
    {g : Fin 2 → L2 Ω} (hg : IsWeakGradient Ω u g) :
    rayleigh Ω u = ENNReal.ofReal ((∑ i, ‖g i‖ ^ 2) / ‖u‖ ^ 2) := by
  have hsq : ∀ x : L2 Ω, (‖x‖₊ : ENNReal) ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := fun x => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
  unfold rayleigh
  rw [neumannEnergy_eq_of_isWeakGradient hΩ hg, hsq u, ENNReal.ofReal_div_of_pos
    (by positivity), ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  simp only [hsq]

/-- **Multiplicity.** On a bounded Lipschitz domain, the dimension of the Neumann eigenspace at
`E ≥ 0` is at most the number of indices `j` with `μ_j(Ω) = E`. -/
theorem finrank_neumannEigenspace_le {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {E : ℝ} (hE : 0 ≤ E) :
    (Module.finrank ℂ (neumannEigenspace Ω E) : ℕ∞) ≤
      {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E}.encard := by
  classical
  have hΩ : IsOpen Ω := hL.1.1
  set Eig := neumannEigenspace Ω E with hEig
  haveI : FiniteDimensional ℂ Eig := finiteDimensional_neumannEigenspace hb hL E
  set d := Module.finrank ℂ Eig with hd
  set T := {j : ℕ | neumannEigenvalue Ω j < ENNReal.ofReal E} with hTdef
  have hT : T.Finite := finite_setOf_neumannEigenvalue_lt hb hL ENNReal.ofReal_ne_top
  have hex : ∃ j, j ∉ T := hT.exists_notMem
  set n₀ := Nat.find hex with hn₀
  have hlt : ∀ j < n₀, j ∈ T := fun j hj => by
    have := Nat.find_min hex hj
    simpa using this
  have hge : ∀ j, n₀ ≤ j → ENNReal.ofReal E ≤ neumannEigenvalue Ω j := fun j hj => by
    have h0 : n₀ ∉ T := Nat.find_spec hex
    simp only [hTdef, Set.mem_setOf_eq, not_lt] at h0
    exact h0.trans (neumannEigenvalue_monotone Ω hj)
  -- eigenfunctions: energy identity
  have heig : ∀ w ∈ Eig, ∃ g, IsWeakGradient Ω w g ∧ ∀ v h, IsWeakGradient Ω v h →
      ∑ i, ⟪h i, g i⟫_ℂ = (E : ℂ) * ⟪v, w⟫_ℂ := fun w hw => hw
  have heig_norm : ∀ w g, IsWeakGradient Ω w g → (∀ v h, IsWeakGradient Ω v h →
      ∑ i, ⟪h i, g i⟫_ℂ = (E : ℂ) * ⟪v, w⟫_ℂ) → ∑ i, ‖g i‖ ^ 2 = E * ‖w‖ ^ 2 := by
    intro w g hg hw
    have h := hw w g hg
    simp only [inner_self_eq_norm_sq_to_K] at h
    exact Complex.ofReal_injective (by push_cast; exact h)
  -- a min–max subspace below `E`
  have hS₁ : ∃ S₁ : Submodule ℂ (L2 Ω), FiniteDimensional ℂ S₁ ∧ Module.finrank ℂ S₁ = n₀ ∧
      ∀ v ∈ S₁, v ≠ 0 → rayleigh Ω v < ENNReal.ofReal E := by
    rcases Nat.eq_zero_or_pos n₀ with h0 | hpos
    · exact ⟨⊥, inferInstance, by rw [h0]; simp,
        fun v hv hv0 => absurd ((Submodule.mem_bot ℂ).mp hv) hv0⟩
    · have h := hlt (n₀ - 1) (by omega)
      simp only [hTdef, Set.mem_setOf_eq] at h
      unfold neumannEigenvalue at h
      obtain ⟨S, h1⟩ := iInf_lt_iff.mp h
      obtain ⟨hS, h2⟩ := iInf_lt_iff.mp h1
      refine ⟨S, Module.finite_of_finrank_pos (by omega), by rw [hS]; omega,
        fun u hu hu0 => lt_of_le_of_lt ?_ h2⟩
      exact le_iSup₂_of_le u hu (le_iSup (fun _ : u ≠ 0 => rayleigh Ω u) hu0)
  obtain ⟨S₁, hS₁f, hS₁d, hS₁r⟩ := hS₁
  -- gradients on `S₁`
  have hgradS : ∀ v ∈ S₁, ∃ h, IsWeakGradient Ω v h ∧ ∑ i, ‖h i‖ ^ 2 ≤ E * ‖v‖ ^ 2 ∧
      (v ≠ 0 → ∑ i, ‖h i‖ ^ 2 < E * ‖v‖ ^ 2) := by
    intro v hv
    by_cases hv0 : v = 0
    · subst hv0
      exact ⟨0, isWeakGradient_zero, by simp, fun h => absurd rfl h⟩
    have hr := hS₁r v hv hv0
    have hne : neumannEnergy Ω v ≠ ⊤ := by
      intro htop
      unfold rayleigh at hr
      rw [htop, ENNReal.top_div_of_ne_top (by simp)] at hr
      exact absurd hr (not_lt.mpr le_top)
    have hH : ∃ h, IsWeakGradient Ω v h := by
      by_contra hno
      push_neg at hno
      apply hne
      unfold neumannEnergy
      exact iInf₂_eq_top.mpr fun g hg => absurd hg (hno g)
    obtain ⟨h, hh⟩ := hH
    rw [rayleigh_eq_ofReal hΩ hv0 hh, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity),
      div_lt_iff₀ (by positivity [norm_pos_iff.mpr hv0])] at hr
    exact ⟨h, hh, hr.le, fun _ => hr⟩
  -- the energy on `S₁ + Eig`
  have hsum : ∀ v ∈ S₁, ∀ w ∈ Eig, v + w ≠ 0 → rayleigh Ω (v + w) ≤ ENNReal.ofReal E := by
    intro v hv w hw hvw
    obtain ⟨h, hh, hhE, -⟩ := hgradS v hv
    obtain ⟨g, hg, hgE⟩ := heig w hw
    have hgn := heig_norm w g hg hgE
    have hcross := hgE v h hh
    rw [rayleigh_eq_ofReal hΩ hvw (hh.add hg), ENNReal.ofReal_le_ofReal_iff hE,
      div_le_iff₀ (by positivity [norm_pos_iff.mpr hvw])]
    have hexp : ∀ i, ‖h i + g i‖ ^ 2 = ‖h i‖ ^ 2 + 2 * (⟪h i, g i⟫_ℂ).re + ‖g i‖ ^ 2 :=
      fun i => @norm_add_sq ℂ _ _ _ _ _ _
    have hvw2 : ‖v + w‖ ^ 2 = ‖v‖ ^ 2 + 2 * (⟪v, w⟫_ℂ).re + ‖w‖ ^ 2 := @norm_add_sq ℂ _ _ _ _ _ _
    have hre : ∑ i, (⟪h i, g i⟫_ℂ).re = E * (⟪v, w⟫_ℂ).re := by
      have := congrArg Complex.re hcross
      rw [Complex.re_sum] at this
      rw [this]; simp
    simp only [Pi.add_apply, hexp, Finset.sum_add_distrib, ← Finset.mul_sum, hre, hgn, hvw2]
    nlinarith
  -- `S₁` and `Eig` are independent
  have hdisj : S₁ ⊓ Eig = ⊥ := by
    rw [eq_bot_iff]
    intro v ⟨hv1, hv2⟩
    rw [Submodule.mem_bot]
    by_contra hv0
    obtain ⟨h, hh, -, hlt'⟩ := hgradS v hv1
    obtain ⟨g, hg, hgE⟩ := heig v hv2
    have := heig_norm v g hg hgE
    rw [hh.unique hΩ hg] at hlt'
    linarith [hlt' hv0]
  set S := S₁ ⊔ Eig with hSdef
  have hSd : Module.finrank ℂ S = n₀ + d := by
    have := Submodule.finrank_sup_add_finrank_inf_eq S₁ Eig
    rw [hdisj, finrank_bot, add_zero, hS₁d] at this
    exact this
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · rw [hd0]; simp
  -- `μ_{n₀ + d - 1} ≤ E`
  have htop : neumannEigenvalue Ω (n₀ + d - 1) ≤ ENNReal.ofReal E := by
    unfold neumannEigenvalue
    refine (iInf₂_le S (by rw [hSd]; omega)).trans ?_
    refine iSup₂_le fun u hu => iSup_le fun hu0 => ?_
    obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hu
    exact hsum v hv w hw hu0
  have heq : ∀ i < d, neumannEigenvalue Ω (n₀ + i) = ENNReal.ofReal E := fun i hi =>
    le_antisymm ((neumannEigenvalue_monotone Ω (by omega)).trans htop) (hge _ (by omega))
  have hsub : ((Finset.range d).image (n₀ + ·) : Set ℕ) ⊆
      {j : ℕ | neumannEigenvalue Ω j = ENNReal.ofReal E} := by
    intro j hj
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    exact heq i hi
  have := Set.encard_le_encard hsub
  rw [Set.encard_coe_eq_coe_finsetCard,
    Finset.card_image_of_injective _ (add_right_injective n₀), Finset.card_range] at this
  exact this
end PolyaNeumann

end
