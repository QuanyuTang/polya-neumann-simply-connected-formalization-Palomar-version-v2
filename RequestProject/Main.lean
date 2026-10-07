module

public import RequestProject.Poincare
public import RequestProject.Finite
public import RequestProject.Transport
public import RequestProject.Unitarity
public import RequestProject.CurveContinuity
public import RequestProject.AreaTrace
public import RequestProject.Driven
public import RequestProject.CayleyFactorization
public import RequestProject.Phase
public import RequestProject.Transmutation
public import RequestProject.CutCorrection
public import RequestProject.Reparam
public import RequestProject.BoundaryOrigin
public import RequestProject.PeriodicForm
public import RequestProject.Coercivity
public import RequestProject.NegativeIndex
public import RequestProject.FiniteRankCompletion
public import RequestProject.RankBound
public import RequestProject.Approximation
public import RequestProject.ArcLength
public import RequestProject.NeumannEigenspace
public import RequestProject.MonodromyCompact
public import RequestProject.PhaseCount
public import RequestProject.PhaseInduction
public import RequestProject.TraceBound
public import RequestProject.SmallEnergy
public import RequestProject.CutTrace
public import RequestProject.ExteriorConnected
public import RequestProject.Pullback
public import RequestProject.FixedSpace
public import RequestProject.HerglotzForm
public import RequestProject.BoundaryConnected
public import RequestProject.BallZarnescu
public import RequestProject.Reconstruction
public import RequestProject.SmallEnergyCore
public import RequestProject.NeumannMultiplicity
public import RequestProject.OriginalSmoothCayleyBound

/-!
# The strict Neumann Pólya inequality on simply connected planar domains

Main results of the paper:

* `PolyaNeumann.strict_neumann_polya` (Theorem 10.16): for every bounded simply connected
  Lipschitz domain `Ω ⊂ ℝ²` and every `j ≥ 1`, `|Ω| μ_j(Ω) < 4π j`;
* `PolyaNeumann.strict_neumann_polya_count`: for every `E > 0`, `N_N(E) > |Ω| E / (4π)`.

The proof is assembled, exactly as in the paper, from
* Lemma 3.3 (discreteness of the Neumann spectrum),
* the quantitative Lipschitz inequality (Theorem 10.15)
  `|Ω| μ_j + 2 ‖U_{μ_j} - I‖ ≤ 4π j`,
* Lemma 10.5 (`U_E ≠ I` for `E > 0`),
* Lemma 3.5 (equivalence of the eigenvalue and counting forms).
-/

@[expose] public section

open scoped Real ComplexConjugate
open MeasureTheory Filter Topology

noncomputable section

namespace PolyaNeumann

/-! ### Lemma 3.3: the discrete Neumann spectrum -/

/-- Lemma 3.3: the Neumann eigenvalues of a Lipschitz domain are finite. -/
theorem neumannEigenvalue_lt_top {Ω : Set ℂ} (hL : IsLipschitzDomain Ω) (j : ℕ) :
    neumannEigenvalue Ω j < ⊤ :=
  neumannEigenvalue_lt_top_of_isOpen hL.1.1 hL.1.2.nonempty j

/-- Lemma 3.5: for a bounded Lipschitz domain, the eigenvalue form and the counting form
of the strict Pólya inequality are equivalent. -/
theorem eigen_iff_count {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) :
    (∀ j : ℕ, 1 ≤ j → volume Ω * neumannEigenvalue Ω j < ENNReal.ofReal (4 * π * j)) ↔
    (∀ E : ℝ, 0 < E → volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) <
      (neumannCount Ω (ENNReal.ofReal E) : ENNReal)) := by
  constructor
  · intro h E hE
    exact count_of_eigen _ _ hb.measure_lt_top.ne (neumannEigenvalue_monotone Ω)
      (neumannEigenvalue_zero Ω hL.1.1 hL.1.2.nonempty hb) h E hE
  · intro h j hj
    exact eigen_of_count _ _ (neumannEigenvalue_monotone Ω)
      (neumannEigenvalue_pos hb hL) (fun j _ => (neumannEigenvalue_lt_top hL j).ne) h j hj

/-! ### Boundary parametrization and transport (Section 10) -/

/-- External theorem E3 (planar Lipschitz boundaries), in the form used here: the boundary of a
bounded simply connected Lipschitz domain is a single Lipschitz Jordan curve. That is, `∂Ω` has
a Lipschitz `2π`-periodic parametrization `γ` that is injective on `[0, 2π)` and has image
`∂Ω`.
Proved from `isPreconnected_frontier_of_simplyConnected` (the boundary is connected,
`BoundaryConnected.lean`) and `exists_jordanParam_of_isPreconnected_frontier` (a connected
Lipschitz boundary is a single Lipschitz Jordan curve, obtained by walking along the boundary
through uniform Lipschitz charts, `BoundaryChart.lean`, `BoundaryWalk.lean`, `BoundaryLoop.lean`). -/
theorem exists_lipschitzJordanParam_topological {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) :
    ∃ γ : ℝ → ℂ, (∃ K, LipschitzWith K γ) ∧ Function.Periodic γ (2 * π) ∧
      Set.InjOn γ (Set.Ico 0 (2 * π)) ∧ γ '' Set.Icc 0 (2 * π) = frontier Ω :=
  exists_jordanParam_of_isPreconnected_frontier hb hL
    (isPreconnected_frontier_of_simplyConnected hb hL hsc)

/-- External theorem E3, exterior part: the exterior `ℂ \ Ω̄` of a bounded simply connected
Lipschitz domain is connected. Proved from `exists_lipschitzJordanParam_topological` (the
boundary is a continuous image of an interval, hence connected) and
`isConnected_compl_closure_of_frontier`. -/
theorem isConnected_compl_closure {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) :
    IsConnected (closure Ω)ᶜ := by
  obtain ⟨γ, ⟨K, hK⟩, -, -, him⟩ := exists_lipschitzJordanParam_topological hb hL hsc
  refine isConnected_compl_closure_of_frontier hb hL ?_
  rw [← him]
  exact isPreconnected_Icc.image γ hK.continuous.continuousOn

/-- External theorem E3 with the winding-number form of Jordan separation: the boundary of a
bounded simply connected Lipschitz domain has a Lipschitz `2π`-periodic parametrization `γ`,
injective on `[0, 2π)` with image `∂Ω`, whose winding number is a constant `σ = ±1` on `Ω` (the
orientation) and vanishes off `Ω̄`.
Proved from `exists_lipschitzJordanParam_topological`, `isConnected_compl_closure` and
`windingNumber_pm_one_of_jordan`: winding numbers of closed Lipschitz curves are integers,
continuous off the curve and zero far away (`WindingNumber.lean`), hence constant on the
connected sets `Ω` and `ℂ \ Ω̄`; the jump of the winding number across the boundary at a
Lipschitz chart point is `±1` (`windingNumber_jump`). -/
theorem exists_lipschitzJordanParam_winding {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) :
    ∃ γ : ℝ → ℂ, (∃ K, LipschitzWith K γ) ∧ Function.Periodic γ (2 * π) ∧
      Set.InjOn γ (Set.Ico 0 (2 * π)) ∧ γ '' Set.Icc 0 (2 * π) = frontier Ω ∧
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ (∀ z ∈ Ω, windingNumber γ z = σ) ∧
        ∀ z, z ∉ closure Ω → windingNumber γ z = 0 := by
  obtain ⟨γ, ⟨K, hK⟩, hper, hinj, him⟩ := exists_lipschitzJordanParam_topological hb hL hsc
  exact ⟨γ, ⟨K, hK⟩, hper, hinj, him, windingNumber_pm_one_of_jordan hb hL hK hper hinj him
    (isConnected_compl_closure hb hL hsc)⟩

/-- External theorem E3 (planar Lipschitz boundaries) with Green's formula: the boundary of a
bounded simply connected Lipschitz domain is a single Lipschitz Jordan curve. It has a Lipschitz
`2π`-periodic parametrization that is injective on `[0, 2π)`, and by Green's formula the
signed-area integral `∫₀^{2π} Im(conj γ · γ')` of this parametrization is `±2|Ω|` (the sign
depending on the orientation).
Proved from the topological statement `exists_lipschitzJordanParam_winding` and Green's formula
in its winding-number form (`integral_signedAreaDensity_of_winding`, `GreenWinding.lean`). -/
theorem exists_lipschitzJordanParam {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) :
    ∃ γ : ℝ → ℂ, (∃ K, LipschitzWith K γ) ∧ Function.Periodic γ (2 * π) ∧
      Set.InjOn γ (Set.Ico 0 (2 * π)) ∧ γ '' Set.Icc 0 (2 * π) = frontier Ω ∧
      |∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity γ θ| = 2 * (volume Ω).toReal := by
  obtain ⟨γ, ⟨K, hK⟩, hper, hinj, him, σ, hσ, hin, hout⟩ :=
    exists_lipschitzJordanParam_winding hb hL hsc
  refine ⟨γ, ⟨K, hK⟩, hper, hinj, him, ?_⟩
  rw [integral_signedAreaDensity_of_winding hL.1.1 hb hK him σ hin hout, abs_mul, abs_mul,
    abs_of_nonneg ENNReal.toReal_nonneg]
  rcases hσ with rfl | rfl <;> norm_num

/-- External theorem E3 and Definition 10.1: a bounded simply connected Lipschitz domain has
a single Lipschitz Jordan boundary curve, which admits a positively oriented
rescaled-arclength parametrization. Proved from the topological statement
`exists_lipschitzJordanParam` by reparametrizing by rescaled arclength and, if necessary,
reversing the orientation. -/
theorem exists_boundaryParam {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) :
    ∃ γ : ℝ → ℂ, IsBoundaryParam Ω γ := by
  obtain ⟨γ, ⟨K, hK⟩, hper, hinj, him, harea⟩ := exists_lipschitzJordanParam hb hL hsc
  obtain ⟨γ1, ⟨K1, hK1⟩, hper1, hinj1, him1, ⟨c, hc, hspeed⟩, harea1, -⟩ :=
    exists_constSpeed_reparam hK hper hinj
  have hv : (0 : ℝ) ≤ 2 * (volume Ω).toReal := by positivity
  rcases (abs_eq hv).mp harea with hpos | hneg
  · exact ⟨γ1, ⟨⟨K1, hK1⟩, hper1, hinj1, him1.trans him, ⟨c, hc, hspeed⟩,
      show ∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity γ1 θ = _ by rw [harea1, hpos]⟩⟩
  · obtain ⟨γ2, hK2, hper2, hinj2, him2, hspeed2, harea2⟩ :=
      exists_reverse_param hK1 hper1 hinj1 hspeed
    exact ⟨γ2, ⟨⟨K1, hK2⟩, hper2, hinj2, him2.trans (him1.trans him), ⟨c, hc, hspeed2⟩,
      show ∫ θ in (0 : ℝ)..(2 * π), signedAreaDensity γ2 θ = _ by
        rw [harea2, harea1, hneg, neg_neg]⟩⟩

/-- Lemma 10.2: the Lipschitz transport of a boundary parametrization exists and is unique
on `[0, L]`. -/
theorem transport_exists_unique {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ) :
    ∃ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W ∧
      ∀ W' : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W' → Set.EqOn W W' (Set.Icc 0 (2 * π)) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
  exact ⟨W, hW, fun W' hW' => transport_unique_of_lipschitz γ hK E hW hW'⟩

/-- Lemma 10.2: the values of the transport are unitary (the coefficient `C_E` is
skew-adjoint). -/
theorem transport_unitary {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ)
    (W : ℝ → Ell2 →L[ℂ] Ell2) (hW : IsTransport γ E W) :
    ∀ θ ∈ Set.Icc 0 (2 * π), W θ ∈ unitary (Ell2 →L[ℂ] Ell2) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  intro θ hθ
  exact Unitary.mem_iff.mpr (volterra_unitary (transportCoeff_aestronglyMeasurable γ E)
    (transportCoeff_norm_le γ E hK) (transportCoeff_star γ E) hW.1 hW.2 θ hθ)

/-- The standard basis vectors of `ℓ²(ℕ₀)` are orthonormal. -/
lemma orthonormal_basisVec : Orthonormal ℂ basisVec := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [basisVec, lp.inner_single_left, lp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- `ℓ²(ℕ₀)` is infinite-dimensional. -/
lemma not_finiteDimensional_ell2 : ¬ FiniteDimensional ℂ Ell2 := by
  intro h
  have := orthonormal_basisVec.linearIndependent.finite
  exact not_finite ℕ

/-- Lemma 4.8 (Cauchy reconstruction) with zero conormal data, together with the uniqueness of
Lemma 4.9 (zero Cauchy data): every compatible trace `h` (Lipschitz and closed on `[0, L]`, with
`∫₀^L conj(g_a) h = 0` for the conormal trace `g_a` of every Herglotz wave) is the Dirichlet
trace `u ∘ γ` of a unique Neumann eigenfunction `u` with eigenvalue `E`; the reconstruction
`h ↦ u` is linear and `u = 0` forces `h = 0` on `[0, L]`.
Proved from `neumann_reconstruction_of_compatible` (`RequestProject/Reconstruction.lean`). Only the
linear map and its triviality on traces are recorded, which is what Lemma 10.5 uses. -/
theorem neumann_reconstruction {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (E : ℝ) (hE : 0 < E) :
    ∃ R : compatibleTraces γ E →ₗ[ℂ] neumannEigenspace Ω E,
      ∀ h, R h = 0 → ∀ θ ∈ Set.Icc 0 (2 * π), (h : ℝ → ℂ) θ = 0 :=
  neumann_reconstruction_of_compatible hb hL hγ hE

/-- Lemma 10.5, first inequality: `dim ker(V_E - I) ≤ dim ker(A_N - E)`, expressed as an
injective linear map from the fixed space of `V_E = W_E(L)` into the Neumann eigenspace.
As in the paper, a fixed vector `v` is sent to the Neumann eigenfunction reconstructed from the
compatible trace `O_E v = ⟨e₀, W_E(·) v⟩`: the pairing step (orthogonality of `O_E v` to the
Herglotz conormal traces, from the driven equation of Lemma 4.4) is proved in `Herglotz.lean` and
`FixedSpace.lean`, the reconstruction is `neumann_reconstruction`, and injectivity follows from
the injectivity of the observation map (Lemma 10.4). -/
theorem fixedSpace_to_neumannEigenspace {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (E : ℝ) (hE : 0 < E) (W : ℝ → Ell2 →L[ℂ] Ell2)
    (hW : IsTransport γ E W) :
    ∃ T : LinearMap.ker ((W (2 * π) - 1 : Ell2 →L[ℂ] Ell2) : Ell2 →ₗ[ℂ] Ell2) →ₗ[ℂ]
      neumannEigenspace Ω E, Function.Injective T :=
  fixedSpace_to_neumannEigenspace_of_reconstruction hγ hE hW
    (neumann_reconstruction hb hL hγ E hE)

/-- Lemma 10.5 with multiplicities: `dim ker(V_E − I) ≤ dim ker(A_N − E) ≤ m`, where `m` is the
number of indices `j` with `μ_j(Ω) = E`. -/
theorem finrank_ker_transport_sub_one_le {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (E : ℝ) (hE : 0 < E) (W : ℝ → Ell2 →L[ℂ] Ell2)
    (hW : IsTransport γ E W) (m : ℕ)
    (hm : {i | neumannEigenvalue Ω i = ENNReal.ofReal E}.encard = m) :
    Module.finrank ℂ
      (LinearMap.ker ((W (2 * π) - 1 : Ell2 →L[ℂ] Ell2) : Ell2 →ₗ[ℂ] Ell2)) ≤ m := by
  obtain ⟨T, hT⟩ := fixedSpace_to_neumannEigenspace hb hL hγ E hE W hW
  haveI := finiteDimensional_neumannEigenspace hb hL E
  have h1 := LinearMap.finrank_le_finrank_of_injective hT
  have h2 := finrank_neumannEigenspace_le hb hL hE.le
  rw [hm] at h2
  exact h1.trans (by exact_mod_cast h2)

/-- Lemma 10.5: for every `E > 0`, `dim ker(V_E - I) ≤ dim ker(A_N - E) < ∞`; in particular
the monodromy satisfies `U_E ≠ I`. The finiteness of `dim ker(A_N - E)` is
`finiteDimensional_neumannEigenspace` (from Rellich compactness); if `U_E = I`, the fixed space
of `V_E` would be all of the infinite-dimensional space `ℓ²(ℕ₀)`. -/
theorem monodromy_ne_one {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (E : ℝ) (hE : 0 < E) (W : ℝ → Ell2 →L[ℂ] Ell2)
    (hW : IsTransport γ E W) : monodromy W ≠ 1 := by
  intro h
  obtain ⟨T, hT⟩ := fixedSpace_to_neumannEigenspace hb hL hγ E hE W hW
  haveI := finiteDimensional_neumannEigenspace hb hL E
  have hV : W (2 * π) = 1 := by
    have h2 := congrArg ContinuousLinearMap.adjoint h
    rw [monodromy, ContinuousLinearMap.adjoint_adjoint] at h2
    rw [h2, ← ContinuousLinearMap.star_eq_adjoint, star_one]
  haveI : FiniteDimensional ℂ
      (LinearMap.ker ((W (2 * π) - 1 : Ell2 →L[ℂ] Ell2) : Ell2 →ₗ[ℂ] Ell2)) :=
    Module.Finite.of_injective T hT
  have htop : LinearMap.ker ((W (2 * π) - 1 : Ell2 →L[ℂ] Ell2) : Ell2 →ₗ[ℂ] Ell2) = ⊤ := by
    rw [hV, sub_self, ContinuousLinearMap.coe_zero]
    exact LinearMap.ker_zero
  rw [htop] at this
  exact not_finiteDimensional_ell2 (LinearEquiv.finiteDimensional Submodule.topEquiv)

/-! ### Smooth domains (Section 9) -/

/-- The real form of the left-hand side of the counting inequality. -/
lemma count_lhs_eq_ofReal {Ω : Set ℂ} (hvol : volume Ω ≠ ⊤) {E : ℝ} (hE : 0 ≤ E)
    (U : Ell2 →L[ℂ] Ell2) :
    volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) +
        ENNReal.ofReal (‖U - 1‖ / (2 * π)) =
      ENNReal.ofReal ((volume Ω).toReal * E / (4 * π) + ‖U - 1‖ / (2 * π)) := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 4 * π),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 * π),
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hvol]

/-- Proposition 7.10 (uniform Cayley bound and resonance rank), read on eigenvectors through
the Cayley correspondence (an eigenvalue `e^{it}` of `U_E`, `0 < t < 2π`, is the eigenvalue
`cot(t/2)` of the Cayley transform `K_E`). Let `E₀ > 0` have Neumann multiplicity `m`: the
number of indices `i` with `μ_i = E₀` (so `m = 0` if `E₀` is nonresonant). Then there are `A`
and `a > 0` such that at every nonresonant energy `E > 0` with `|E - E₀| < a`, every orthonormal
family of eigenvectors of `U_E` with eigenvalues `e^{it}`, `cot(t/2) > A`, has at most `m`
members (`rank 1_{(A,∞)}(K_E) ≤ m`; for `m = 0` this is `K_E ≤ A`).
Proved from the original smooth-domain Herglotz bound and the chosen-origin Cayley transfer
(`uniform_cayley_rank_bound_of_original_smooth_domain`). -/
theorem uniform_cayley_rank_bound {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (E₀ : ℝ) (hE₀ : 0 < E₀) (m : ℕ)
    (hm : {i | neumannEigenvalue Ω i = ENNReal.ofReal E₀}.encard = m) :
    ∃ A a : ℝ, 0 < a ∧ ∀ E, 0 < E → |E - E₀| < a →
      (∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) →
      CayleyRankBound (monodromyAt γ E) A m := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨W₀, hW₀⟩ := transport_exists_of_lipschitz γ hK E₀
  have hU₀ : monodromyAt γ E₀ ≠ 1 := by
    rw [monodromyAt_eq hK hW₀]
    exact monodromy_ne_one hb hS.isLipschitzDomain hγ E₀ hE₀ W₀ hW₀
  exact uniform_cayley_rank_bound_of_original_smooth_domain hb hS hsc hγ E₀ hE₀ m hm hU₀

/-- Lemma 9.3, analytic core (trace of the cut logarithm): for a closed Lipschitz curve, let
`0 < ε < 2π` and let `[E₁, E₂] ⊂ (0, ∞)` be an interval on which `e^{iε}` avoids the spectrum of
`U_E`. Then `tr(-i log_ε U_E) = ∑_{z ≠ 1} mult(z) argCut ε z` increases on `[E₁, E₂]` at the
constant rate `tr L_E = (1/4) ∫₀^{2π} b` of Lemma 4.7, i.e.
`tr(-i log_ε U_{E₂}) - tr(-i log_ε U_{E₁}) = (E₂ - E₁) · (1/4) ∫ b`.
(Proved in `CutTrace.lean` (`cutPhaseSum_monodromyAt_sub'`) without the determinant identities of
External theorem E9: an absolutely convergent Fourier series `argCut ε z = ∑ₙ 2 Re(cₙ (zⁿ - 1))`
valid away from the cut reduces the claim to the traces `tr(U_E^n - I)`, which are differentiated
in `E` through the curvature formula `∂_E U_E = i Q_E U_E`.) -/
theorem cutPhaseSum_monodromyAt_sub {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 2 * π) (E₁ E₂ : ℝ)
    (h1 : 0 < E₁) (h12 : E₁ ≤ E₂)
    (hcut : ∀ E ∈ Set.Icc E₁ E₂,
      Complex.exp (ε * Complex.I) ∉ spectrum ℂ (monodromyAt γ E)) :
    cutPhaseSum ε (monodromyAt γ E₂) - cutPhaseSum ε (monodromyAt γ E₁) =
      (E₂ - E₁) * ((1 / 4) * ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ) :=
  cutPhaseSum_monodromyAt_sub' hK hclosed hε0 hε E₁ E₂ h1 h12 hcut

/-- Lemma 9.3 (continuity of a cut logarithm), for the monodromy of a bounded smooth Jordan
domain: let `0 < ε < 2π` and let `[E₁, E₂] ⊂ (0, ∞)` be an interval on which `e^{iε}` (hence the
whole radial cut through it) avoids the spectrum of `U_E`. Then the cut phase count
`J_ε(E) = (E|Ω|/2 - tr(-i log_ε U_E)) / (2π)` takes the same value at `E₁` and `E₂`. Here the
trace is written as the multiplicity-weighted eigenvalue sum `∑_{z ≠ 1} mult(z) argCut ε z`.
Proved from `cutPhaseSum_monodromyAt_sub` and Green's formula `∫ b = 2|Ω|` (part of the
boundary parametrization). -/
theorem cutPhaseCount_const {Ω : Set ℂ} {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε < 2 * π) (E₁ E₂ : ℝ) (h1 : 0 < E₁) (h12 : E₁ ≤ E₂)
    (hcut : ∀ E ∈ Set.Icc E₁ E₂,
      Complex.exp (ε * Complex.I) ∉ spectrum ℂ (monodromyAt γ E)) :
    cutPhaseCount Ω γ ε E₂ = cutPhaseCount Ω γ ε E₁ := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  have h := cutPhaseSum_monodromyAt_sub hK hclosed hε0 hε E₁ E₂ h1 h12 hcut
  have harea : ∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ = 2 * (volume Ω).toReal := by
    rw [integral_areaDensity_eq hK hclosed]; exact hγ.area
  rw [harea] at h
  unfold cutPhaseCount
  rw [div_left_inj' (by positivity)]
  linarith

/-- Proposition 7.10 and the Cayley correspondence (Cayley bound at a nonresonant energy, on
eigenvectors): for a bounded smooth Jordan domain and a nonresonant energy `E > 0`, the Cayley
transform `K_E` is bounded above, `K_E ≤ A`. Through the Cayley correspondence (an eigenvalue
`e^{it}` of `U_E`, `0 < t < 2π`, is the eigenvalue `cot(t/2)` of `K_E`), this is stated on
eigenvectors: `U_E v = e^{it} v` with `v ≠ 0` and `0 < t < 2π` implies `cot(t/2) ≤ A`.
Proved from `uniform_cayley_rank_bound` with `m = 0`. -/
theorem cayley_eigenvalue_bound {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ)
    (hE : 0 < E) (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) :
    ∃ A : ℝ, ∀ t : ℝ, 0 < t → t < 2 * π → ∀ v : Ell2, v ≠ 0 →
      monodromyAt γ E v = Complex.exp (t * Complex.I) • v → Real.cot (t / 2) ≤ A := by
  have hm : {i | neumannEigenvalue Ω i = ENNReal.ofReal E}.encard = ((0 : ℕ) : ℕ∞) := by
    rw [Nat.cast_zero, Set.encard_eq_zero]
    exact Set.eq_empty_of_forall_notMem fun i hi => hnr i hi
  obtain ⟨A, a, ha, hA⟩ := uniform_cayley_rank_bound hb hS hsc hγ E hE 0 hm
  exact ⟨A, fun t ht0 ht v hv hUv =>
    (hA E hE (by rw [sub_self, abs_zero]; exact ha) hnr).cot_le ht0 ht hv hUv⟩

/-- Lemma 9.1 (finitely many upper-semicircle eigenphases): for a bounded smooth Jordan domain
and a nonresonant energy `E > 0`, only finitely many eigenvalues of the monodromy `U_E` lie in
the open upper half-plane. Proved, as in the paper, from the Cayley bound `K_E ≤ A`
(`cayley_eigenvalue_bound`), which keeps these eigenvalues at distance at least
`1/(|A| + 1)` from `1`, and the convergence of `∑ mult(z) |z - 1|` (Lemma 4.7), which allows
only finitely many eigenvalues at a fixed positive distance from `1`. -/
theorem upper_eigenvalues_finite {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ)
    (hE : 0 < E) (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) :
    {z : ℂ | 0 < z.im ∧ ∃ v : Ell2, v ≠ 0 ∧ monodromyAt γ E v = z • v}.Finite := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
  obtain ⟨A, hA⟩ := cayley_eigenvalue_bound hb hS hsc hγ E hE hnr
  rw [monodromyAt_eq hK hW] at hA ⊢
  have hUunit : monodromy W ∈ unitary (Ell2 →L[ℂ] Ell2) := by
    rw [monodromy, ← ContinuousLinearMap.star_eq_adjoint]
    exact Unitary.star_mem (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩)
  exact upper_eigen_finite_of_cot_bound hUunit
    (isCompactOperator_monodromy_sub_one hK hclosed hE.le hW)
    (summable_eigenMult_monodromy hK hclosed hE.le hW) A hA

/-- Lemma 9.1 (absolute summability): for a bounded smooth Jordan domain and a nonresonant
energy `E > 0`, the multiplicity-weighted negative-branch phase sum
`∑_{z ∈ σ_p(U_E) \ {1}} Arg₋ z` is absolutely convergent. (The paper also shows that `M(E)` is an
integer; that part is not needed here.) Proved, as in the paper, from the finiteness of the
upper-semicircle eigenvalues (`upper_eigenvalues_finite`), the bound
`|Arg₋ z| ≤ (π/2)|z - 1|` on the lower semicircle and the trace-class property of `U_E - I`
(Lemma 4.7, `summable_eigenMult_monodromy`), which makes `∑ mult(z) |z - 1|` finite. -/
theorem phase_summable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ)
    (hE : 0 < E) (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) :
    Summable (phaseTerm (monodromyAt γ E)) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
  have hfin := upper_eigenvalues_finite hb hS hsc hγ E hE hnr
  rw [monodromyAt_eq hK hW] at hfin ⊢
  have hUunit : monodromy W ∈ unitary (Ell2 →L[ℂ] Ell2) := by
    rw [monodromy, ← ContinuousLinearMap.star_eq_adjoint]
    exact Unitary.star_mem (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩)
  exact summable_phaseTerm_of_upper_finite hUunit hfin
    (summable_eigenMult_monodromy hK hclosed hE.le hW)

/-- Lemma 8.6 (negative index at small energy), on Herglotz data: there is `δ > 0` such that
for `0 < E < δ` and every transport `W` at energy `E`, the Herglotz form is nonnegative on the
kernel of a single linear functional: `herglotzForm W γ E a ≥ 0` whenever `L a = 0`. (In the
paper, `𝒜_E = C_E^sc + a_E⁻¹ b_E ⟨b_E, ·⟩` with `C_E^sc ≥ 0`, so the form is nonnegative on
`{⟨b_E, g⟩ = 0}`, i.e. `ind₋ 𝒜_E ≤ 1`.)
Proved (in `RequestProject/SmallEnergyCore.lean`) through the Schur complement along the
constant mode and the analytic estimate `small_energy_schur_core`;
simple connectivity is not needed for this lemma. The abstract index count is
`negIndex_le_one_of_nonneg_on_ker`. -/
theorem small_energy_herglotz_bound {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hS : IsSmoothDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) :
    ∃ δ > 0, ∀ E, 0 < E → E < δ → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      ∃ L : (ℝ → ℂ) →ₗ[ℂ] (Fin 1 → ℂ), ∀ a, IsDirDensity a → L a = 0 →
        0 ≤ herglotzForm W γ E a := by
  exact small_energy_herglotz_bound' hb hS.isLipschitzDomain hγ

/-- Lemma 8.7 (positive principal phases at small energy), read on eigenvectors through the
Cayley correspondence: there is `δ > 0` such that for `0 < E < δ`, every orthonormal family of
eigenvectors of `U_E` with eigenvalues `e^{it}`, `cot(t/2) > 0` (that is, positive principal
phases `t ∈ (0, π)`), has at most one member.
Proved, as in the paper, from `ind₋ 𝒜_E ≤ 1` on Herglotz data (`small_energy_herglotz_bound`,
Lemma 8.6) and the Cayley factorization, which turns two positive principal phases into a
two-dimensional negative subspace of `𝒜_E` (`cayleyRankBound_of_herglotzForm_bound`). -/
theorem small_energy_cayley_rank_bound {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hS : IsSmoothDomain Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) :
    ∃ δ > 0, ∀ E, 0 < E → E < δ → CayleyRankBound (monodromyAt γ E) 0 1 := by
  obtain ⟨δ, hδ, hA⟩ := small_energy_herglotz_bound hb hS hγ
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  refine ⟨δ, hδ, fun E hE hEδ => ?_⟩
  obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK E
  obtain ⟨L, hL⟩ := hA E hE hEδ W hW
  rw [monodromyAt_eq hK hW]
  exact cayleyRankBound_of_herglotzForm_bound hK hclosed hW 0 0 le_rfl L
    (fun a ha hLa => by rw [zero_mul, neg_zero]; exact hL a ha hLa)

/-- Lemma 8.8 (initial value of the phase count): for a bounded smooth Jordan domain,
`M(E) = 1` for all sufficiently small `E > 0`. Proved, as in the paper (Lemmas 8.7–8.8): the
trace-norm bound `‖U_E - I‖_{𝒮₁} ≤ C E` keeps `-1` out of the spectrum and makes the principal
phase sum `O(E)`; the principal cut phase count `J_π` is constant (`cutPhaseCount_const`) and
tends to `0`, so `∑ θ_j = E|Ω|/2`; exactly one principal phase is positive
(`small_energy_cayley_rank_bound`, and the sum is positive), and `M = J_π + 1 = 1`. -/
theorem phaseCount_initial {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    ∃ δ > 0, ∀ E, 0 < E → E < δ → phaseCount Ω γ E = 1 := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  obtain ⟨Cq, hCq0, hT⟩ := exists_linear_traceBound_monodromyAt hK hclosed
  obtain ⟨δr, hδr, hrank⟩ := small_energy_cayley_rank_bound hb hS hγ
  set v := (volume Ω).toReal with hv
  have hvpos : 0 < v := ENNReal.toReal_pos
    (hS.1.1.measure_pos volume hS.1.2.nonempty).ne' hb.measure_lt_top.ne
  have hpi := Real.pi_pos
  set δ := min δr (1 / (Cq + 1)) with hδ
  have hδpos : 0 < δ := lt_min hδr (by positivity)
  have hsmall : ∀ E, 0 < E → E < δ → Cq * E < 2 := by
    intro E hE hEδ
    have h1 : E < 1 / (Cq + 1) := hEδ.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith
  -- `-1` avoids the spectrum
  have hcut : ∀ E, 0 < E → E < δ →
      Complex.exp (π * Complex.I) ∉ spectrum ℂ (monodromyAt γ E) := by
    intro E hE hEδ hmem
    rw [Complex.exp_pi_mul_I] at hmem
    obtain ⟨w, hw0, hw⟩ := exists_eigen_of_mem_spectrum
      (isCompactOperator_monodromyAt_sub_one hK hclosed hE.le) hmem (by norm_num)
    exact not_eigen_neg_one_of_traceBound (monodromyAt_mem_unitary hK E)
      (isCompactOperator_monodromyAt_sub_one hK hclosed hE.le) (hT E hE.le)
      (hsmall E hE hEδ) hw0 hw
  -- `J_π(E) = O(E)`
  set c := (v / 2 + π / 2 * Cq) / (2 * π) with hc
  have hJb : ∀ E, 0 < E → E < δ → |cutPhaseCount Ω γ π E| ≤ c * E := by
    intro E hE hEδ
    obtain ⟨-, hP⟩ := cutPhaseSum_pi_bound (monodromyAt_mem_unitary hK E)
      (isCompactOperator_monodromyAt_sub_one hK hclosed hE.le) (hT E hE.le)
    rw [cutPhaseCount, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
      div_le_iff₀ (by positivity)]
    have h1 : |v * E / 2 - cutPhaseSum π (monodromyAt γ E)| ≤
        v * E / 2 + π / 2 * (Cq * E) := by
      have := abs_sub (v * E / 2) (cutPhaseSum π (monodromyAt γ E))
      rw [abs_of_pos (by positivity : (0 : ℝ) < v * E / 2)] at this
      linarith
    calc |v * E / 2 - cutPhaseSum π (monodromyAt γ E)| ≤ v * E / 2 + π / 2 * (Cq * E) := h1
      _ = c * E * (2 * π) := by rw [hc]; field_simp
  -- `J_π = 0`
  have hJ0 : ∀ E, 0 < E → E < δ → cutPhaseCount Ω γ π E = 0 := by
    intro E hE hEδ
    have hev : ∀ᶠ F in 𝓝[>] (0 : ℝ), |cutPhaseCount Ω γ π E| ≤ c * F := by
      filter_upwards [Ioo_mem_nhdsGT hE] with F hF
      rw [cutPhaseCount_const hγ hpi (by linarith) F E hF.1 hF.2.le
        (fun G hG => hcut G (hF.1.trans_le hG.1) (hG.2.trans_lt hEδ))]
      exact hJb F hF.1 (hF.2.trans hEδ)
    have hlim : Tendsto (fun F => c * F) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h : Tendsto (fun F : ℝ => c * F) (𝓝 (0 : ℝ)) (𝓝 (c * 0)) :=
        tendsto_id.const_mul c
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    exact abs_nonpos_iff.mp (ge_of_tendsto hlim hev)
  refine ⟨δ, hδpos, fun E hE hEδ => ?_⟩
  set U := monodromyAt γ E with hUdef
  have hUu : U ∈ unitary (Ell2 →L[ℂ] Ell2) := monodromyAt_mem_unitary hK E
  have hUc : IsCompactOperator ⇑(U - 1) := isCompactOperator_monodromyAt_sub_one hK hclosed hE.le
  obtain ⟨hsa, hle⟩ := arcCount_le (ε := π) (A := 0) hUu hUc (by linarith)
    (fun t ht0 htπ => by
      rw [Real.cot_eq_cos_div_sin]
      exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
        (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)))
    (hrank E hE (hEδ.trans_le (min_le_left _ _)))
  obtain ⟨hcs, -⟩ := cutPhaseSum_pi_bound hUu hUc (hT E hE.le)
  have hps : Summable (phaseTerm U) := by
    have : phaseTerm U = fun z => cutPhaseTerm π U z - 2 * π * arcTerm π U z := by
      funext z; rw [cutPhaseTerm_eq]; ring
    rw [this]; exact hcs.sub (hsa.mul_left _)
  have hdec := cutPhaseSum_eq_add hps hsa
  have hJ := hJ0 E hE hEδ
  have hM : phaseCount Ω γ E = cutPhaseCount Ω γ π E + arcCount π U := by
    rw [phaseCount, cutPhaseCount, ← hUdef, hdec]; field_simp; ring
  -- the principal phase sum is `E|Ω|/2 > 0`
  have hP : cutPhaseSum π U = v * E / 2 := by
    rw [cutPhaseCount, div_eq_zero_iff] at hJ
    rcases hJ with h | h
    · linarith
    · linarith
  have hge : 1 ≤ arcCount π U := by
    by_contra hlt
    push_neg at hlt
    have hall : ∀ z, arcTerm π U z = 0 := by
      intro z
      by_contra hz
      have h1 : 1 ≤ arcTerm π U z := by
        unfold arcTerm at hz ⊢
        split_ifs at hz ⊢ with h
        · have : eigenMult U z ≠ 0 := by exact_mod_cast hz
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
        · exact absurd rfl hz
      have h2 : arcTerm π U z ≤ arcCount π U :=
        hsa.le_tsum z (fun j _ => arcTerm_nonneg π U j)
      linarith
    have hnp : cutPhaseSum π U ≤ 0 := by
      refine tsum_nonpos fun z => ?_
      rw [cutPhaseTerm_eq, hall z, mul_zero, add_zero, phaseTerm]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (argNeg_nonpos _)
    have : 0 < v * E / 2 := by positivity
    linarith
  rw [hM, hJ0 E hE hEδ, zero_add]
  exact le_antisymm (by exact_mod_cast hle) hge

/-- Lemma 9.4 (constancy away from the Neumann spectrum): `M` is constant on every interval
`[E₁, E₂] ⊆ (0, ∞)` containing no Neumann eigenvalue. Proved, as in the paper: locally the
uniform Cayley bound `K_E ≤ A` (`uniform_cayley_rank_bound`) excludes an arc
`{e^{it} : 0 < t ≤ ε}` from the spectrum of `U_E`, so `M = J_ε` there, and `J_ε` is locally
constant (`cutPhaseCount_const`); local constancy on an interval gives constancy. -/
theorem phaseCount_const {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E₁ E₂ : ℝ)
    (h1 : 0 < E₁) (h12 : E₁ ≤ E₂)
    (hno : ∀ j, ∀ E ∈ Set.Icc E₁ E₂, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) :
    phaseCount Ω γ E₂ = phaseCount Ω γ E₁ := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  -- local constancy
  have hloc : ∀ E₀ ∈ Set.Icc E₁ E₂, ∃ a > 0, ∀ E ∈ Set.Icc E₁ E₂, ∀ E' ∈ Set.Icc E₁ E₂,
      |E - E₀| < a → |E' - E₀| < a → E ≤ E' → phaseCount Ω γ E' = phaseCount Ω γ E := by
    intro E₀ hE₀
    have hpos₀ : 0 < E₀ := h1.trans_le hE₀.1
    have hm : {i | neumannEigenvalue Ω i = ENNReal.ofReal E₀}.encard = ((0 : ℕ) : ℕ∞) := by
      rw [Nat.cast_zero, Set.encard_eq_zero]
      exact Set.eq_empty_of_forall_notMem fun i hi => hno i E₀ hE₀ hi
    obtain ⟨A, a, ha, hA⟩ := uniform_cayley_rank_bound hb hS hsc hγ E₀ hpos₀ 0 hm
    obtain ⟨ε, hε0, hεπ, hεA⟩ := exists_cot_half_gt A
    have hnoarc : ∀ E ∈ Set.Icc E₁ E₂, |E - E₀| < a → ∀ t, 0 < t → t ≤ ε → ∀ v : Ell2,
        v ≠ 0 → monodromyAt γ E v ≠ Complex.exp (t * Complex.I) • v := fun E hE hEa =>
      (hA E (h1.trans_le hE.1) hEa (fun j => hno j E hE)).no_arc_eigen hεπ hεA
    have hJ : ∀ E ∈ Set.Icc E₁ E₂, |E - E₀| < a →
        phaseCount Ω γ E = cutPhaseCount Ω γ ε E := by
      intro E hE hEa
      rw [phaseCount, cutPhaseCount, cutPhaseSum_eq_phaseSum (monodromyAt_mem_unitary hK E)
        (isCompactOperator_monodromyAt_sub_one hK hclosed (h1.trans_le hE.1).le)
        (fun t ht0 htε => hnoarc E hE hEa t ht0 htε.le)]
    refine ⟨a, ha, fun E hE E' hE' hEa hE'a hEE' => ?_⟩
    rw [hJ E hE hEa, hJ E' hE' hE'a]
    refine cutPhaseCount_const hγ hε0 (by linarith [Real.pi_pos]) E E'
      (h1.trans_le hE.1) hEE' (fun F hF => ?_)
    have hFI : F ∈ Set.Icc E₁ E₂ := ⟨hE.1.trans hF.1, hF.2.trans hE'.2⟩
    have hFa : |F - E₀| < a := by
      rw [abs_lt] at hEa hE'a ⊢; constructor <;> linarith [hF.1, hF.2]
    exact exp_mul_I_notMem_spectrum (isCompactOperator_monodromyAt_sub_one hK hclosed
      (h1.trans_le hFI.1).le) hε0 hεπ (fun v hv => hnoarc F hFI hFa ε hε0 le_rfl v hv)
  -- constancy on the interval
  let f : Set.Icc E₁ E₂ → ℝ := fun E => phaseCount Ω γ E
  have hf : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨a, ha, hx⟩ := hloc x x.2
    filter_upwards [Metric.ball_mem_nhds x ha] with y hy
    have hy' : |(y : ℝ) - x| < a := by
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at hy; exact hy
    have hx0 : |(x : ℝ) - x| < a := by rw [sub_self, abs_zero]; exact ha
    rcases le_total (y : ℝ) x with h | h
    · exact (hx y y.2 x x.2 hy' hx0 h).symm
    · exact hx x x.2 y y.2 hx0 hy' h
  haveI : PreconnectedSpace (Set.Icc E₁ E₂) := Subtype.preconnectedSpace isPreconnected_Icc
  exact hf.apply_eq_of_preconnectedSpace ⟨E₂, h12, le_rfl⟩ ⟨E₁, le_rfl, h12⟩

/-- Lemma 9.5 (bound on a jump): let `μ = μ_j > 0` be a Neumann eigenvalue of multiplicity
`m`, here the number of indices `i` with `μ_i = μ`. Then, for nonresonant energies
`0 < E₁ < μ < E₂` close enough to `μ`, `M(E₂) ≤ M(E₁) + m`. Proved, as in the paper: take `A` from
the resonance rank bound (`uniform_cayley_rank_bound`) and a cut `e^{iε}` with `cot(ε/2) > A`
outside the (countable) set of eigenvalues of `U_μ`; it stays outside the spectrum of `U_E` for
`E` near `μ`, so `J_ε` is constant there (`cutPhaseCount_const`), and
`M(E) = J_ε(E) + n_{(0,ε)}(U_E)` with `0 ≤ n_{(0,ε)}(U_E) ≤ m`. -/
theorem phaseCount_jump {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (j : ℕ)
    (hj : 0 < neumannEigenvalue Ω j) (m : ℕ)
    (hm : {i | neumannEigenvalue Ω i = neumannEigenvalue Ω j}.encard = m) :
    ∃ δ > 0, ∀ E₁ E₂, 0 < E₁ → (neumannEigenvalue Ω j).toReal - δ < E₁ →
      E₁ < (neumannEigenvalue Ω j).toReal → (neumannEigenvalue Ω j).toReal < E₂ →
      E₂ < (neumannEigenvalue Ω j).toReal + δ →
      (∀ i, neumannEigenvalue Ω i ≠ ENNReal.ofReal E₁) →
      (∀ i, neumannEigenvalue Ω i ≠ ENNReal.ofReal E₂) →
      phaseCount Ω γ E₂ ≤ phaseCount Ω γ E₁ + m := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  have hfin := (neumannEigenvalue_lt_top hS.isLipschitzDomain j).ne
  set μ := (neumannEigenvalue Ω j).toReal with hμdef
  have hμ0 : 0 < μ := ENNReal.toReal_pos hj.ne' hfin
  have hm' : {i | neumannEigenvalue Ω i = ENNReal.ofReal μ}.encard = m := by
    rw [hμdef, ENNReal.ofReal_toReal hfin]; exact hm
  obtain ⟨A, a, ha, hA⟩ := uniform_cayley_rank_bound hb hS hsc hγ μ hμ0 m hm'
  obtain ⟨ε₀, hε₀, hε₀π, hε₀A⟩ := exists_cot_half_gt A
  -- the cut directions in `(0, ε₀)` that are eigenvalues of `U_μ` form a countable set
  set S : Set ℝ := {t | t ∈ Set.Ioo 0 ε₀ ∧ ∃ v : Ell2, v ≠ 0 ∧
    monodromyAt γ μ v = Complex.exp (t * Complex.I) • v} with hSdef
  have hS_count : S.Countable := by
    obtain ⟨W, hW⟩ := transport_exists_of_lipschitz γ hK μ
    have hsum := summable_eigenMult_monodromy hK hclosed hμ0.le hW
    rw [← monodromyAt_eq hK hW] at hsum
    refine Set.MapsTo.countable_of_injOn (f := fun t : ℝ => Complex.exp (t * Complex.I))
      (t := Subtype.val '' Function.support
        (fun z : {z : ℂ // z ≠ 1} => (eigenMult (monodromyAt γ μ) z : ℝ) * ‖(z : ℂ) - 1‖))
      ?_ ?_ (hsum.countable_support.image _)
    · rintro t ⟨⟨ht0, htε⟩, v, hv0, hv⟩
      have hne : Complex.exp (t * Complex.I) ≠ 1 := by
        intro h1
        have := congrArg Complex.im h1
        rw [Complex.exp_ofReal_mul_I_im, Complex.one_im] at this
        linarith [Real.sin_pos_of_pos_of_lt_pi ht0 (htε.trans hε₀π)]
      refine ⟨⟨_, hne⟩, ?_, rfl⟩
      haveI := finiteDimensional_eigenspace
        (isCompactOperator_monodromyAt_sub_one hK hclosed hμ0.le) hne
      have hpos : 0 < eigenMult (monodromyAt γ μ) (Complex.exp (t * Complex.I)) :=
        Module.finrank_pos_iff_exists_ne_zero.mpr
          ⟨⟨v, Module.End.mem_eigenspace_iff.mpr hv⟩, fun h => hv0 (by simpa using h)⟩
      have hn : 0 < ‖Complex.exp (t * Complex.I) - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      exact (mul_pos (by exact_mod_cast hpos) hn).ne'
    · intro s hs t ht hst
      have := congrArg Complex.arg hst
      simp only at this
      rwa [Complex.arg_exp_mul_I, Complex.arg_exp_mul_I, (toIocMod_eq_self _).mpr,
        (toIocMod_eq_self _).mpr] at this
      all_goals constructor <;> linarith [hs.1.1, hs.1.2, ht.1.1, ht.1.2]
  -- choose the cut
  obtain ⟨ε, ⟨hε0, hεε₀⟩, hεS⟩ : (Set.Ioo 0 ε₀ \ S).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hne
    have h0 := measure_mono_null hne (hS_count.measure_zero MeasureTheory.volume)
    rw [Real.volume_Ioo, sub_zero, ENNReal.ofReal_eq_zero] at h0
    linarith
  have hεπ : ε < π := hεε₀.trans hε₀π
  have hεA : A < Real.cot (ε / 2) :=
    lt_of_lt_of_le hε₀A (cot_half_le_cot_half hε0 hεε₀.le hε₀π)
  have hspecμ : Complex.exp (ε * Complex.I) ∉ spectrum ℂ (monodromyAt γ μ) :=
    exp_mul_I_notMem_spectrum (isCompactOperator_monodromyAt_sub_one hK hclosed hμ0.le) hε0 hεπ
      (fun v hv h => hεS ⟨⟨hε0, hεε₀⟩, v, hv, h⟩)
  -- the cut stays outside the spectrum near `μ`
  have hnhds : {E : ℝ | IsUnit (algebraMap ℂ (Ell2 →L[ℂ] Ell2) (Complex.exp (ε * Complex.I)) -
      monodromyAt γ E)} ∈ 𝓝 μ := by
    rw [spectrum.mem_iff, not_not] at hspecμ
    exact (continuousAt_const.sub (continuousAt_monodromyAt hK hclosed hμ0)).preimage_mem_nhds
      (Units.isOpen.mem_nhds hspecμ)
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨min a δ₁, lt_min ha hδ₁, ?_⟩
  intro E₁ E₂ hE₁0 hE₁lo hE₁hi hE₂lo hE₂hi hnr₁ hnr₂
  have hcut : ∀ E ∈ Set.Icc E₁ E₂,
      Complex.exp (ε * Complex.I) ∉ spectrum ℂ (monodromyAt γ E) := by
    intro E hE
    have hEb : E ∈ Metric.ball μ δ₁ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [min_le_right a δ₁, hE.1, hE.2]
    have := hball hEb
    rw [spectrum.mem_iff, not_not]
    exact this
  have hJ := cutPhaseCount_const hγ hε0 (by linarith [Real.pi_pos]) E₁ E₂ hE₁0
    (by linarith) hcut
  -- `M = J_ε + n_{(0,ε)}` with `0 ≤ n_{(0,ε)} ≤ m`
  have hdec : ∀ E, 0 < E → |E - μ| < a → (∀ i, neumannEigenvalue Ω i ≠ ENNReal.ofReal E) →
      phaseCount Ω γ E = cutPhaseCount Ω γ ε E + arcCount ε (monodromyAt γ E) ∧
        arcCount ε (monodromyAt γ E) ≤ m := by
    intro E hE hEa hnr
    obtain ⟨hsa, hle⟩ := arcCount_le (monodromyAt_mem_unitary hK E)
      (isCompactOperator_monodromyAt_sub_one hK hclosed hE.le) (by linarith [Real.pi_pos])
      (fun t ht0 htε => lt_of_lt_of_le hεA (cot_half_le_cot_half ht0 htε.le hεπ))
      (hA E hE hEa hnr)
    refine ⟨?_, hle⟩
    rw [phaseCount, cutPhaseCount, cutPhaseSum_eq_add (phase_summable hb hS hsc hγ E hE hnr) hsa]
    have := Real.pi_pos
    field_simp
    ring
  have hE₁a : |E₁ - μ| < a := by
    rw [abs_lt]; constructor <;> linarith [min_le_left a δ₁]
  have hE₂a : |E₂ - μ| < a := by
    rw [abs_lt]; constructor <;> linarith [min_le_left a δ₁]
  obtain ⟨h1eq, -⟩ := hdec E₁ hE₁0 hE₁a hnr₁
  obtain ⟨h2eq, h2le⟩ := hdec E₂ (by linarith) hE₂a hnr₂
  rw [h1eq, h2eq, hJ]
  linarith [arcCount_nonneg ε (monodromyAt γ E₁)]

/-- Lemma 9.6 (comparison with the strict count): for a bounded smooth Jordan domain and every
nonresonant `E > 0`, `M(E) ≤ N_N(E)`. Proved, as in the paper, by induction across the
finitely many eigenvalues below `E`, from the initial value (Lemma 8.8), the constancy away
from the spectrum (Lemma 9.4) and the jump bound (Lemma 9.5). -/
theorem phaseCount_le_count {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ)
    (hE : 0 < E) (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) :
    ENNReal.ofReal (phaseCount Ω γ E) ≤ (neumannCount Ω (ENNReal.ofReal E) : ENNReal) := by
  have hL := hS.isLipschitzDomain
  have hfin : ∀ j, neumannEigenvalue Ω j ≠ ⊤ := fun j => (neumannEigenvalue_lt_top hL j).ne
  set lam : ℕ → ℝ := fun j => (neumannEigenvalue Ω j).toReal with hlam
  have hμ : ∀ j, neumannEigenvalue Ω j = ENNReal.ofReal (lam j) := fun j =>
    (ENNReal.ofReal_toReal (hfin j)).symm
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => ENNReal.toReal_nonneg
  -- conversions between the two descriptions of the spectrum
  have hne : ∀ j (t : ℝ), 0 ≤ t → (neumannEigenvalue Ω j ≠ ENNReal.ofReal t ↔ lam j ≠ t) := by
    intro j t ht
    rw [hμ j, ne_eq, ne_eq, ENNReal.ofReal_eq_ofReal_iff (hlam0 j) ht]
  have hlt : ∀ (t : ℝ), 0 < t → {j | neumannEigenvalue Ω j < ENNReal.ofReal t} =
      {j | lam j < t} := by
    intro t ht
    ext j
    simp only [Set.mem_setOf_eq]
    rw [hμ j, ENNReal.ofReal_lt_ofReal_iff ht]
  have hcount : neumannCount Ω (ENNReal.ofReal E) = {j | lam j < E}.encard := by
    rw [neumannCount, hlt E hE]
  by_cases hinf : {j | lam j < E}.Finite
  swap
  · rw [hcount, Set.encard_eq_top_iff.mpr hinf, ENat.toENNReal_top]; exact le_top
  have h0 : lam 0 = 0 := by
    simp [hlam, neumannEigenvalue_zero Ω hL.1.1 hL.1.2.nonempty hb]
  have key := phase_le_count_of_jumps lam h0 (phaseCount Ω γ)
    (by
      obtain ⟨δ, hδ, h⟩ := phaseCount_initial hb hS hγ
      exact ⟨δ, hδ, fun E hE hEδ _ => (h E hE hEδ).le⟩)
    (by
      intro E₁ E₂ h1 h12 hno
      refine (phaseCount_const hb hS hsc hγ E₁ E₂ h1 h12 fun j t ht => ?_).le
      rw [hne j t (h1.le.trans ht.1)]
      rintro rfl
      exact hno j ht)
    (by
      intro j hj m hm
      have hj' : 0 < neumannEigenvalue Ω j := by
        rw [hμ j]; exact ENNReal.ofReal_pos.mpr hj
      have hset : {i | neumannEigenvalue Ω i = neumannEigenvalue Ω j} = {i | lam i = lam j} := by
        ext i
        simp only [Set.mem_setOf_eq]
        exact ENNReal.toReal_eq_toReal_iff' (hfin i) (hfin j) |>.symm
      obtain ⟨δ, hδ, h⟩ := phaseCount_jump hb hS hsc hγ j hj' m (hset ▸ hm)
      refine ⟨δ, hδ, fun E₁ E₂ h1 h2 h3 h4 h5 h6 h7 => h E₁ E₂ h1 h2 h3 h4 h5 ?_ ?_⟩
      · intro i; rw [hne i E₁ h1.le]; exact h6 i
      · intro i; rw [hne i E₂ (h1.trans (h3.trans h4)).le]; exact h7 i)
    E hE (fun j => (hne j E hE.le).mp (hnr j)) hinf
  rw [hcount, ← hinf.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal key

/-- Lemmas 9.1 and 9.6 (the phase count at a nonresonant energy): for a bounded smooth Jordan
domain and a nonresonant energy `E > 0` (no Neumann eigenvalue equals `E`), the nonunit
eigenvalues of `U_E` can be listed, with multiplicity, as a family `z_i` of unimodular numbers
`≠ 1` whose negative arguments `Arg₋ z_i` are summable, and the phase integer
`M(E) = (E|Ω|/2 - ∑ Arg₋ z_i)/(2π)` is at most `N_N(E)`. Proved from Lemma 9.1
(`phase_summable`), Lemma 9.6 (`phaseCount_le_count`) and the compactness of `U_E - I`
(Lemma 4.7), which makes every eigenspace at `z ≠ 1` finite-dimensional. -/
theorem smooth_phase_count {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ)
    (hE : 0 < E) (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E)
    (W : ℝ → Ell2 →L[ℂ] Ell2) (hW : IsTransport γ E W) :
    ∃ (ι : Type) (z : ι → ℂ), (∀ i, ‖z i‖ = 1) ∧ (∀ i, z i ≠ 1) ∧
      (∀ (c : ℂ) (v : Ell2), v ≠ 0 → monodromy W v = c • v → c ≠ 1 → ∃ i, z i = c) ∧
      Summable (fun i => argNeg (z i)) ∧
      ENNReal.ofReal (((volume Ω).toReal * E / 2 - ∑' i, argNeg (z i)) / (2 * π)) ≤
        (neumannCount Ω (ENNReal.ofReal E) : ENNReal) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  have hUunit : monodromy W ∈ unitary (Ell2 →L[ℂ] Ell2) := by
    rw [monodromy, ← ContinuousLinearMap.star_eq_adjoint]
    exact Unitary.star_mem (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩)
  have hs := phase_summable hb hS hsc hγ E hE hnr
  rw [monodromyAt_eq hK hW] at hs
  obtain ⟨ι, z, hz, h1, hall, hsum, htsum⟩ := exists_eigen_family hUunit
    (isCompactOperator_monodromy_sub_one hK hclosed hE.le hW) hs
  refine ⟨ι, z, hz, h1, hall, hsum, ?_⟩
  have h := phaseCount_le_count hb hS hsc hγ E hE hnr
  rwa [phaseCount, monodromyAt_eq hK hW, ← htsum] at h

/-- Theorem 9.7 at nonresonant energies (Lemma 9.2 combined with the phase count): for a
bounded smooth Jordan domain and a nonresonant `E > 0`,
`N_N(E) ≥ E |Ω| / (4π) + ‖U_E - I‖ / (2π)`. `U_E - I` is compact (Lemma 4.7), so if
`U_E ≠ I` its norm is `|z - 1|` for an eigenvalue `z ≠ 1` of `U_E` (Lemma 9.2). -/
theorem smooth_count_nonresonant {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (E : ℝ) (hE : 0 < E)
    (hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E) (W : ℝ → Ell2 →L[ℂ] Ell2)
    (hW : IsTransport γ E W) :
    volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) +
        ENNReal.ofReal (‖monodromy W - 1‖ / (2 * π)) ≤
      (neumannCount Ω (ENNReal.ofReal E) : ENNReal) := by
  obtain ⟨ι, z, hz, h1, hall, hs, hM⟩ := smooth_phase_count hb hS hsc hγ E hE hnr W hW
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  have hUunit : monodromy W ∈ unitary (Ell2 →L[ℂ] Ell2) := by
    rw [monodromy, ← ContinuousLinearMap.star_eq_adjoint]
    exact Unitary.star_mem (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩)
  have hr : ‖monodromy W - 1‖ = 0 ∨ ∃ j, ‖z j - 1‖ = ‖monodromy W - 1‖ := by
    by_cases hU1 : monodromy W = 1
    · left; rw [hU1, sub_self, norm_zero]
    · right
      obtain ⟨c, v, hv0, hv, hc1, hcn⟩ := exists_eigenvalue_norm_sub_one hUunit
        (isCompactOperator_monodromy_sub_one hK hclosed hE.le hW) hU1
      obtain ⟨i, rfl⟩ := hall c v hv0 hv hc1
      exact ⟨i, hcn⟩
  have key := phase_integer_ge hz h1 hs E (volume Ω).toReal _ hr
  rw [count_lhs_eq_ofReal hb.measure_lt_top.ne hE.le]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hM
  rw [mul_comm ((volume Ω).toReal) E]
  exact key

/-- Theorem 9.7 (quantitative smooth counting inequality): for a bounded smooth Jordan
domain and every `E > 0`, `N_N(E) ≥ E |Ω| / (4π) + ‖U_E - I‖ / (2π)`. Proved, as in the paper,
from the nonresonant case by approaching `E` from below through nonresonant energies, using
the continuity of `E ↦ U_E` (Lemma 4.7). -/
theorem smooth_count {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (E : ℝ)
    (hE : 0 < E) (W : ℝ → Ell2 →L[ℂ] Ell2) (hW : IsTransport γ E W) :
    volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) +
        ENNReal.ofReal (‖monodromy W - 1‖ / (2 * π)) ≤
      (neumannCount Ω (ENNReal.ofReal E) : ENNReal) := by
  classical
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  choose Ws hWs using fun E' : ℝ => transport_exists_of_lipschitz γ hK E'
  have hWE : monodromy (Ws E) = monodromy W := by
    unfold monodromy
    rw [transport_unique_of_lipschitz γ hK E (hWs E) hW ⟨by positivity, le_rfl⟩]
  set N : ℕ∞ := neumannCount Ω (ENNReal.ofReal E) with hNdef
  by_cases hN : N = ⊤
  · rw [hN, ENat.toENNReal_top]; exact le_top
  set T := {j : ℕ | neumannEigenvalue Ω j < ENNReal.ofReal E} with hTdef
  have hT : T.Finite := Set.encard_ne_top_iff.mp hN
  have hN' : (N : ENNReal) ≠ ⊤ := by simpa using hN
  have hvol : volume Ω ≠ ⊤ := hb.measure_lt_top.ne
  -- the real form of the left-hand side
  set g : ℝ → ℝ := fun E' => (volume Ω).toReal * E' / (4 * π) +
    ‖monodromy (Ws E') - 1‖ / (2 * π) with hg
  -- nonresonant energies just below `E`
  have hev1 : ∀ᶠ E' in 𝓝[<] E, E' ∈ Set.Ioo 0 E := Ioo_mem_nhdsLT hE
  have hev2 : ∀ᶠ E' in 𝓝[<] E, ∀ j ∈ T, (neumannEigenvalue Ω j).toReal < E' :=
    hT.eventually_all.mpr fun j hj => by
      have hne : neumannEigenvalue Ω j ≠ ⊤ := ne_top_of_lt hj
      have hlt : (neumannEigenvalue Ω j).toReal < E :=
        (ENNReal.toReal_lt_toReal hne ENNReal.ofReal_ne_top).mpr hj |>.trans_le
          (by rw [ENNReal.toReal_ofReal hE.le])
      exact Ioo_mem_nhdsLT hlt |> Filter.mem_of_superset <| fun x hx => hx.1
  have hev : ∀ᶠ E' in 𝓝[<] E, g E' ≤ (N : ENNReal).toReal := by
    filter_upwards [hev1, hev2] with E' hE' hT'
    have hlt : ENNReal.ofReal E' < ENNReal.ofReal E :=
      (ENNReal.ofReal_lt_ofReal_iff hE).mpr hE'.2
    have hnr : ∀ j, neumannEigenvalue Ω j ≠ ENNReal.ofReal E' := by
      intro j hj
      have hjT : j ∈ T := by
        show neumannEigenvalue Ω j < _
        rw [hj]; exact hlt
      have := hT' j hjT
      rw [hj, ENNReal.toReal_ofReal hE'.1.le] at this
      exact lt_irrefl _ this
    have hcount : neumannCount Ω (ENNReal.ofReal E') = N := by
      rw [hNdef, neumannCount, neumannCount]
      congr 1
      ext j
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h; exact h.trans hlt
      · intro h
        have hne : neumannEigenvalue Ω j ≠ ⊤ := ne_top_of_lt h
        rw [← ENNReal.ofReal_toReal hne]
        exact (ENNReal.ofReal_lt_ofReal_iff hE'.1).mpr (hT' j h)
    have h := smooth_count_nonresonant hb hS hsc hγ E' hE'.1 hnr (Ws E') (hWs E')
    rw [hcount, count_lhs_eq_ofReal hvol hE'.1.le] at h
    exact (ENNReal.ofReal_le_iff_le_toReal hN').mp h
  -- continuity of `g` at `E`
  have hcont : ContinuousAt g E := by
    have hm := (hasDerivAt_monodromy_energy hK hclosed hWs hE).continuousAt
    exact ((continuous_const.mul continuous_id).div_const _).continuousAt.add
      ((hm.sub continuousAt_const).norm.div_const _)
  have hgE : g E ≤ (N : ENNReal).toReal :=
    le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
  rw [count_lhs_eq_ofReal hvol hE.le, ← hWE]
  exact (ENNReal.ofReal_le_iff_le_toReal hN').mpr hgE


/-- Corollary 9.8 (quantitative smooth eigenvalue inequality): for a bounded smooth Jordan
domain and `j ≥ 1`, `|Ω| μ_j + 2 ‖U_{μ_j} - I‖ ≤ 4π j`. -/
theorem smooth_eigen {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) (j : ℕ)
    (hj : 1 ≤ j) (W : ℝ → Ell2 →L[ℂ] Ell2)
    (hW : IsTransport γ (neumannEigenvalue Ω j).toReal W) :
    volume Ω * neumannEigenvalue Ω j + ENNReal.ofReal (2 * ‖monodromy W - 1‖) ≤
      ENNReal.ofReal (4 * π * j) := by
  have hL := hS.isLipschitzDomain
  have hfin := (neumannEigenvalue_lt_top hL j).ne
  have hE : 0 < (neumannEigenvalue Ω j).toReal :=
    ENNReal.toReal_pos (neumannEigenvalue_pos hb hL j hj).ne' hfin
  have h := smooth_count hb hS hsc hγ _ hE W hW
  rw [ENNReal.ofReal_toReal hfin] at h
  have hc : ((neumannCount Ω (neumannEigenvalue Ω j) : ℕ∞) : ENNReal) ≤ (j : ENNReal) := by
    have := ENat.toENNReal_le.mpr
      (encard_lt_le_of_monotone _ (neumannEigenvalue_monotone Ω) j)
    simpa [neumannCount] using this
  have h2 := h.trans hc
  have h4 : ENNReal.ofReal (4 * π) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have h4' : ENNReal.ofReal (4 * π) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h3 := mul_le_mul_left h2 (ENNReal.ofReal (4 * π))
  rw [add_mul, ENNReal.div_mul_cancel h4 h4', ← ENNReal.ofReal_mul (by positivity)] at h3
  convert h3 using 2
  · congr 1; field_simp; ring
  · rw [mul_comm (j : ENNReal), ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]

/-! ### Lipschitz domains (Section 10) -/

/-- The data produced by the smooth approximation of Section 10 (Definition 10.8), together
with the properties of it used in the limit argument. For a bounded simply connected Lipschitz
domain `Ω` with boundary parametrization `γ`:
* smooth bounded simply connected domains `Ω_n = f_n(Ω)` with boundary parametrizations `γ'_n`
  (External theorem BZ);
* the curves `γ_n = f_n ∘ γ - f_n(γ(0))`, closed and uniformly Lipschitz, converging uniformly
  to `γ` with bounded lengths, whose monodromies agree with those of `γ'_n`
  (Lemma 10.14, via Lemma 10.3);
* densities `ρ_n = |det Df_n|`, uniformly bounded and converging to `1` a.e., with
  `|Ω_n| = ∫_Ω ρ_n` (Lemma 10.9 and change of variables);
* pulled-back forms `q_n`, `m_n` on `L²(Ω)`: `μ_j(Ω_n)` obeys the min–max bound for
  `q_n / m_n` on subspaces of `H¹(Ω)` (Lemma 10.10), `q_n → q_Ω` and `m_n → 1` uniformly on
  unit spheres of finite-dimensional subspaces of `H¹(Ω)` (Lemma 10.11), and along subsequences
  with convergent eigenvalues there are orthonormal limits of the eigenfunctions
  (the compactness part of Lemma 10.13). -/
structure SmoothApproximation (Ω : Set ℂ) (γ : ℝ → ℂ) where
  /-- The approximating smooth domains `Ω_n`. -/
  dom : ℕ → Set ℂ
  dom_bounded : ∀ n, Bornology.IsBounded (dom n)
  dom_smooth : ∀ n, IsSmoothDomain (dom n)
  dom_simplyConnected : ∀ n, SimplyConnectedSpace (dom n)
  /-- Boundary parametrizations `γ'_n` of `∂Ω_n`. -/
  param : ℕ → ℝ → ℂ
  param_isBoundaryParam : ∀ n, IsBoundaryParam (dom n) (param n)
  /-- The transported curves `γ_n = f_n ∘ γ - f_n(γ(0))`. -/
  curve : ℕ → ℝ → ℂ
  curveLip : ℕ → NNReal
  curve_lipschitz : ∀ n, LipschitzWith (curveLip n) (curve n)
  curve_closed : ∀ n, curve n (2 * π) = curve n 0
  curve_tendsto : TendstoUniformlyOn curve γ atTop (Set.Icc 0 (2 * π))
  curve_length : ∃ B, ∀ n, ∫ θ in (0 : ℝ)..(2 * π), ‖deriv (curve n) θ‖ ≤ B
  monodromy_eq : ∀ n (E : ℝ) (W W' : ℝ → Ell2 →L[ℂ] Ell2), IsTransport (curve n) E W →
    IsTransport (param n) E W' → monodromy W = monodromy W'
  /-- The densities `ρ_n = |det Df_n|`. -/
  density : ℕ → ℂ → ℝ
  densityBound : ℝ
  density_aestronglyMeasurable : ∀ n, AEStronglyMeasurable (density n) (volume.restrict Ω)
  density_bound : ∀ n, ∀ᵐ w ∂(volume.restrict Ω), |density n w| ≤ densityBound
  density_tendsto : ∀ᵐ w ∂(volume.restrict Ω), Tendsto (fun n => density n w) atTop (𝓝 1)
  volume_dom : ∀ n, volume (dom n) = ENNReal.ofReal (∫ w in Ω, density n w)
  /-- The pulled-back Neumann forms `q_n[u,u]` and masses `m_n[u,u]`. -/
  formQ : ℕ → L2 Ω → ℝ
  formM : ℕ → L2 Ω → ℝ
  minmax : ∀ (j n : ℕ) (S : Submodule ℂ (L2 Ω)), Module.finrank ℂ S = j + 1 →
    (S : Set (L2 Ω)) ⊆ H1 Ω → neumannEigenvalue (dom n) j ≤
      ⨆ (u : L2 Ω) (_ : u ∈ S) (_ : ‖u‖ = 1), ENNReal.ofReal (formQ n u / formM n u)
  formQ_tendsto : ∀ S : Submodule ℂ (L2 Ω), FiniteDimensional ℂ S → (S : Set (L2 Ω)) ⊆ H1 Ω →
    TendstoUniformlyOn formQ (fun u => (neumannEnergy Ω u).toReal) atTop
      ((S : Set (L2 Ω)) ∩ Metric.sphere 0 1)
  formM_tendsto : ∀ S : Submodule ℂ (L2 Ω), FiniteDimensional ℂ S → (S : Set (L2 Ω)) ⊆ H1 Ω →
    TendstoUniformlyOn formM (fun _ => 1) atTop ((S : Set (L2 Ω)) ∩ Metric.sphere 0 1)
  limits : ∀ (j : ℕ) (φ : ℕ → ℕ), StrictMono φ → ∀ lam : ENNReal, lam < ⊤ →
    Tendsto (fun n => neumannEigenvalue (dom (φ n)) j) atTop (𝓝 lam) →
    ∃ u : Fin (j + 1) → L2 Ω, Orthonormal ℂ u ∧ ∀ a : Fin (j + 1) → ℂ,
      neumannEnergy Ω (∑ r, a r • u r) ≤ lam * ENNReal.ofReal (∑ r, ‖a r‖ ^ 2)

/-- External theorem BZ, Definition 10.8 and Lemmas 10.9–10.11, 10.14 and the compactness part
of Lemma 10.13: every bounded simply connected Lipschitz domain with a boundary parametrization
admits a smooth approximation with the properties of `SmoothApproximation`.
Proved from the Ball–Zarnescu data (`exists_ballZarnescu`) and the pulled-back forms
(`exists_pullbackForms`): after discarding finitely many indices, `Ω_n = f_n(Ω)`, the curves are
`γ_n = f_n ∘ γ` with monodromies equal to those of the boundary parametrizations of `Ω_n`
(`eventually_boundaryParam_ballZarnescu`, Lemma 10.3), the densities are `ρ_n = |det Df_n|`,
bounded by the square of the bi-Lipschitz constant and equal to `1` off the collars, and
`|Ω_n| = ∫_Ω ρ_n` by the change of variables formula (`volume_image_eq_lintegral`). -/
theorem exists_smoothApproximation {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) : Nonempty (SmoothApproximation Ω γ) := by
  obtain ⟨A⟩ := exists_ballZarnescu hb hL
  obtain ⟨formQ, hmin, hQ, hlim⟩ := exists_pullbackForms hb hL A
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_boundaryParam_ballZarnescu hb hL hγ A)
  choose γ' hγ' τ hτm hτL hτ0 hτ2 hτc using fun n => hN (n + N) (Nat.le_add_left N n)
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  have hΩo : IsOpen Ω := hL.1.1
  have hfr : ∀ θ, γ θ ∈ closure Ω := by
    intro θ
    have h1 : γ θ ∈ γ '' Set.Icc 0 (0 + 2 * π) := by
      rw [hγ.periodic.image_Icc Real.two_pi_pos]; exact Set.mem_range_self θ
    rw [zero_add, hγ.image] at h1
    exact frontier_subset_closure h1
  have hcl : ∀ n, LipschitzWith (A.lip * Kγ) (A.map (n + N) ∘ γ) := fun n =>
    lipschitzOnWith_univ.mp ((A.lipschitz (n + N)).comp (hKγ.lipschitzOnWith (s := Set.univ))
      fun θ _ => hfr θ)
  have hmeas : ∀ n, AEStronglyMeasurable (fun w => |(fderiv ℝ (A.map (n + N)) w).det|)
      volume := fun n =>
    ((continuous_abs.comp ContinuousLinearMap.continuous_det).measurable.comp
      (measurable_fderiv ℝ _)).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ w ∂(volume.restrict Ω),
      |(fderiv ℝ (A.map (n + N)) w).det| ≤ (A.lip : ℝ) ^ 2 := fun n =>
    ae_restrict_of_forall_mem hΩo.measurableSet fun w hw =>
      abs_det_fderiv_le hΩo ((A.lipschitz (n + N)).mono subset_closure) hw
  have hdt : ∀ᵐ w ∂(volume.restrict Ω),
      Tendsto (fun n => |(fderiv ℝ (A.map (n + N)) w).det|) atTop (𝓝 1) := by
    refine ae_restrict_of_forall_mem hΩo.measurableSet fun w hw => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(tendsto_add_atTop_nat N).eventually (A.collar_shrink w hw)] with n hn
    have hloc : (A.map (n + N) : ℂ → ℂ) =ᶠ[𝓝 w] id :=
      Filter.mem_of_superset ((A.collar_closed _).isOpen_compl.mem_nhds hn)
        fun x hx => A.eq_self _ x hx
    rw [hloc.fderiv_eq, fderiv_id, ContinuousLinearMap.det, ContinuousLinearMap.coe_id,
      LinearMap.det_id, abs_one]
  refine ⟨{
    dom := fun n => A.map (n + N) '' Ω
    dom_bounded := fun n => hb.subset (A.subset _)
    dom_smooth := fun n => A.smooth _
    dom_simplyConnected := fun n =>
      ((A.map (n + N)).image Ω).symm.toHomotopyEquiv.simplyConnectedSpace
    param := γ'
    param_isBoundaryParam := hγ'
    curve := fun n => A.map (n + N) ∘ γ
    curveLip := fun _ => A.lip * Kγ
    curve_lipschitz := hcl
    curve_closed := fun n => by simp [Function.comp, show γ (2 * π) = γ 0 by simpa using hγ.periodic 0]
    curve_tendsto := ?_
    curve_length := ⟨2 * π * (A.lip * Kγ), fun n => ?_⟩
    monodromy_eq := fun n E W W' hW hW' => ?_
    density := fun n w => |(fderiv ℝ (A.map (n + N)) w).det|
    densityBound := (A.lip : ℝ) ^ 2
    density_aestronglyMeasurable := fun n => (hmeas n).restrict
    density_bound := fun n => (hbound n).mono fun w hw => by rwa [abs_abs]
    density_tendsto := hdt
    volume_dom := fun n => ?_
    formQ := fun n => formQ (n + N)
    formM := fun n => weightedMass Ω (fun w => |(fderiv ℝ (A.map (n + N)) w).det|)
    minmax := fun j n S hS hH => hmin j (n + N) S hS hH
    formQ_tendsto := fun S hS hH => ?_
    formM_tendsto := fun S hS _ => tendstoUniformlyOn_weightedMass _ _ (fun n => (hmeas n).restrict)
      (fun n => (hbound n).mono fun w hw => by rwa [abs_abs]) hdt S hS
    limits := fun j φ hφ lam hlam h => hlim j (fun n => φ n + N)
      (fun a b hab => Nat.add_lt_add_right (hφ hab) N) lam hlam h }⟩
  case refine_1 =>
    have h := (A.tendsto.comp γ).mono (fun θ _ => hfr θ : Set.Icc 0 (2 * π) ⊆ γ ⁻¹' closure Ω)
    exact fun u hu => (tendsto_add_atTop_nat N).eventually (h u hu)
  case refine_2 =>
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
      (f := fun θ => ‖deriv (⇑(A.map (n + N)) ∘ γ) θ‖) (C := A.lip * Kγ) fun θ _ => by
        rw [norm_norm]; exact_mod_cast norm_deriv_le_of_lipschitz (hcl n)
    rw [sub_zero, abs_of_pos Real.two_pi_pos] at h
    exact (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; linarith)
  case refine_3 =>
    obtain ⟨Kτ, hKτ⟩ := hτL n
    obtain ⟨K', hK'⟩ := (hγ' n).lipschitz
    rw [← hτc n] at hW
    exact monodromy_comp hK' (hτm n) hKτ (hτ0 n) (hτ2 n) hW' hW
  case refine_4 =>
    have hlip := (A.lipschitz (n + N)).mono subset_closure
    rw [volume_image_eq_lintegral hΩo hlip (A.map (n + N)).injective.injOn,
      ofReal_integral_eq_lintegral_ofReal]
    · exact Measure.integrableOn_of_bounded hb.measure_lt_top.ne (hmeas n)
        ((hbound n).mono fun w hw => by rwa [Real.norm_eq_abs, abs_abs])
    · exact Eventually.of_forall fun _ => abs_nonneg _
  case refine_5 => exact fun u hu => (tendsto_add_atTop_nat N).eventually (hQ S hS hH u hu)

/-- Theorem 10.15 (quantitative Lipschitz eigenvalue inequality): for every bounded simply
connected Lipschitz domain and every `j ≥ 1`, `|Ω| μ_j + 2 ‖U_γ(μ_j) - I‖ ≤ 4π j`.
Proved, as in the paper, by applying Corollary 9.8 to the smooth approximations and passing to
the limit with Lemmas 10.12–10.14. -/
theorem lipschitz_quantitative {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) {γ : ℝ → ℂ}
    (hγ : IsBoundaryParam Ω γ) (j : ℕ) (hj : 1 ≤ j) (W : ℝ → Ell2 →L[ℂ] Ell2)
    (hW : IsTransport γ (neumannEigenvalue Ω j).toReal W) :
    volume Ω * neumannEigenvalue Ω j + ENNReal.ofReal (2 * ‖monodromy W - 1‖) ≤
      ENNReal.ofReal (4 * π * j) := by
  obtain ⟨A⟩ := exists_smoothApproximation hb hL hsc hγ
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  -- transports of the approximating curves at the approximating eigenvalues
  choose Ws hWs using fun n => transport_exists_of_lipschitz (A.curve n) (A.curve_lipschitz n)
    (neumannEigenvalue (A.dom n) j).toReal
  choose Ws' hWs' using fun n => transport_exists_of_lipschitz (A.param n)
    ((A.param_isBoundaryParam n).lipschitz.choose_spec) (neumannEigenvalue (A.dom n) j).toReal
  -- Corollary 9.8 on each smooth domain
  have hsmooth : ∀ n, volume (A.dom n) * neumannEigenvalue (A.dom n) j +
      ENNReal.ofReal (2 * ‖monodromy (Ws n) - 1‖) ≤ ENNReal.ofReal (4 * π * j) := by
    intro n
    rw [A.monodromy_eq n _ _ _ (hWs n) (hWs' n)]
    exact smooth_eigen (A.dom_bounded n) (A.dom_smooth n) (A.dom_simplyConnected n)
      (A.param_isBoundaryParam n) j hj (Ws' n) (hWs' n)
  -- Lemma 10.13: convergence of area and eigenvalues
  have hvolfin : volume Ω ≠ ⊤ := hb.measure_lt_top.ne
  have hvol := tendsto_volume_of_density hvolfin A.dom A.density A.densityBound
    A.density_aestronglyMeasurable A.density_bound A.density_tendsto A.volume_dom
  have hμ := tendsto_neumannEigenvalue j (fun n => neumannEigenvalue (A.dom n) j) A.formQ A.formM
    (A.minmax j) (fun S hS hH => A.formQ_tendsto S (Module.finite_of_finrank_eq_succ hS) hH)
    (fun S hS hH => A.formM_tendsto S (Module.finite_of_finrank_eq_succ hS) hH) (A.limits j)
  -- Lemma 10.14 and the limit
  exact lipschitz_quantitative_of_approximation A.dom j hK A.curve_lipschitz hclosed
    A.curve_closed A.curve_tendsto A.curve_length hW hWs hsmooth hvolfin
    (neumannEigenvalue_lt_top hL j).ne hvol hμ

/-- **Theorem 10.16 (strict Neumann Pólya inequality).** For every bounded simply connected
Lipschitz domain `Ω ⊂ ℝ²` and every integer `j ≥ 1`, `|Ω| μ_j(Ω) < 4π j`. -/
theorem strict_neumann_polya (Ω : Set ℂ) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) (j : ℕ) (hj : 1 ≤ j) :
    volume Ω * neumannEigenvalue Ω j < ENNReal.ofReal (4 * π * j) := by
  have hfin := (neumannEigenvalue_lt_top hL j).ne
  have hE : 0 < (neumannEigenvalue Ω j).toReal :=
    ENNReal.toReal_pos (neumannEigenvalue_pos hb hL j hj).ne' hfin
  obtain ⟨γ, hγ⟩ := exists_boundaryParam hb hL hsc
  obtain ⟨W, hW, -⟩ := transport_exists_unique hγ (neumannEigenvalue Ω j).toReal
  have hq := lipschitz_quantitative hb hL hsc hγ j hj W hW
  have hU := norm_sub_one_pos (monodromy_ne_one hb hL hγ _ hE W hW)
  have hpos : ENNReal.ofReal (2 * ‖monodromy W - 1‖) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hfin' : volume Ω * neumannEigenvalue Ω j ≠ ⊤ :=
    ENNReal.mul_ne_top hb.measure_lt_top.ne hfin
  exact lt_of_lt_of_le (ENNReal.lt_add_right hfin' hpos) hq

/-- **Theorem 10.16, counting form.** For every bounded simply connected Lipschitz domain
and every `E > 0`, `N_N(E) > |Ω| E / (4π)`. -/
theorem strict_neumann_polya_count (Ω : Set ℂ) (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) (E : ℝ) (hE : 0 < E) :
    volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) <
      (neumannCount Ω (ENNReal.ofReal E) : ENNReal) :=
  (eigen_iff_count hb hL).mp (strict_neumann_polya Ω hb hL hsc) E hE

end PolyaNeumann

/-!
Stable top-level entry points for automated audits and downstream users.
The original namespaced declarations above remain the canonical proof
statements; these aliases provide the same compact API as the companion
Dirichlet formalization.
-/

theorem main (Ω : Set ℂ) (hb : Bornology.IsBounded Ω)
    (hL : PolyaNeumann.IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) (j : ℕ)
    (hj : 1 ≤ j) :
    volume Ω * PolyaNeumann.neumannEigenvalue Ω j < ENNReal.ofReal (4 * π * j) :=
  PolyaNeumann.strict_neumann_polya Ω hb hL hsc j hj

theorem main_counting (Ω : Set ℂ) (hb : Bornology.IsBounded Ω)
    (hL : PolyaNeumann.IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) (E : ℝ)
    (hE : 0 < E) :
    volume Ω * ENNReal.ofReal E / ENNReal.ofReal (4 * π) <
      (PolyaNeumann.neumannCount Ω (ENNReal.ofReal E) : ENNReal) :=
  PolyaNeumann.strict_neumann_polya_count Ω hb hL hsc E hE

end
