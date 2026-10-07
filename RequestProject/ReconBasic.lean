module

public import RequestProject.FixedSpace
public import RequestProject.ChainRule
public import RequestProject.WeakCompact
public import RequestProject.GreenWinding

/-!
# Basic notions for the Cauchy reconstruction (Lemma 4.8)

* `lap φ` : the Laplacian `∂ₓ² φ + ∂ᵧ² φ` written with real Fréchet derivatives;
* `dbar F` : the Wirtinger derivative `∂̄F = (∂ₓF + i ∂ᵧF)/2`;
* `ePlane ξ` : the Fourier character `z ↦ e^{-2πi⟨z, ξ⟩}`;
* `doubleLayer γ h φ` : the double-layer pairing `∫₀^{2π} h(θ) Dφ(γ(θ))(-iγ'(θ)) dθ`;
* `IsWeakGradOn D w g` : `g` is a weak gradient of `w` on the open set `D`, tested against
  smooth compactly supported functions with support in `D` (integrals over `ℂ`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

/-- The directional derivative `z ↦ Dφ(z) v`. -/
def dirD (φ : ℂ → ℂ) (v : ℂ) : ℂ → ℂ := fun z => fderiv ℝ φ z v

/-- The Laplacian `∂ₓ²φ + ∂ᵧ²φ`. -/
def lap (φ : ℂ → ℂ) : ℂ → ℂ := fun z => dirD (dirD φ 1) 1 z + dirD (dirD φ Complex.I) Complex.I z

/-- The Wirtinger derivative `∂̄F = (∂ₓF + i ∂ᵧF)/2`. -/
def dbar (F : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ F z 1 + Complex.I * fderiv ℝ F z Complex.I) / 2

/-- The Fourier character `z ↦ e^{-2πi⟨z, ξ⟩}` (with `⟨z, ξ⟩ = Re(conj z · ξ)`). -/
def ePlane (ξ z : ℂ) : ℂ := Complex.exp (-(2 * π * Complex.I) * ((conj z * ξ).re : ℂ))

/-- The double-layer pairing `μ_h(φ) = ∫₀^{2π} h(θ) Dφ(γ(θ))(-iγ'(θ)) dθ` of a boundary density
`h` (in the parameter `θ`) with a smooth function `φ`. -/
def doubleLayer (γ h : ℝ → ℂ) (φ : ℂ → ℂ) : ℂ :=
  ∫ θ in (0 : ℝ)..(2 * π), h θ * fderiv ℝ φ (γ θ) (-(Complex.I * deriv γ θ))

/-- `g` is a weak gradient of `w` on `D`: `∫ w ∂ᵢφ = -∫ gᵢ φ` for every smooth compactly
supported `φ` with support in `D`. -/
def IsWeakGradOn (D : Set ℂ) (w : ℂ → ℂ) (g : Fin 2 → ℂ → ℂ) : Prop :=
  ∀ φ : ℂ → ℂ, TestFunction D φ → ∀ i : Fin 2,
    ∫ z, w z * fderiv ℝ φ z (coordDir i) = -∫ z, g i z * φ z

/-! ### Test functions -/

/-- A smooth compactly supported function is in every `Lᵖ`. -/
lemma TestFunction.memLp' {D : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction D φ) (p : ENNReal)
    {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ] : MemLp φ p μ :=
  (hφ.1.continuous).memLp_of_hasCompactSupport hφ.2.1

lemma TestFunction.mono {D D' : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction D φ) (h : D ⊆ D') :
    TestFunction D' φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans h⟩

lemma TestFunction.univ' {D : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction D φ) :
    TestFunction univ φ := hφ.mono (subset_univ _)

/-- Directional derivatives of test functions are test functions. -/
lemma TestFunction.dirD {D : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction D φ) (v : ℂ) :
    TestFunction D (dirD φ v) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (hφ.1.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).clm_apply contDiff_const
  · exact hφ.2.1.fderiv_apply (𝕜 := ℝ) v
  · exact (tsupport_fderiv_apply_subset ℝ v).trans hφ.2.2

lemma TestFunction.add {D : Set ℂ} {φ ψ : ℂ → ℂ} (hφ : TestFunction D φ)
    (hψ : TestFunction D ψ) : TestFunction D (fun z => φ z + ψ z) :=
  ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, (tsupport_add φ ψ).trans (union_subset hφ.2.2 hψ.2.2)⟩

lemma TestFunction.const_mul {D : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction D φ) (c : ℂ) :
    TestFunction D (fun z => c * φ z) :=
  ⟨contDiff_const.mul hφ.1, hφ.2.1.mul_left, (tsupport_mul_subset_right).trans hφ.2.2⟩

/-- The Laplacian of a test function is a test function. -/
lemma TestFunction.lap {D : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction D φ) :
    TestFunction D (lap φ) :=
  ((hφ.dirD 1).dirD 1).add ((hφ.dirD Complex.I).dirD Complex.I)

/-- `Δφ + Eφ` is a test function. -/
lemma TestFunction.helm {D : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction D φ) (E : ℝ) :
    TestFunction D (fun z => PolyaNeumann.lap φ z + E * φ z) :=
  hφ.lap.add (hφ.const_mul _)

/-- Complex conjugates of test functions are test functions. -/
lemma TestFunction.conj {D : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction D φ) :
    TestFunction D (fun z => conj (φ z)) := by
  refine ⟨Complex.conjCLE.contDiff.comp hφ.1, hφ.2.1.comp_left (by simp), ?_⟩
  exact (tsupport_comp_subset (g := fun z : ℂ => conj z) (by simp) φ).trans hφ.2.2

lemma dirD_conj {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (v z : ℂ) :
    dirD (fun z => conj (φ z)) v z = conj (dirD φ v z) := by
  unfold dirD
  have := (Complex.conjCLE.hasFDerivAt.comp z
    ((hφ.differentiable one_ne_zero) z).hasFDerivAt).fderiv
  rw [show (fun z => conj (φ z)) = Complex.conjCLE ∘ φ from rfl, this]
  rfl

/-- `L²` functions times test functions are integrable. -/
lemma integrable_mul_test {u : ℂ → ℂ} {μ : Measure ℂ} [IsFiniteMeasureOnCompacts μ]
    (hu : MemLp u 2 μ) {D : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction D φ) :
    Integrable (fun z => u z * φ z) μ :=
  hu.integrable_mul (hφ.memLp' 2)

/-- Fundamental lemma of the calculus of variations on an open set, for complex functions. -/
lemma ae_eq_zero_of_integral_mul_test {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : LocallyIntegrable f volume)
    (h : ∀ φ : ℂ → ℂ, TestFunction U φ → ∫ z, f z * φ z = 0) :
    ∀ᵐ z ∂(volume.restrict U), f z = 0 := by
  have h0 := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.locallyIntegrableOn U)
    (fun ψ hψ hψc hψs => by
      have ht : TestFunction U (fun w => ((ψ w : ℝ) : ℂ)) :=
        ⟨Complex.ofRealCLM.contDiff.comp hψ, hψc.comp_left Complex.ofReal_zero,
          (tsupport_comp_subset Complex.ofReal_zero ψ).trans hψs⟩
      have e := h _ ht
      simp_rw [Complex.real_smul, mul_comm]
      exact e)
  exact (ae_restrict_iff' hU.measurableSet).mpr h0

/-- A product of bounded Lipschitz functions is Lipschitz. -/
lemma lipschitzWith_mul_of_bounded {f g : ℂ → ℂ} {Kf Kg : NNReal} (hf : LipschitzWith Kf f)
    (hg : LipschitzWith Kg g) {Cf Cg : ℝ} (hCf : ∀ z, ‖f z‖ ≤ Cf) (hCg : ∀ z, ‖g z‖ ≤ Cg) :
    ∃ K : NNReal, LipschitzWith K (fun z => f z * g z) := by
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf 0)
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg 0)
  refine ⟨⟨Cf * Kg + Cg * Kf, by positivity⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [dist_eq_norm, dist_eq_norm]
  change _ ≤ (Cf * Kg + Cg * Kf) * _
  have e : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  rw [e]
  calc ‖f x * (g x - g y) + g y * (f x - f y)‖
      ≤ ‖f x‖ * ‖g x - g y‖ + ‖g y‖ * ‖f x - f y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ Cf * (Kg * ‖x - y‖) + Cg * (Kf * ‖x - y‖) := by
        have h1 := hg.dist_le_mul x y
        have h2 := hf.dist_le_mul x y
        rw [dist_eq_norm, dist_eq_norm] at h1 h2
        gcongr
        · exact hCf x
        · exact hCg y
    _ = (Cf * Kg + Cg * Kf) * ‖x - y‖ := by ring

end PolyaNeumann
