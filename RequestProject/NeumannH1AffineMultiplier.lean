module

public import RequestProject.NeumannSobolev
public import RequestProject.LpBoundedMultiplier
public import RequestProject.ReconBasic

/-!
# Affine multiplication in the actual weak-gradient H¹ space

Multiplication by `z-p` is constructed from the genuine L² multiplier and
the weak product rule. Testing against `(z-p)φ` proves gradient membership
for arbitrary H¹ inputs. A supplied physical bound gives an explicit H¹
operator norm; boundedness of the domain supplies such a bound at every p.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real Filter
open scoped ComplexConjugate InnerProductSpace Topology

/-- A pointwise affine bound gives an essential bound on the actual restricted
measure. Restriction monotonicity avoids a measurability assumption on Ω. -/
theorem neumannAffine_ae_bound {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) :
    ∀ᵐ z ∂volume.restrict Ω, ‖z - p‖ ≤ B := by
  have hsub : Ω ⊆ closedBall p B := by
    intro z hz
    simpa only [mem_closedBall, dist_eq_norm] using hB z hz
  apply ae_restrict_of_ae_restrict_of_subset hsub
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
  simpa only [mem_closedBall, dist_eq_norm] using hz

/-- The actual affine coefficient multiplier in physical L². -/
def neumannAffineL2Multiplier {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) : L2 Ω →L[ℂ] L2 Ω :=
  lpBoundedMultiplier (fun z : ℂ => z - p)
    (continuous_id.sub continuous_const).aestronglyMeasurable
    (neumannAffine_ae_bound p hB)

theorem neumannAffineL2Multiplier_ae {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) (u : L2 Ω) :
    (neumannAffineL2Multiplier p hB u : ℂ → ℂ) =ᵐ[volume.restrict Ω]
      fun z => (z - p) * u z :=
  lpBoundedMultiplier_ae (fun z : ℂ => z - p)
    (continuous_id.sub continuous_const).aestronglyMeasurable
    (neumannAffine_ae_bound p hB) u

theorem norm_neumannAffineL2Multiplier_apply_le {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) (u : L2 Ω) :
    ‖neumannAffineL2Multiplier p hB u‖ ≤ B * ‖u‖ :=
  norm_lpBoundedMulLin_le (fun z : ℂ => z - p)
    (continuous_id.sub continuous_const).aestronglyMeasurable
    (neumannAffine_ae_bound p hB) u

private theorem affine_test_mul {Ω : Set ℂ} {φ : ℂ → ℂ}
    (hφ : TestFunction Ω φ) (p : ℂ) :
    TestFunction Ω (fun z => (z - p) * φ z) :=
  ⟨(contDiff_id.sub contDiff_const).mul hφ.1, hφ.2.1.mul_left,
    tsupport_mul_subset_right.trans hφ.2.2⟩

private theorem affine_test_mul_fderiv {Ω : Set ℂ} {φ : ℂ → ℂ}
    (hφ : TestFunction Ω φ) (p z : ℂ) (i : Fin 2) :
    fderiv ℝ (fun w => (w - p) * φ w) z (coordDir i) =
      coordDir i * φ z + (z - p) * fderiv ℝ φ z (coordDir i) := by
  have hd : HasFDerivAt (fun w : ℂ => (w - p) * φ w)
      ((z - p) • fderiv ℝ φ z + φ z • ContinuousLinearMap.id ℝ ℂ) z :=
    ((hasFDerivAt_id z).sub_const p).mul
      (hφ.1.differentiable (by simp) z).hasFDerivAt
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  ring

/-- The affine weak product rule follows from the original weak-gradient
identity tested against the actual compactly supported affine product. -/
theorem isWeakGradient_neumannAffineL2Multiplier {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) {u : L2 Ω} {g : Fin 2 → L2 Ω}
    (hu : IsWeakGradient Ω u g) :
    IsWeakGradient Ω (neumannAffineL2Multiplier p hB u)
      (fun i => neumannAffineL2Multiplier p hB (g i) + coordDir i • u) := by
  intro φ hφ i
  have hweak := hu (fun z => (z - p) * φ z) (affine_test_mul hφ p) i
  have hiu : Integrable (fun z => u z * φ z) (volume.restrict Ω) :=
    (Lp.memLp u).integrable_mul hφ.memLp
  have hif : Integrable (fun z => neumannAffineL2Multiplier p hB u z *
      fderiv ℝ φ z (coordDir i)) (volume.restrict Ω) :=
    (Lp.memLp (neumannAffineL2Multiplier p hB u)).integrable_mul
      (hφ.memLp_fderiv (coordDir i))
  have hig : Integrable (fun z => neumannAffineL2Multiplier p hB (g i) z * φ z)
      (volume.restrict Ω) :=
    (Lp.memLp (neumannAffineL2Multiplier p hB (g i))).integrable_mul hφ.memLp
  have hleft :
      (∫ z in Ω, u z * fderiv ℝ (fun w => (w - p) * φ w) z (coordDir i)) =
        coordDir i * (∫ z in Ω, u z * φ z) +
          ∫ z in Ω, neumannAffineL2Multiplier p hB u z * fderiv ℝ φ z (coordDir i) := by
    calc
      _ = ∫ z in Ω, coordDir i * (u z * φ z) +
          neumannAffineL2Multiplier p hB u z * fderiv ℝ φ z (coordDir i) := by
        apply integral_congr_ae
        filter_upwards [neumannAffineL2Multiplier_ae p hB u] with z hz
        rw [affine_test_mul_fderiv hφ p z i, hz]
        ring
      _ = _ := by rw [integral_add (hiu.const_mul _) hif, integral_const_mul]
  have hright : (∫ z in Ω, (g i) z * ((z - p) * φ z)) =
      ∫ z in Ω, neumannAffineL2Multiplier p hB (g i) z * φ z := by
    apply integral_congr_ae
    filter_upwards [neumannAffineL2Multiplier_ae p hB (g i)] with z hz
    rw [hz]
    ring
  have hout :
      (∫ z in Ω, ((neumannAffineL2Multiplier p hB (g i) + coordDir i • u : L2 Ω) :
          ℂ → ℂ) z * φ z) =
        (∫ z in Ω, neumannAffineL2Multiplier p hB (g i) z * φ z) +
          coordDir i * ∫ z in Ω, u z * φ z := by
    calc
      _ = ∫ z in Ω, neumannAffineL2Multiplier p hB (g i) z * φ z +
          coordDir i * (u z * φ z) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (neumannAffineL2Multiplier p hB (g i))
            (coordDir i • u), Lp.coeFn_smul (coordDir i) u] with z hadd hsmul
        rw [hadd]
        simp only [Pi.add_apply]
        rw [hsmul]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = _ := by rw [integral_add hig (hiu.const_mul _), integral_const_mul]
  rw [hleft, hright] at hweak
  rw [hout]
  linear_combination hweak

private theorem affine_h1_ext {Ω : Set ℂ} {u v : NeumannH1 Ω}
    (hv : h1Value Ω u = h1Value Ω v)
    (hg : ∀ i : Fin 2, h1Gradient Ω i u = h1Gradient Ω i v) : u = v := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hv
  · exact hg j

def affineH1Vector {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) (u : NeumannH1 Ω) : NeumannH1 Ω :=
  h1Vector (isWeakGradient_neumannAffineL2Multiplier p hB (h1Value_weakGradient Ω u))

private theorem affineH1Vector_value {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) (u : NeumannH1 Ω) :
    h1Value Ω (affineH1Vector p hB u) = neumannAffineL2Multiplier p hB (h1Value Ω u) :=
  h1Value_h1Vector
    (isWeakGradient_neumannAffineL2Multiplier p hB (h1Value_weakGradient Ω u))

private theorem affineH1Vector_gradient {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) (u : NeumannH1 Ω) (i : Fin 2) :
    h1Gradient Ω i (affineH1Vector p hB u) =
      neumannAffineL2Multiplier p hB (h1Gradient Ω i u) + coordDir i • h1Value Ω u :=
  h1Gradient_h1Vector
    (isWeakGradient_neumannAffineL2Multiplier p hB (h1Value_weakGradient Ω u)) i

def affineH1Lin {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) : NeumannH1 Ω →ₗ[ℂ] NeumannH1 Ω where
  toFun := affineH1Vector p hB
  map_add' u v := by
    apply affine_h1_ext
    · simp only [affineH1Vector_value, map_add]
    · intro i
      simp only [affineH1Vector_gradient, map_add, smul_add]
      abel
  map_smul' c u := by
    apply affine_h1_ext
    · simp only [affineH1Vector_value, map_smul, RingHom.id_apply]
    · intro i
      simp only [affineH1Vector_gradient, map_smul, smul_add, RingHom.id_apply]
      rw [smul_comm]

private theorem affineH1Lin_value {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) (u : NeumannH1 Ω) :
    h1Value Ω (affineH1Lin p hB u) = neumannAffineL2Multiplier p hB (h1Value Ω u) :=
  affineH1Vector_value p hB u

private theorem affineH1Lin_gradient {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) (u : NeumannH1 Ω) (i : Fin 2) :
    h1Gradient Ω i (affineH1Lin p hB u) =
      neumannAffineL2Multiplier p hB (h1Gradient Ω i u) + coordDir i • h1Value Ω u :=
  affineH1Vector_gradient p hB u i

private theorem affine_real_component_bounds {r a b c : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : r ^ 2 = a ^ 2 + (b ^ 2 + c ^ 2)) :
    a ≤ r ∧ b ≤ r ∧ c ≤ r := by
  constructor
  · apply (sq_le_sq₀ ha hr).mp
    nlinarith [sq_nonneg b, sq_nonneg c]
  constructor
  · apply (sq_le_sq₀ hb hr).mp
    nlinarith [sq_nonneg a, sq_nonneg c]
  · apply (sq_le_sq₀ hc hr).mp
    nlinarith [sq_nonneg a, sq_nonneg b]

private theorem affine_h1_component_norm_le {Ω : Set ℂ} (u : NeumannH1 Ω) :
    ‖h1Value Ω u‖ ≤ ‖u‖ ∧ ‖h1Gradient Ω 0 u‖ ≤ ‖u‖ ∧
      ‖h1Gradient Ω 1 u‖ ≤ ‖u‖ := by
  have hs := h1_norm_sq Ω u
  rw [Fin.sum_univ_two] at hs
  exact affine_real_component_bounds (norm_nonneg u) (norm_nonneg (h1Value Ω u))
    (norm_nonneg (h1Gradient Ω 0 u)) (norm_nonneg (h1Gradient Ω 1 u)) hs

private theorem affine_h1_value_norm_le {Ω : Set ℂ} (u : NeumannH1 Ω) :
    ‖h1Value Ω u‖ ≤ ‖u‖ := (affine_h1_component_norm_le u).1

private theorem affine_h1_gradient_norm_le {Ω : Set ℂ} (u : NeumannH1 Ω) (i : Fin 2) :
    ‖h1Gradient Ω i u‖ ≤ ‖u‖ := by
  fin_cases i
  · exact (affine_h1_component_norm_le u).2.1
  · exact (affine_h1_component_norm_le u).2.2

private theorem affine_real_three_component_norm_le {r a b c A : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hA : 0 ≤ A)
    (hs : r ^ 2 = a ^ 2 + (b ^ 2 + c ^ 2))
    (hva : a ≤ A) (hvb : b ≤ A) (hvc : c ≤ A) :
    r ≤ Real.sqrt 3 * A := by
  have hsa : a ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ ha hva 2
  have hsb : b ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hb hvb 2
  have hsc : c ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hc hvc 2
  apply (sq_le_sq₀ hr (mul_nonneg (Real.sqrt_nonneg _) hA)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  nlinarith

private theorem affine_h1_norm_le_of_components {Ω : Set ℂ} (u : NeumannH1 Ω)
    {A : ℝ} (hA : 0 ≤ A) (hv : ‖h1Value Ω u‖ ≤ A)
    (hg : ∀ i : Fin 2, ‖h1Gradient Ω i u‖ ≤ A) :
    ‖u‖ ≤ Real.sqrt 3 * A := by
  have hs := h1_norm_sq Ω u
  rw [Fin.sum_univ_two] at hs
  exact affine_real_three_component_norm_le (norm_nonneg u) (norm_nonneg (h1Value Ω u))
    (norm_nonneg (h1Gradient Ω 0 u)) (norm_nonneg (h1Gradient Ω 1 u)) hA hs hv (hg 0) (hg 1)

private theorem affine_real_value_norm_bound {a v N B : ℝ}
    (hB : 0 ≤ B) (hN : 0 ≤ N) (ha : a ≤ B * v) (hv : v ≤ N) :
    a ≤ (B + 1) * N := by
  calc
    a ≤ B * v := ha
    _ ≤ B * N := mul_le_mul_of_nonneg_left hv hB
    _ ≤ (B + 1) * N := by nlinarith

private theorem affine_gradient_norm_bound {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (L : V →L[ℂ] V) (a v : V) (q : ℂ) {B N : ℝ}
    (hB : 0 ≤ B) (hL : ‖L a‖ ≤ B * ‖a‖)
    (ha : ‖a‖ ≤ N) (hv : ‖v‖ ≤ N) (hq : ‖q‖ = 1) :
    ‖L a + q • v‖ ≤ (B + 1) * N := by
  calc
    _ ≤ ‖L a‖ + ‖q • v‖ := norm_add_le _ _
    _ = ‖L a‖ + ‖v‖ := by rw [norm_smul, hq, one_mul]
    _ ≤ B * ‖a‖ + ‖v‖ := add_le_add hL le_rfl
    _ ≤ B * N + N := add_le_add (mul_le_mul_of_nonneg_left ha hB) hv
    _ = (B + 1) * N := by ring

theorem affineH1Lin_norm_le {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) (u : NeumannH1 Ω) :
    ‖affineH1Lin p hB u‖ ≤ (Real.sqrt 3 * (B + 1)) * ‖u‖ := by
  have hv : ‖h1Value Ω (affineH1Lin p hB u)‖ ≤ (B + 1) * ‖u‖ := by
    rw [affineH1Lin_value]
    exact affine_real_value_norm_bound hB0 (norm_nonneg u)
      (norm_neumannAffineL2Multiplier_apply_le p hB (h1Value Ω u))
      (affine_h1_value_norm_le u)
  have hg (i : Fin 2) : ‖h1Gradient Ω i (affineH1Lin p hB u)‖ ≤ (B + 1) * ‖u‖ := by
    rw [affineH1Lin_gradient]
    exact affine_gradient_norm_bound (V := L2 Ω) (neumannAffineL2Multiplier p hB)
      (h1Gradient Ω i u) (h1Value Ω u) (coordDir i) hB0
      (norm_neumannAffineL2Multiplier_apply_le p hB (h1Gradient Ω i u))
      (affine_h1_gradient_norm_le u i) (affine_h1_value_norm_le u) (norm_coordDir i)
  have hA : 0 ≤ (B + 1) * ‖u‖ :=
    mul_nonneg (by linarith) (norm_nonneg u)
  have h := affine_h1_norm_le_of_components (affineH1Lin p hB u)
    hA hv hg
  simpa only [mul_assoc] using h

/-- Affine multiplication in genuine H¹ from a specified physical bound. -/
def neumannH1AffineMultiplierOfBound {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) : NeumannH1 Ω →L[ℂ] NeumannH1 Ω := by
  exact (affineH1Lin p hB).mkContinuous (Real.sqrt 3 * (B + 1))
    (affineH1Lin_norm_le p hB0 hB)

theorem neumannH1AffineMultiplierOfBound_apply {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) (u : NeumannH1 Ω) :
    neumannH1AffineMultiplierOfBound p hB0 hB u = affineH1Lin p hB u := rfl

theorem h1Value_neumannH1AffineMultiplierOfBound {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) (u : NeumannH1 Ω) :
    h1Value Ω (neumannH1AffineMultiplierOfBound p hB0 hB u) =
      neumannAffineL2Multiplier p hB (h1Value Ω u) := by
  rw [neumannH1AffineMultiplierOfBound_apply]
  exact affineH1Lin_value p hB u

theorem h1Gradient_neumannH1AffineMultiplierOfBound {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) (u : NeumannH1 Ω) (i : Fin 2) :
    h1Gradient Ω i (neumannH1AffineMultiplierOfBound p hB0 hB u) =
      neumannAffineL2Multiplier p hB (h1Gradient Ω i u) + coordDir i • h1Value Ω u := by
  rw [neumannH1AffineMultiplierOfBound_apply]
  exact affineH1Lin_gradient p hB u i

theorem norm_neumannH1AffineMultiplierOfBound_apply_le {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) (u : NeumannH1 Ω) :
    ‖neumannH1AffineMultiplierOfBound p hB0 hB u‖ ≤ (Real.sqrt 3 * (B + 1)) * ‖u‖ := by
  rw [neumannH1AffineMultiplierOfBound_apply]
  exact affineH1Lin_norm_le p hB0 hB u

theorem norm_neumannH1AffineMultiplierOfBound_le {Ω : Set ℂ} (p : ℂ) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ z ∈ Ω, ‖z - p‖ ≤ B) :
    ‖neumannH1AffineMultiplierOfBound p hB0 hB‖ ≤ Real.sqrt 3 * (B + 1) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact norm_neumannH1AffineMultiplierOfBound_apply_le p hB0 hB

/-- Every bounded actual domain has a genuine affine coefficient bound. -/
theorem exists_neumannAffine_bound {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (p : ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ Ω, ‖z - p‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := hb.subset_ball_lt 0 p
  refine ⟨B, hB0.le, fun z hz => ?_⟩
  have h : ‖z - p‖ < B := by
    simpa only [mem_ball, dist_eq_norm] using hB hz
  exact h.le

def neumannH1AffineBound {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (p : ℂ) : ℝ :=
  Classical.choose (exists_neumannAffine_bound hb p)

theorem neumannH1AffineBound_nonneg {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (p : ℂ) :
    0 ≤ neumannH1AffineBound hb p := (Classical.choose_spec (exists_neumannAffine_bound hb p)).1

theorem neumannH1AffineBound_spec {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (p : ℂ) :
    ∀ z ∈ Ω, ‖z - p‖ ≤ neumannH1AffineBound hb p :=
  (Classical.choose_spec (exists_neumannAffine_bound hb p)).2

/-- Multiplication by `z-p` on the actual H¹ space of any bounded domain. -/
def neumannH1AffineMultiplier {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (p : ℂ) :
    NeumannH1 Ω →L[ℂ] NeumannH1 Ω :=
  neumannH1AffineMultiplierOfBound p (neumannH1AffineBound_nonneg hb p)
    (neumannH1AffineBound_spec hb p)

theorem h1Value_neumannH1AffineMultiplier {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (u : NeumannH1 Ω) :
    h1Value Ω (neumannH1AffineMultiplier hb p u) =
      neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) (h1Value Ω u) :=
  h1Value_neumannH1AffineMultiplierOfBound p (neumannH1AffineBound_nonneg hb p)
    (neumannH1AffineBound_spec hb p) u

theorem h1Value_neumannH1AffineMultiplier_ae {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (u : NeumannH1 Ω) :
    (h1Value Ω (neumannH1AffineMultiplier hb p u) : ℂ → ℂ) =ᵐ[volume.restrict Ω]
      fun z => (z - p) * (h1Value Ω u : ℂ → ℂ) z := by
  rw [h1Value_neumannH1AffineMultiplier]
  exact neumannAffineL2Multiplier_ae p (neumannH1AffineBound_spec hb p) (h1Value Ω u)

theorem h1Gradient_neumannH1AffineMultiplier {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (u : NeumannH1 Ω) (i : Fin 2) :
    h1Gradient Ω i (neumannH1AffineMultiplier hb p u) =
      neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) (h1Gradient Ω i u) +
        coordDir i • h1Value Ω u :=
  h1Gradient_neumannH1AffineMultiplierOfBound p (neumannH1AffineBound_nonneg hb p)
    (neumannH1AffineBound_spec hb p) u i

theorem h1Gradient_neumannH1AffineMultiplier_x {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (u : NeumannH1 Ω) :
    h1Gradient Ω 0 (neumannH1AffineMultiplier hb p u) =
      neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) (h1Gradient Ω 0 u) +
        h1Value Ω u := by
  simpa only [show coordDir 0 = (1 : ℂ) from rfl, one_smul] using
    h1Gradient_neumannH1AffineMultiplier hb p u 0

theorem h1Gradient_neumannH1AffineMultiplier_y {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (u : NeumannH1 Ω) :
    h1Gradient Ω 1 (neumannH1AffineMultiplier hb p u) =
      neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) (h1Gradient Ω 1 u) +
        Complex.I • h1Value Ω u := by
  simpa only [show coordDir 1 = Complex.I from rfl] using
    h1Gradient_neumannH1AffineMultiplier hb p u 1

theorem h1Gradient_neumannH1AffineMultiplier_ae {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (u : NeumannH1 Ω) (i : Fin 2) :
    (h1Gradient Ω i (neumannH1AffineMultiplier hb p u) : ℂ → ℂ) =ᵐ[volume.restrict Ω]
      fun z => (z - p) * (h1Gradient Ω i u : ℂ → ℂ) z +
        coordDir i * (h1Value Ω u : ℂ → ℂ) z := by
  rw [h1Gradient_neumannH1AffineMultiplier]
  filter_upwards [Lp.coeFn_add
      (neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) (h1Gradient Ω i u))
      (coordDir i • h1Value Ω u),
    neumannAffineL2Multiplier_ae p (neumannH1AffineBound_spec hb p) (h1Gradient Ω i u),
    Lp.coeFn_smul (coordDir i) (h1Value Ω u)] with z hadd hmul hsmul
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hmul, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]

theorem norm_neumannH1AffineMultiplier_apply_le {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (p : ℂ) (u : NeumannH1 Ω) :
    ‖neumannH1AffineMultiplier hb p u‖ ≤
      (Real.sqrt 3 * (neumannH1AffineBound hb p + 1)) * ‖u‖ :=
  norm_neumannH1AffineMultiplierOfBound_apply_le p (neumannH1AffineBound_nonneg hb p)
    (neumannH1AffineBound_spec hb p) u

theorem norm_neumannH1AffineMultiplier_le {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (p : ℂ) :
    ‖neumannH1AffineMultiplier hb p‖ ≤ Real.sqrt 3 * (neumannH1AffineBound hb p + 1) :=
  norm_neumannH1AffineMultiplierOfBound_le p (neumannH1AffineBound_nonneg hb p)
    (neumannH1AffineBound_spec hb p)

end PolyaNeumann
