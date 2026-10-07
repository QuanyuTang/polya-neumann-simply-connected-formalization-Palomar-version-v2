module

public import RequestProject.NeumannH1AffineMultiplier
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Tactic.Module

/-!
# Genuine weak Wirtinger identities for the physical Vekua series

All derivatives below are the components of the actual weak-gradient H¹
space. The second-order identity is obtained by testing those weak gradients
twice and commuting derivatives of compact smooth tests. In particular no
weak Laplacian, smoothness of the H¹ input, or boundary condition is assumed.

This module is part of the verified dependency chain.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set
open scoped ComplexConjugate InnerProductSpace

/-- The genuine weak derivative `(∂x - i∂y)/2`. -/
def h1WirtingerD (Ω : Set ℂ) : NeumannH1 Ω →L[ℂ] L2 Ω :=
  (1 / 2 : ℂ) • (h1Gradient Ω 0 - Complex.I • h1Gradient Ω 1)

/-- The genuine weak derivative `(∂x + i∂y)/2`. -/
def h1WirtingerDbar (Ω : Set ℂ) : NeumannH1 Ω →L[ℂ] L2 Ω :=
  (1 / 2 : ℂ) • (h1Gradient Ω 0 + Complex.I • h1Gradient Ω 1)

theorem h1WirtingerD_apply (Ω : Set ℂ) (u : NeumannH1 Ω) :
    h1WirtingerD Ω u =
      (1 / 2 : ℂ) • (h1Gradient Ω 0 u - Complex.I • h1Gradient Ω 1 u) := rfl

theorem h1WirtingerDbar_apply (Ω : Set ℂ) (u : NeumannH1 Ω) :
    h1WirtingerDbar Ω u =
      (1 / 2 : ℂ) • (h1Gradient Ω 0 u + Complex.I • h1Gradient Ω 1 u) := rfl

theorem h1WirtingerD_eq_zero_of_antiholomorphic {Ω : Set ℂ} (u : NeumannH1 Ω)
    (hu : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u) :
    h1WirtingerD Ω u = 0 := by
  rw [h1WirtingerD_apply, hu, sub_self, smul_zero]

/-- A computation barrier for the completed H¹ Cauchy--Riemann equation. -/
theorem h1WirtingerD_eq_zero_of_cauchyRiemann (Ω : Set ℂ) (u : NeumannH1 Ω)
    (hu : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u) :
    h1WirtingerD Ω u = 0 := h1WirtingerD_eq_zero_of_antiholomorphic u hu

/-- A genuine antiholomorphic primitive has the stated conjugate derivative. -/
theorem h1WirtingerDbar_eq_value_of_components (Ω : Set ℂ) (u v : NeumannH1 Ω)
    (hx : h1Gradient Ω 0 u = h1Value Ω v)
    (hy : h1Gradient Ω 1 u = -Complex.I • h1Value Ω v) :
    h1WirtingerDbar Ω u = h1Value Ω v := by
  rw [h1WirtingerDbar_apply, hx, hy]
  simp only [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  module

/-- A bounded linear test pairing keeps calculations on L² elements rather
than unfolding their a.e. representatives in every product rule. -/
private def vekuaL2TestPair (Ω : Set ℂ) {φ : ℂ → ℂ}
    (hφ : TestFunction Ω φ) : L2 Ω →L[ℂ] ℂ :=
  innerSL ℂ ((hφ.conj.memLp' 2).toLp (fun z => conj (φ z)))

private theorem vekuaL2TestPair_apply (Ω : Set ℂ) {φ : ℂ → ℂ}
    (hφ : TestFunction Ω φ) (u : L2 Ω) :
    vekuaL2TestPair Ω hφ u = ∫ z in Ω, u z * φ z := by
  change ⟪(hφ.conj.memLp' 2).toLp (fun z => conj (φ z)), u⟫_ℂ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hφ.conj.memLp' 2 (μ := volume.restrict Ω)).coeFn_toLp] with z hz
  simp only [RCLike.inner_apply, hz, Complex.conj_conj]

private theorem vekua_integral_smul {Ω : Set ℂ} {φ : ℂ → ℂ}
    (hφ : TestFunction Ω φ) (c : ℂ) (u : L2 Ω) :
    (∫ z in Ω, (c • u : L2 Ω) z * φ z) = c * ∫ z in Ω, u z * φ z := by
  rw [← vekuaL2TestPair_apply Ω hφ, map_smul, smul_eq_mul,
    vekuaL2TestPair_apply]

private theorem vekua_integral_D {Ω : Set ℂ} (u : NeumannH1 Ω)
    {φ : ℂ → ℂ} (hφ : TestFunction Ω φ) :
    (∫ z in Ω, h1WirtingerD Ω u z * φ z) = (1 / 2 : ℂ) *
      ((∫ z in Ω, h1Gradient Ω 0 u z * φ z) -
        Complex.I * ∫ z in Ω, h1Gradient Ω 1 u z * φ z) := by
  rw [← vekuaL2TestPair_apply Ω hφ, h1WirtingerD_apply,
    map_smul, map_sub, map_smul]
  simp only [smul_eq_mul, vekuaL2TestPair_apply]

private theorem vekua_integral_Dbar {Ω : Set ℂ} (u : NeumannH1 Ω)
    {φ : ℂ → ℂ} (hφ : TestFunction Ω φ) :
    (∫ z in Ω, h1WirtingerDbar Ω u z * φ z) = (1 / 2 : ℂ) *
      ((∫ z in Ω, h1Gradient Ω 0 u z * φ z) +
        Complex.I * ∫ z in Ω, h1Gradient Ω 1 u z * φ z) := by
  rw [← vekuaL2TestPair_apply Ω hφ, h1WirtingerDbar_apply,
    map_smul, map_add, map_smul]
  simp only [smul_eq_mul, vekuaL2TestPair_apply]

/-- The actual weak-gradient equation for the first Wirtinger derivative. -/
theorem h1WirtingerD_weak_test {Ω : Set ℂ} (u : NeumannH1 Ω)
    {φ : ℂ → ℂ} (hφ : TestFunction Ω φ) :
    (∫ z in Ω, h1Value Ω u z * dirD φ 1 z) -
        Complex.I * (∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z) =
      -2 * ∫ z in Ω, h1WirtingerD Ω u z * φ z := by
  have hx := h1Value_weakGradient Ω u φ hφ 0
  have hy := h1Value_weakGradient Ω u φ hφ 1
  change (∫ z in Ω, h1Value Ω u z * dirD φ 1 z) =
    -∫ z in Ω, h1Gradient Ω 0 u z * φ z at hx
  change (∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z) =
    -∫ z in Ω, h1Gradient Ω 1 u z * φ z at hy
  rw [hx, hy, vekua_integral_D u hφ]
  ring

/-- The actual weak-gradient equation for the conjugate Wirtinger derivative. -/
theorem h1WirtingerDbar_weak_test {Ω : Set ℂ} (u : NeumannH1 Ω)
    {φ : ℂ → ℂ} (hφ : TestFunction Ω φ) :
    (∫ z in Ω, h1Value Ω u z * dirD φ 1 z) +
        Complex.I * (∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z) =
      -2 * ∫ z in Ω, h1WirtingerDbar Ω u z * φ z := by
  have hx := h1Value_weakGradient Ω u φ hφ 0
  have hy := h1Value_weakGradient Ω u φ hφ 1
  change (∫ z in Ω, h1Value Ω u z * dirD φ 1 z) =
    -∫ z in Ω, h1Gradient Ω 0 u z * φ z at hx
  change (∫ z in Ω, h1Value Ω u z * dirD φ Complex.I z) =
    -∫ z in Ω, h1Gradient Ω 1 u z * φ z at hy
  rw [hx, hy, vekua_integral_Dbar u hφ]
  ring

private theorem vekua_dirD_comm {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (v w z : ℂ) :
    dirD (dirD φ v) w z = dirD (dirD φ w) v z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (m := (⊤ : ℕ∞)) le_rfl).differentiable (by simp) z
  have hv : fderiv ℝ (dirD φ v) z w = fderiv ℝ (fderiv ℝ φ) z w v := by
    change fderiv ℝ (fun x => fderiv ℝ φ x v) z w = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have hw : fderiv ℝ (dirD φ w) z v = fderiv ℝ (fderiv ℝ φ) z v w := by
    change fderiv ℝ (fun x => fderiv ℝ φ x w) z v = _
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  change fderiv ℝ (dirD φ v) z w = fderiv ℝ (dirD φ w) z v
  rw [hv, hw]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
        WithTop.coe_le_coe.mpr le_top))).eq w v

private theorem vekua_lap_factor (xx xy yx yy : ℂ) (hxy : xy = yx) :
    xx + yy = (xx - Complex.I * xy) + Complex.I * (yx - Complex.I * yy) := by
  rw [hxy]
  simp only [mul_sub, ← mul_assoc, Complex.I_mul_I]
  ring

/-- Distributionally, `4 ∂bar ∂ u = Δu`, proved for actual H¹ values by
two applications of their defining weak-gradient identities. -/
theorem h1_weak_lap_of_wirtinger_factorization {Ω : Set ℂ}
    (u v : NeumannH1 Ω) (f : L2 Ω)
    (hu : h1WirtingerD Ω u = h1Value Ω v)
    (hv : h1WirtingerDbar Ω v = f)
    {φ : ℂ → ℂ} (hφ : TestFunction Ω φ) :
    (∫ z in Ω, h1Value Ω u z * lap φ z) =
      4 * ∫ z in Ω, f z * φ z := by
  have hx := h1WirtingerD_weak_test u (hφ.dirD 1)
  have hy := h1WirtingerD_weak_test u (hφ.dirD Complex.I)
  have hz := h1WirtingerDbar_weak_test v hφ
  rw [hu] at hx hy
  rw [hv] at hz
  have hc :
      (∫ z in Ω, h1Value Ω u z * dirD (dirD φ 1) Complex.I z) =
        ∫ z in Ω, h1Value Ω u z * dirD (dirD φ Complex.I) 1 z := by
    apply integral_congr_ae
    refine Filter.Eventually.of_forall (fun z => ?_)
    change h1Value Ω u z * dirD (dirD φ 1) Complex.I z =
      h1Value Ω u z * dirD (dirD φ Complex.I) 1 z
    rw [vekua_dirD_comm hφ.1]
  have hxx := integrable_mul_test (Lp.memLp (h1Value Ω u)) ((hφ.dirD 1).dirD 1)
  have hyy := integrable_mul_test (Lp.memLp (h1Value Ω u))
    ((hφ.dirD Complex.I).dirD Complex.I)
  calc
    _ = (∫ z in Ω, h1Value Ω u z * dirD (dirD φ 1) 1 z) +
        ∫ z in Ω, h1Value Ω u z * dirD (dirD φ Complex.I) Complex.I z := by
      simp only [lap, mul_add]
      exact integral_add hxx hyy
    _ = ((∫ z in Ω, h1Value Ω u z * dirD (dirD φ 1) 1 z) -
          Complex.I * ∫ z in Ω, h1Value Ω u z * dirD (dirD φ 1) Complex.I z) +
        Complex.I * ((∫ z in Ω,
          h1Value Ω u z * dirD (dirD φ Complex.I) 1 z) -
          Complex.I * ∫ z in Ω,
            h1Value Ω u z * dirD (dirD φ Complex.I) Complex.I z) :=
      vekua_lap_factor _ _ _ _ hc
    _ = -2 * ((∫ z in Ω, h1Value Ω v z * dirD φ 1 z) +
          Complex.I * ∫ z in Ω, h1Value Ω v z * dirD φ Complex.I z) := by
      rw [hx, hy]
      ring
    _ = 4 * ∫ z in Ω, f z * φ z := by
      rw [hz]
      ring

/-- The factorization gives the genuine compact-test Helmholtz equation.
Taking `α = -E/4` yields exactly `Δu + E u = 0`. -/
theorem h1_weak_helmholtz_of_wirtinger_factorization {Ω : Set ℂ}
    (u v : NeumannH1 Ω) (α : ℂ)
    (hu : h1WirtingerD Ω u = h1Value Ω v)
    (hv : h1WirtingerDbar Ω v = α • h1Value Ω u)
    {φ : ℂ → ℂ} (hφ : TestFunction Ω φ) :
    (∫ z in Ω, h1Value Ω u z * (lap φ z - 4 * α * φ z)) = 0 := by
  have h := h1_weak_lap_of_wirtinger_factorization u v
    (α • h1Value Ω u) hu hv hφ
  rw [vekua_integral_smul hφ] at h
  have hl := integrable_mul_test (Lp.memLp (h1Value Ω u)) hφ.lap
  have hr := (integrable_mul_test (Lp.memLp (h1Value Ω u)) hφ).const_mul (4 * α)
  calc
    _ = (∫ z in Ω, h1Value Ω u z * lap φ z) -
        (4 * α) * ∫ z in Ω, h1Value Ω u z * φ z := by
      calc
        _ = ∫ z in Ω, h1Value Ω u z * lap φ z -
            (4 * α) * (h1Value Ω u z * φ z) := by
          apply integral_congr_ae
          refine Filter.Eventually.of_forall (fun z => ?_)
          change h1Value Ω u z * (lap φ z - 4 * α * φ z) =
            h1Value Ω u z * lap φ z - (4 * α) * (h1Value Ω u z * φ z)
          ring
        _ = _ := by rw [integral_sub hl hr, integral_const_mul]
    _ = 0 := by rw [h]; ring

/-- The affine H¹ product rule for the actual first Wirtinger derivative. -/
theorem h1WirtingerD_neumannH1AffineMultiplier {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (p : ℂ) (u : NeumannH1 Ω) :
    h1WirtingerD Ω (neumannH1AffineMultiplier hb p u) =
      neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p)
        (h1WirtingerD Ω u) + h1Value Ω u := by
  rw [h1WirtingerD_apply, h1Gradient_neumannH1AffineMultiplier_x,
    h1Gradient_neumannH1AffineMultiplier_y, h1WirtingerD_apply]
  simp only [map_smul, map_sub, smul_add, smul_smul, Complex.I_mul_I,
    neg_smul, one_smul]
  module

/-- Multiplication by `z-p` commutes with the conjugate Wirtinger derivative. -/
theorem h1WirtingerDbar_neumannH1AffineMultiplier {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (p : ℂ) (u : NeumannH1 Ω) :
    h1WirtingerDbar Ω (neumannH1AffineMultiplier hb p u) =
      neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p)
        (h1WirtingerDbar Ω u) := by
  rw [h1WirtingerDbar_apply, h1Gradient_neumannH1AffineMultiplier_x,
    h1Gradient_neumannH1AffineMultiplier_y, h1WirtingerDbar_apply]
  simp only [map_smul, map_add, smul_add, smul_smul, Complex.I_mul_I,
    neg_smul, one_smul]
  module

/-- Powers of the actual H¹ multiplier agree with powers of its L² value
multiplier; this is an operator statement on genuine H¹ inputs. -/
theorem h1Value_neumannH1AffineMultiplier_pow {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (p : ℂ) (u : NeumannH1 Ω) (j : ℕ) :
    h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) u) =
      (neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) ^ j)
        (h1Value Ω u) := by
  induction j with
  | zero => simp only [pow_zero, ContinuousLinearMap.one_apply]
  | succ j ih =>
    calc
      _ = neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p)
          (h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) u)) := by
        rw [pow_succ', ContinuousLinearMap.mul_apply, h1Value_neumannH1AffineMultiplier]
      _ = _ := by rw [ih, pow_succ', ContinuousLinearMap.mul_apply]

theorem h1WirtingerDbar_affine_pow {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (p : ℂ) (u : NeumannH1 Ω) (j : ℕ) :
    h1WirtingerDbar Ω ((neumannH1AffineMultiplier hb p ^ j) u) =
      (neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p) ^ j)
        (h1WirtingerDbar Ω u) := by
  induction j with
  | zero => simp only [pow_zero, ContinuousLinearMap.one_apply]
  | succ j ih =>
    calc
      _ = neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p)
          (h1WirtingerDbar Ω ((neumannH1AffineMultiplier hb p ^ j) u)) := by
        rw [pow_succ', ContinuousLinearMap.mul_apply,
          h1WirtingerDbar_neumannH1AffineMultiplier]
      _ = _ := by rw [ih, pow_succ', ContinuousLinearMap.mul_apply]

private theorem vekua_nat_succ_smul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (j : ℕ) (x : V) :
    ((j + 1 : ℕ) : ℂ) • x + x = ((j + 1 + 1 : ℕ) : ℂ) • x := by
  have hc : ((j + 1 + 1 : ℕ) : ℂ) = ((j + 1 : ℕ) : ℂ) + 1 := by
    simp only [Nat.cast_add, Nat.cast_one]
  rw [hc, add_smul, one_smul]

private theorem vekua_affine_successor {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] (L : V →L[ℂ] V) (j : ℕ) (x y : V) (hL : L x = y) :
    L (((j + 1 : ℕ) : ℂ) • x) + y = ((j + 1 + 1 : ℕ) : ℂ) • y := by
  rw [map_smul, hL]
  exact vekua_nat_succ_smul j y

/-- The true polynomial differentiation rule for an antiholomorphic H¹
input. No regularity of that input beyond H¹ is used. -/
theorem h1WirtingerD_affine_pow_of_antiholomorphic {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (p : ℂ) (u : NeumannH1 Ω)
    (hu : h1Gradient Ω 0 u = Complex.I • h1Gradient Ω 1 u) (j : ℕ) :
    h1WirtingerD Ω ((neumannH1AffineMultiplier hb p ^ (j + 1)) u) =
      ((j + 1 : ℕ) : ℂ) • h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) u) := by
  have hzero := h1WirtingerD_eq_zero_of_antiholomorphic u hu
  induction j with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, ContinuousLinearMap.one_apply,
      h1WirtingerD_neumannH1AffineMultiplier, hzero, map_zero, zero_add,
      Nat.cast_one, one_smul]
  | succ j ih =>
    have hval : neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p)
        (h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) u)) =
        h1Value Ω ((neumannH1AffineMultiplier hb p ^ (j + 1)) u) := by
      rw [pow_succ', ContinuousLinearMap.mul_apply, h1Value_neumannH1AffineMultiplier]
    calc
      _ = neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p)
          (h1WirtingerD Ω ((neumannH1AffineMultiplier hb p ^ (j + 1)) u)) +
          h1Value Ω ((neumannH1AffineMultiplier hb p ^ (j + 1)) u) := by
        rw [pow_succ', ContinuousLinearMap.mul_apply,
          h1WirtingerD_neumannH1AffineMultiplier]
      _ = _ := by
        rw [ih]
        exact vekua_affine_successor (V := L2 Ω)
          (neumannAffineL2Multiplier p (neumannH1AffineBound_spec hb p)) j
          (h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) u))
          (h1Value Ω ((neumannH1AffineMultiplier hb p ^ (j + 1)) u)) hval

/-- If `w` is a genuine antiholomorphic primitive of `v`, each polynomial
term has the exact distributional Laplacian needed for factorial cancellation. -/
theorem h1_weak_lap_affine_pow_of_antiholomorphic_primitive {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (p : ℂ) (w v : NeumannH1 Ω)
    (hx : h1Gradient Ω 0 w = h1Value Ω v)
    (hy : h1Gradient Ω 1 w = -Complex.I • h1Value Ω v)
    (j : ℕ) {φ : ℂ → ℂ} (hφ : TestFunction Ω φ) :
    (∫ z in Ω, h1Value Ω ((neumannH1AffineMultiplier hb p ^ (j + 1)) w) z * lap φ z) =
      4 * ((j + 1 : ℕ) : ℂ) *
        ∫ z in Ω, h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) v) z * φ z := by
  have hw : h1Gradient Ω 0 w = Complex.I • h1Gradient Ω 1 w := by
    rw [hx, hy, smul_smul]
    simp only [mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  have hbar : h1WirtingerDbar Ω w = h1Value Ω v := by
    exact h1WirtingerDbar_eq_value_of_components Ω w v hx hy
  have hu : h1WirtingerD Ω ((neumannH1AffineMultiplier hb p ^ (j + 1)) w) =
      h1Value Ω (((j + 1 : ℕ) : ℂ) •
        ((neumannH1AffineMultiplier hb p ^ j) w)) := by
    rw [map_smul]
    exact h1WirtingerD_affine_pow_of_antiholomorphic hb p w hw j
  have hv : h1WirtingerDbar Ω (((j + 1 : ℕ) : ℂ) •
      ((neumannH1AffineMultiplier hb p ^ j) w)) =
      ((j + 1 : ℕ) : ℂ) • h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) v) := by
    rw [map_smul, h1WirtingerDbar_affine_pow, hbar,
      h1Value_neumannH1AffineMultiplier_pow]
  have h := h1_weak_lap_of_wirtinger_factorization
    ((neumannH1AffineMultiplier hb p ^ (j + 1)) w)
    (((j + 1 : ℕ) : ℂ) • ((neumannH1AffineMultiplier hb p ^ j) w))
    (((j + 1 : ℕ) : ℂ) • h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) v)) hu hv hφ
  rw [vekua_integral_smul hφ] at h
  simpa only [mul_assoc] using h

/-- Actual weak-gradient pairing against a compact smooth test. -/
theorem h1Gradient_compact_test_eq_neg_lap {Ω : Set ℂ} (u : NeumannH1 Ω)
    {φ : ℂ → ℂ} (hφ : TestFunction Ω φ) :
    (∑ i : Fin 2, ∫ z in Ω, h1Gradient Ω i u z * fderiv ℝ φ z (coordDir i)) =
      -(∫ z in Ω, h1Value Ω u z * lap φ z) := by
  have hx := h1Value_weakGradient Ω u (dirD φ 1) (hφ.dirD 1) 0
  have hy := h1Value_weakGradient Ω u (dirD φ Complex.I) (hφ.dirD Complex.I) 1
  change (∫ z in Ω, h1Value Ω u z * dirD (dirD φ 1) 1 z) =
    -∫ z in Ω, h1Gradient Ω 0 u z * dirD φ 1 z at hx
  change (∫ z in Ω, h1Value Ω u z * dirD (dirD φ Complex.I) Complex.I z) =
    -∫ z in Ω, h1Gradient Ω 1 u z * dirD φ Complex.I z at hy
  have hxx := integrable_mul_test (Lp.memLp (h1Value Ω u)) ((hφ.dirD 1).dirD 1)
  have hyy := integrable_mul_test (Lp.memLp (h1Value Ω u))
    ((hφ.dirD Complex.I).dirD Complex.I)
  have hlap : (∫ z in Ω, h1Value Ω u z * lap φ z) =
      -(∫ z in Ω, h1Gradient Ω 0 u z * dirD φ 1 z) -
        ∫ z in Ω, h1Gradient Ω 1 u z * dirD φ Complex.I z := by
    calc
      _ = (∫ z in Ω, h1Value Ω u z * dirD (dirD φ 1) 1 z) +
          ∫ z in Ω, h1Value Ω u z * dirD (dirD φ Complex.I) Complex.I z := by
        simp only [lap, mul_add]
        exact integral_add hxx hyy
      _ = _ := by rw [hx, hy]; ring
  rw [Fin.sum_univ_two]
  change (∫ z in Ω, h1Gradient Ω 0 u z * dirD φ 1 z) +
    (∫ z in Ω, h1Gradient Ω 1 u z * dirD φ Complex.I z) = _
  rw [hlap]
  ring

/-- The physical weak gradient recurrence for the polynomial primitive terms.
The minus sign comes from the defining compact-test weak gradient convention. -/
theorem h1Gradient_affine_pow_compact_test_of_antiholomorphic_primitive {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (p : ℂ) (w v : NeumannH1 Ω)
    (hx : h1Gradient Ω 0 w = h1Value Ω v)
    (hy : h1Gradient Ω 1 w = -Complex.I • h1Value Ω v)
    (j : ℕ) {φ : ℂ → ℂ} (hφ : TestFunction Ω φ) :
    (∑ i : Fin 2, ∫ z in Ω,
      h1Gradient Ω i ((neumannH1AffineMultiplier hb p ^ (j + 1)) w) z *
        fderiv ℝ φ z (coordDir i)) =
      -(4 * ((j + 1 : ℕ) : ℂ) *
        ∫ z in Ω, h1Value Ω ((neumannH1AffineMultiplier hb p ^ j) v) z * φ z) := by
  rw [h1Gradient_compact_test_eq_neg_lap
      ((neumannH1AffineMultiplier hb p ^ (j + 1)) w) hφ,
    h1_weak_lap_affine_pow_of_antiholomorphic_primitive hb p w v hx hy j hφ]

end PolyaNeumann
