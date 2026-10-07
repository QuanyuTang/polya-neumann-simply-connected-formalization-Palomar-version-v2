module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# An actual smooth Fourier collar

The coefficient `a n` is the ordinary Taylor coefficient, hence the
averaged circle Fourier coefficient when that identification is proved.
No orthonormal Fourier normalization or square-root period is inserted.

The genuine cutoff is one on the negative half-line and zero past one.
The nth monomial is cut off at `n * (normSq z - 1) = 1`. On this support
`norm z ^ n ≤ exp (1/2)`. The real kth derivatives have a true uniform
bound `B k * n ^ k`, obtained from scalar restriction, finite compact
derivative bounds, and Mathlib's actual product/composition estimates.
Weighted absolute summability of the Taylor coefficients then proves
global real C∞ smoothness of the constructed series.

The final matching lemma consumes a genuine Taylor-series identity,
not an assumed extension or assumed smoothness of an infinite sum.
Deriving rapid decay and the Taylor identity from the eventual smooth
circle trace remains a separate boundary-regularity/Fourier step.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open Set Metric Filter
open scoped Topology

/-- The actual transition, with precisely the required two constant sides. -/
def fourierCollarCutoff (t : ℝ) : ℝ := 1 - Real.smoothTransition t

theorem fourierCollarCutoff_one {t : ℝ} (ht : t ≤ 0) : fourierCollarCutoff t = 1 := by
  simp [fourierCollarCutoff, Real.smoothTransition.zero_of_nonpos ht]

theorem fourierCollarCutoff_zero {t : ℝ} (ht : 1 ≤ t) : fourierCollarCutoff t = 0 := by
  simp [fourierCollarCutoff, Real.smoothTransition.one_of_one_le ht]

theorem fourierCollarCutoff_mem_Icc (t : ℝ) : fourierCollarCutoff t ∈ Icc (0 : ℝ) 1 := by
  have h0 := Real.smoothTransition.nonneg t
  have h1 := Real.smoothTransition.le_one t
  constructor <;> dsimp [fourierCollarCutoff] <;> linarith

theorem fourierCollarCutoff_contDiff (N : ℕ∞) : ContDiff ℝ N fourierCollarCutoff :=
  contDiff_const.sub Real.smoothTransition.contDiff

/-- Each derivative is truly bounded globally: outside the compact
transition interval the function is locally constant. -/
theorem fourierCollarCutoff_exists_derivative_bound (i : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t : ℝ, ‖iteratedFDeriv ℝ i fourierCollarCutoff t‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    (ContDiff.continuous_iteratedFDeriv' (fourierCollarCutoff_contDiff (i : ℕ∞))).continuousOn
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro t
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · exact (hB t ht).trans (le_max_right _ _)
  · rcases lt_or_ge t 0 with ht0 | ht0
    · have heq : fourierCollarCutoff =ᶠ[𝓝 t] (fun _ : ℝ => (1 : ℝ)) := by
        filter_upwards [eventually_lt_nhds ht0] with s hs
        exact fourierCollarCutoff_one hs.le
      have hd := (heq.iteratedFDeriv ℝ i).eq_of_nhds
      rw [hd]
      cases i with
      | zero => simpa only [norm_iteratedFDeriv_zero, norm_one] using (le_max_left (1 : ℝ) B)
      | succ i =>
          simpa only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero] using
            (show (0 : ℝ) ≤ max 1 B by positivity)
    · have ht1 : 1 < t := lt_of_not_ge (fun h => ht ⟨ht0, h⟩)
      have heq : fourierCollarCutoff =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
        filter_upwards [eventually_gt_nhds ht1] with s hs
        exact fourierCollarCutoff_zero hs.le
      have hd := (heq.iteratedFDeriv ℝ i).eq_of_nhds
      rw [hd]
      simpa only [iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero] using
        (show (0 : ℝ) ≤ max 1 B by positivity)

/-- A finite family of the genuine global derivative bounds. -/
theorem fourierCollarCutoff_exists_finite_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i ≤ k, ∀ t : ℝ, ‖iteratedFDeriv ℝ i fourierCollarCutoff t‖ ≤ C := by
  choose B hB hbound using fourierCollarCutoff_exists_derivative_bound
  let C := max 1 (∑ i ∈ Finset.range (k + 1), B i)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro i hi t
  have hsingle : B i ≤ ∑ j ∈ Finset.range (k + 1), B j :=
    Finset.single_le_sum (fun j _ => (by linarith [hB j])) (Finset.mem_range.mpr (by omega))
  exact (hbound i t).trans (hsingle.trans (le_max_right _ _))

def fourierCollarRadialDefect (z : ℂ) : ℝ := ‖z‖ ^ 2 - 1

theorem fourierCollarRadialDefect_contDiff (N : ℕ∞) : ContDiff ℝ N fourierCollarRadialDefect :=
  (contDiff_norm_sq ℂ).sub contDiff_const

/-- Compact bounds on the unscaled radial polynomial. These are actual
iterated derivatives, rather than an assumed Faà di Bruno estimate. -/
theorem fourierCollarRadialDefect_exists_finite_derivative_bound (k : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ k, ∀ z ∈ closedBall (0 : ℂ) 2,
      ‖iteratedFDeriv ℝ i fourierCollarRadialDefect z‖ ≤ D := by
  have hbound (i : ℕ) : ∃ B : ℝ, 1 ≤ B ∧ ∀ z ∈ closedBall (0 : ℂ) 2,
      ‖iteratedFDeriv ℝ i fourierCollarRadialDefect z‖ ≤ B := by
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) 2).exists_bound_of_continuousOn
      (ContDiff.continuous_iteratedFDeriv' (fourierCollarRadialDefect_contDiff (i : ℕ∞))).continuousOn
    exact ⟨max 1 B, le_max_left _ _, fun z hz => (hB z hz).trans (le_max_right _ _)⟩
  choose B hB hbound using hbound
  let D := max 1 (∑ i ∈ Finset.range (k + 1), B i)
  refine ⟨D, le_max_left _ _, ?_⟩
  intro i hi z hz
  have hsingle : B i ≤ ∑ j ∈ Finset.range (k + 1), B j :=
    Finset.single_le_sum (fun j _ => (by linarith [hB j])) (Finset.mem_range.mpr (by omega))
  exact (hbound i z hz).trans (hsingle.trans (le_max_right _ _))

def fourierCollarScaledDefect (n : ℕ) (z : ℂ) : ℝ := (n : ℝ) * fourierCollarRadialDefect z

theorem fourierCollarScaledDefect_contDiff (N : ℕ∞) (n : ℕ) :
    ContDiff ℝ N (fourierCollarScaledDefect n) :=
  contDiff_const.mul (fourierCollarRadialDefect_contDiff N)

def fourierCollarTerm (n : ℕ) (z : ℂ) : ℂ :=
  z ^ n * (fourierCollarCutoff (fourierCollarScaledDefect n z) : ℂ)

theorem fourierCollarTerm_contDiff (N : ℕ∞) (n : ℕ) : ContDiff ℝ N (fourierCollarTerm n) :=
  (contDiff_id.pow n).mul (Complex.ofRealCLM.contDiff.comp
    ((fourierCollarCutoff_contDiff N).comp (fourierCollarScaledDefect_contDiff N n)))

theorem fourierCollarTerm_eq_pow_on_closedDisk (n : ℕ) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    fourierCollarTerm n z = z ^ n := by
  have hr : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hq : fourierCollarScaledDefect n z ≤ 0 := by
    dsimp [fourierCollarScaledDefect, fourierCollarRadialDefect]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by nlinarith [norm_nonneg z])
  simp only [fourierCollarTerm, fourierCollarCutoff_one hq, Complex.ofReal_one, mul_one]

/-- The support radius remains in a fixed compact ball. -/
theorem fourierCollar_support_radius {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : fourierCollarScaledDefect n z ≤ 1) :
    ‖z‖ ^ 2 ≤ 1 + 1 / (n : ℝ) ∧ z ∈ closedBall (0 : ℂ) 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hr : ‖z‖ ^ 2 - 1 ≤ 1 / (n : ℝ) := by
    apply (le_div_iff₀ hn0).mpr
    change (‖z‖ ^ 2 - 1) * (n : ℝ) ≤ 1
    rw [mul_comm]
    exact hz
  have hinv : 1 / (n : ℝ) ≤ 1 := (div_le_one hn0).mpr hn1
  refine ⟨by linarith, ?_⟩
  rw [mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg z]

/-- The shrinking support compensates exactly for monomial growth.
This proves the uniform exponential constant instead of assuming it. -/
theorem fourierCollar_support_pow_le_exp_half {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n)
    {z : ℂ} (hz : fourierCollarScaledDefect n z ≤ 1) :
    ‖z‖ ^ m ≤ Real.exp (1 / 2 : ℝ) := by
  have hsupport := (fourierCollar_support_radius hn hz).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hExp : 1 ≤ Real.exp (1 / 2 : ℝ) := by
    have h := Real.add_one_le_exp (1 / 2 : ℝ)
    linarith
  rcases le_or_gt ‖z‖ 1 with hr | hr
  · exact (pow_le_one₀ (norm_nonneg z) hr).trans hExp
  · have hlog : (2 : ℝ) * Real.log ‖z‖ ≤ ‖z‖ ^ 2 - 1 := by
      simpa only [Real.log_pow, Nat.cast_ofNat] using
        Real.log_le_sub_one_of_pos (sq_pos_of_pos (lt_trans zero_lt_one hr))
    have hlog' : 2 * Real.log ‖z‖ ≤ 1 / (n : ℝ) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hlog' hn0.le
    have hcancel : (1 / (n : ℝ)) * (n : ℝ) = 1 := by field_simp [hn0.ne']
    rw [hcancel] at hmul
    have hne : (n : ℝ) * Real.log ‖z‖ ≤ 1 / 2 := by nlinarith
    have hnpow : ‖z‖ ^ n ≤ Real.exp (1 / 2 : ℝ) := by
      have heq : ‖z‖ ^ n = Real.exp ((n : ℝ) * Real.log ‖z‖) := by
        rw [Real.exp_nat_mul, Real.exp_log (lt_trans zero_lt_one hr)]
      rw [heq]
      exact Real.exp_le_exp.mpr hne
    exact (pow_le_pow_right₀ hr.le hm).trans hnpow

/-- The exact real derivative norm of a holomorphic monomial. -/
theorem fourierCollar_pow_iteratedFDeriv_norm (n k : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ k (fun w : ℂ => w ^ n) z‖ =
      (n.descFactorial k : ℝ) * ‖z‖ ^ (n - k) := by
  have hp : ContDiffAt ℂ k (fun w : ℂ => w ^ n) z := (contDiff_id.pow n).contDiffAt
  rw [← hp.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_pow, norm_mul,
    Complex.norm_natCast, norm_pow]

theorem fourierCollar_pow_iteratedFDeriv_le {n : ℕ} (hn : 1 ≤ n) (k : ℕ) {z : ℂ}
    (hz : fourierCollarScaledDefect n z ≤ 1) :
    ‖iteratedFDeriv ℝ k (fun w : ℂ => w ^ n) z‖ ≤ (n : ℝ) ^ k * Real.exp (1 / 2 : ℝ) := by
  rw [fourierCollar_pow_iteratedFDeriv_norm]
  have hdesc : (n.descFactorial k : ℝ) ≤ (n : ℝ) ^ k := by
    exact_mod_cast Nat.descFactorial_le_pow n k
  exact mul_le_mul hdesc (fourierCollar_support_pow_le_exp_half hn (Nat.sub_le _ _) hz)
    (by positivity) (by positivity)

/-- True uniform kth-order bounds for the individual collar summands. -/
theorem fourierCollarTerm_exists_iteratedFDeriv_bound (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∀ z : ℂ,
      ‖iteratedFDeriv ℝ k (fourierCollarTerm n) z‖ ≤ B * (n : ℝ) ^ k := by
  obtain ⟨C, hC, hχ⟩ := fourierCollarCutoff_exists_finite_derivative_bound k
  obtain ⟨D, hD, hq⟩ := fourierCollarRadialDefect_exists_finite_derivative_bound k
  let B := ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * Real.exp (1 / 2 : ℝ) * ((k - i).factorial : ℝ) * C * D ^ (k - i)
  have hBdef : B = ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * Real.exp (1 / 2 : ℝ) * ((k - i).factorial : ℝ) * C * D ^ (k - i) := rfl
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg (fun i _ => by positivity)
  refine ⟨B, hB, ?_⟩
  intro n hn z
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  by_cases hz : fourierCollarScaledDefect n z ≤ 1
  · have hz2 := (fourierCollar_support_radius hn hz).2
    have hscaled (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ k) :
        ‖iteratedFDeriv ℝ i (fourierCollarScaledDefect n) z‖ ≤ ((n : ℝ) * D) ^ i := by
      have hscale : ‖iteratedFDeriv ℝ i (fourierCollarScaledDefect n) z‖ =
          (n : ℝ) * ‖iteratedFDeriv ℝ i fourierCollarRadialDefect z‖ := by
        change ‖iteratedFDeriv ℝ i (fun w => (n : ℝ) • fourierCollarRadialDefect w) z‖ = _
        rw [iteratedFDeriv_const_smul_apply'
          (fourierCollarRadialDefect_contDiff (i : ℕ∞)).contDiffAt, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg hn0.le]
      rw [hscale]
      have hND : 1 ≤ (n : ℝ) * D := by
        simpa only [one_mul] using mul_le_mul hn1 hD (by norm_num : (0 : ℝ) ≤ 1) hn0.le
      exact (mul_le_mul_of_nonneg_left (hq i hi z hz2) hn0.le).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ hND hi1)
    have hcut (j : ℕ) (hj : j ≤ k) :
        ‖iteratedFDeriv ℝ j
          (fun w : ℂ => (fourierCollarCutoff (fourierCollarScaledDefect n w) : ℂ)) z‖ ≤
          (j.factorial : ℝ) * C * ((n : ℝ) * D) ^ j := by
      have hc := norm_iteratedFDeriv_comp_le (fourierCollarCutoff_contDiff (j : ℕ∞))
        (fourierCollarScaledDefect_contDiff (j : ℕ∞) n) le_rfl z
        (fun i hi => hχ i (hi.trans hj) _) (fun i hi1 hi => hscaled i hi1 (hi.trans hj))
      have hnrm := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (x := z)
        (((fourierCollarCutoff_contDiff (j : ℕ∞)).comp
          (fourierCollarScaledDefect_contDiff (j : ℕ∞) n)).contDiffAt) le_rfl
      simpa only [Function.comp_def, Complex.ofRealLI_apply] using hnrm.le.trans hc
    have hprod := norm_iteratedFDeriv_mul_le
      (show ContDiff ℝ (k : ℕ∞) (fun w : ℂ => w ^ n) from contDiff_id.pow n)
      (Complex.ofRealCLM.contDiff.comp ((fourierCollarCutoff_contDiff (k : ℕ∞)).comp
        (fourierCollarScaledDefect_contDiff (k : ℕ∞) n))) z le_rfl
    change ‖iteratedFDeriv ℝ k (fun w : ℂ => w ^ n *
      (fourierCollarCutoff (fourierCollarScaledDefect n w) : ℂ)) z‖ ≤ _
    apply hprod.trans
    rw [hBdef, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hkmi : k - i ≤ k := Nat.sub_le _ _
    have hpow := fourierCollar_pow_iteratedFDeriv_le hn i hz
    have hcut' := hcut (k - i) hkmi
    have hmul := mul_le_mul hpow hcut' (norm_nonneg _) (by positivity)
    have hchosen := mul_le_mul_of_nonneg_left hmul (show (0 : ℝ) ≤ k.choose i from Nat.cast_nonneg _)
    calc
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w : ℂ => w ^ n) z‖ *
          ‖iteratedFDeriv ℝ (k - i)
            (fun w : ℂ => (fourierCollarCutoff (fourierCollarScaledDefect n w) : ℂ)) z‖ ≤
          (k.choose i : ℝ) * ((n : ℝ) ^ i * Real.exp (1 / 2 : ℝ)) *
            (((k - i).factorial : ℝ) * C * ((n : ℝ) * D) ^ (k - i)) := by
        simpa only [mul_assoc] using hchosen
      _ = ((k.choose i : ℝ) * Real.exp (1 / 2 : ℝ) * ((k - i).factorial : ℝ) * C * D ^ (k - i)) *
          ((n : ℝ) ^ i * (n : ℝ) ^ (k - i)) := by rw [mul_pow]; ring
      _ = ((k.choose i : ℝ) * Real.exp (1 / 2 : ℝ) * ((k - i).factorial : ℝ) * C * D ^ (k - i)) *
          (n : ℝ) ^ k := by rw [← pow_add, Nat.add_sub_of_le hik]
  · have hgt : 1 < fourierCollarScaledDefect n z := lt_of_not_ge hz
    have heq : fourierCollarTerm n =ᶠ[𝓝 z] (fun _ : ℂ => (0 : ℂ)) := by
      have hopen : {w : ℂ | 1 < fourierCollarScaledDefect n w} ∈ 𝓝 z :=
        (isOpen_lt continuous_const (fourierCollarScaledDefect_contDiff (0 : ℕ∞) n).continuous).mem_nhds hgt
      filter_upwards [hopen] with w hw
      simp only [fourierCollarTerm, fourierCollarCutoff_zero hw.le, Complex.ofReal_zero, mul_zero]
    have hd := (heq.iteratedFDeriv ℝ k).eq_of_nhds
    rw [hd]
    simp only [iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero]
    exact mul_nonneg hB (pow_nonneg hn0.le _)

/-- All polynomially weighted ordinary Taylor coefficients are absolutely
summable. This is an intermediate Fourier regularity input, not a collar. -/
def HasRapidFourierDecay (a : ℕ → ℂ) : Prop :=
  ∀ k : ℕ, Summable (fun n : ℕ => ‖a (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ k)

def fourierCollarExtension (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  a 0 + ∑' n : ℕ, a (n + 1) • fourierCollarTerm (n + 1) z

/-- Smoothness of the constructed series follows from actual uniform
derivative majorants, rather than a smooth-series premise. -/
theorem fourierCollarExtension_contDiff {a : ℕ → ℂ} (ha : HasRapidFourierDecay a) :
    ContDiff ℝ (⊤ : ℕ∞) (fourierCollarExtension a) := by
  choose B hB hbound using fourierCollarTerm_exists_iteratedFDeriv_bound
  have hseries : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ℂ => ∑' n : ℕ, a (n + 1) • fourierCollarTerm (n + 1) z) := by
    apply contDiff_tsum (v := fun k n => B k * (‖a (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ k))
    · intro n
      exact (fourierCollarTerm_contDiff (⊤ : ℕ∞) (n + 1)).const_smul (a (n + 1))
    · intro k _
      exact (ha k).mul_left (B k)
    · intro k n z _
      rw [iteratedFDeriv_const_smul_apply'
        (fourierCollarTerm_contDiff (k : ℕ∞) (n + 1)).contDiffAt, norm_smul]
      calc
        ‖a (n + 1)‖ * ‖iteratedFDeriv ℝ k (fourierCollarTerm (n + 1)) z‖ ≤
            ‖a (n + 1)‖ * (B k * ((n + 1 : ℕ) : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (hbound k (n + 1) (by omega) z) (norm_nonneg _)
        _ = B k * (‖a (n + 1)‖ * ((n + 1 : ℕ) : ℝ) ^ k) := by ring
  exact contDiff_const.add hseries

/-- Every summand agrees with its actual Taylor monomial on the
closed disk, including the boundary. The zeroth coefficient is separate. -/
theorem fourierCollarExtension_eq_taylor_on_closedDisk (a : ℕ → ℂ) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) :
    fourierCollarExtension a z = a 0 + ∑' n : ℕ, a (n + 1) * z ^ (n + 1) := by
  unfold fourierCollarExtension
  congr 1
  apply tsum_congr
  intro n
  rw [fourierCollarTerm_eq_pow_on_closedDisk (n + 1) hz]
  rfl

/-- A genuine smooth collar from genuine rapidly decaying Taylor data.
The input equality is a Taylor-series identity for F, never an assumed
extension or an assumed infinite-sum differentiability assertion. -/
theorem exists_smooth_fourier_collar_of_taylor {a : ℕ → ℂ} (ha : HasRapidFourierDecay a)
    {F : ℂ → ℂ} (hTaylor : ∀ z ∈ closedBall (0 : ℂ) 1,
      F z = a 0 + ∑' n : ℕ, a (n + 1) * z ^ (n + 1)) :
    ∃ G : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧ EqOn G F (closedBall (0 : ℂ) 1) := by
  refine ⟨fourierCollarExtension a, fourierCollarExtension_contDiff ha, ?_⟩
  intro z hz
  rw [fourierCollarExtension_eq_taylor_on_closedDisk a hz, hTaylor z hz]

/-- Interior complex holomorphicity is inherited from the actual F.
Only real smoothness is asserted outside the disk. -/
theorem exists_smooth_holomorphic_fourier_collar_of_taylor {a : ℕ → ℂ}
    (ha : HasRapidFourierDecay a) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hTaylor : ∀ z ∈ closedBall (0 : ℂ) 1,
      F z = a 0 + ∑' n : ℕ, a (n + 1) * z ^ (n + 1)) :
    ∃ G : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) G ∧
      EqOn G F (closedBall (0 : ℂ) 1) ∧ DifferentiableOn ℂ G (ball (0 : ℂ) 1) := by
  obtain ⟨G, hG, hGF⟩ := exists_smooth_fourier_collar_of_taylor ha hTaylor
  exact ⟨G, hG, hGF, hF.congr (fun z hz => hGF (ball_subset_closedBall hz))⟩

end PolyaNeumann
