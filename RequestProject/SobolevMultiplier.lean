module

public import RequestProject.SobolevCircle
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.PSeries

/-!
# Multiplier estimates on the Sobolev scale of the circle

The multiplier estimates of External theorem E2 (used in Lemmas 5.2 and 5.3 of the paper:
multiplication by a smooth coefficient, and by the powers `γ^j`, is bounded on `H^s(𝕋)`) in the
Fourier model of `SobolevCircle.lean`. On Fourier coefficients, multiplication of functions is
the convolution `(c ⋆ f)ₙ = ∑ₖ cₖ f_{n-k}`, and the Sobolev weights `λₙ = 1 + |n|` satisfy
Peetre's inequality `λₙ^s ≤ λ_{n-k}^s λₖ^s` (`s ≥ 0`). Hence:

* `young_ennreal`: Young's inequality `‖C ⋆ F‖_{ℓ²} ≤ ‖C‖_{ℓ¹} ‖F‖_{ℓ²}` for nonnegative
  sequences (in `ℝ≥0∞`, with the Cauchy–Schwarz inequality `ennreal_tsum_cs`);
* `sobNormSq_seqConv_le` (**multiplier estimate**): if `∑ₖ λₖ^s |cₖ| = M < ∞` and `f ∈ H^s`,
  then `c ⋆ f ∈ H^s` and `‖c ⋆ f‖_{H^s} ≤ M ‖f‖_{H^s}`;
* `wl1Norm_seqConv_le` (**algebra property**): the weighted `ℓ¹` norm
  `∑ₖ λₖ^s |cₖ|` is submultiplicative under convolution, so the coefficient sequences of
  products such as `γ^j` have norm at most `R^j` (`wl1Norm_seqConvPow_le`).
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Filter Topology
open scoped ENNReal

/-! ### Peetre's inequality -/

/-- `λₙ ≤ λ_{n-k} λₖ` for the Sobolev weights `λₙ = 1 + |n|`. -/
lemma sobWeight_le_mul (n k : ℤ) : sobWeight n ≤ sobWeight (n - k) * sobWeight k := by
  unfold sobWeight
  have h1 : |(n : ℝ)| ≤ |((n - k : ℤ) : ℝ)| + |(k : ℝ)| := by
    push_cast
    calc |(n : ℝ)| = |((n : ℝ) - k) + k| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  nlinarith [abs_nonneg ((n - k : ℤ) : ℝ), abs_nonneg (k : ℝ),
    mul_nonneg (abs_nonneg ((n - k : ℤ) : ℝ)) (abs_nonneg (k : ℝ))]

/-- **Peetre's inequality** for `s ≥ 0`: `λₙ^s ≤ λ_{n-k}^s λₖ^s`. -/
lemma sobWeight_rpow_le_mul {s : ℝ} (hs : 0 ≤ s) (n k : ℤ) :
    sobWeight n ^ s ≤ sobWeight (n - k) ^ s * sobWeight k ^ s := by
  rw [← Real.mul_rpow (sobWeight_pos _).le (sobWeight_pos _).le]
  exact Real.rpow_le_rpow (sobWeight_pos _).le (sobWeight_le_mul n k) hs

/-! ### Young's inequality for nonnegative sequences -/

/-- Cauchy–Schwarz for weighted sums in `ℝ≥0∞`: `(∑ Cₖ Gₖ)² ≤ (∑ Cₖ)(∑ Cₖ Gₖ²)`. -/
theorem ennreal_tsum_cs {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (C G : ι → ℝ≥0∞) :
    (∑' k, C k * G k) ^ 2 ≤ (∑' k, C k) * ∑' k, C k * G k ^ 2 := by
  have hpq : (2:ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (MeasureTheory.Measure.count) hpq
    (f := fun k => C k ^ (1/2:ℝ)) (g := fun k => C k ^ (1/2:ℝ) * G k)
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable
  simp only [MeasureTheory.lintegral_count, Pi.mul_apply] at h
  have e1 : ∀ k, C k ^ (1/2:ℝ) * (C k ^ (1/2:ℝ) * G k) = C k * G k := by
    intro k
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ k, (C k ^ (1/2:ℝ)) ^ (2:ℝ) = C k := by
    intro k; rw [← ENNReal.rpow_mul]; norm_num
  have e3 : ∀ k, (C k ^ (1/2:ℝ) * G k) ^ (2:ℝ) = C k * G k ^ 2 := by
    intro k; rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2]; norm_cast
  simp only [e1, e2, e3] at h
  calc (∑' k, C k * G k) ^ 2
      ≤ ((∑' k, C k) ^ (1/2:ℝ) * (∑' k, C k * G k ^ 2) ^ (1/2:ℝ)) ^ 2 := by gcongr
    _ = _ := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul]; norm_num

/-- **Young's inequality** `ℓ¹ ⋆ ℓ² ⊆ ℓ²` on `ℤ`, for nonnegative sequences in `ℝ≥0∞`. -/
theorem young_ennreal (C F : ℤ → ℝ≥0∞) :
    ∑' n, (∑' k, C k * F (n - k)) ^ 2 ≤ (∑' k, C k) ^ 2 * ∑' n, F n ^ 2 := by
  calc ∑' n, (∑' k, C k * F (n - k)) ^ 2
      ≤ ∑' n, (∑' k, C k) * ∑' k, C k * F (n - k) ^ 2 :=
        ENNReal.tsum_le_tsum fun n => ennreal_tsum_cs _ _
    _ = (∑' k, C k) * ∑' k, C k * ∑' n, F (n - k) ^ 2 := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_comm]
        simp_rw [ENNReal.tsum_mul_left]
    _ = (∑' k, C k) ^ 2 * ∑' n, F n ^ 2 := by
        have : ∀ k : ℤ, ∑' n, F (n - k) ^ 2 = ∑' n, F n ^ 2 := fun k =>
          (Equiv.subRight k).tsum_eq (fun n => F n ^ 2)
        simp_rw [this, ENNReal.tsum_mul_right]; ring

/-! ### Sobolev norms and weighted `ℓ¹` norms of coefficient sequences -/

/-- `f ∈ H^s(𝕋)` on the Fourier side: `∑ₙ λₙ^{2s} |fₙ|² < ∞`. -/
def IsSobolevSeq (s : ℝ) (f : ℤ → ℂ) : Prop :=
  Summable fun n => (sobWeight n ^ s * ‖f n‖) ^ 2

/-- The squared `H^s` norm `∑ₙ (λₙ^s |fₙ|)²`. -/
def sobNormSq (s : ℝ) (f : ℤ → ℂ) : ℝ := ∑' n, (sobWeight n ^ s * ‖f n‖) ^ 2

/-- The weighted `ℓ¹` condition `∑ₖ λₖ^s |cₖ| < ∞` on a coefficient sequence (for `s ≥ 0` this
is the algebra of multipliers of `H^s` used here). -/
def IsWL1 (s : ℝ) (c : ℤ → ℂ) : Prop := Summable fun k => sobWeight k ^ s * ‖c k‖

/-- The weighted `ℓ¹` norm `∑ₖ λₖ^s |cₖ|`. -/
def wl1Norm (s : ℝ) (c : ℤ → ℂ) : ℝ := ∑' k, sobWeight k ^ s * ‖c k‖

/-- The convolution of coefficient sequences, `(c ⋆ f)ₙ = ∑ₖ cₖ f_{n-k}`: the Fourier
coefficients of a product. -/
def seqConv (c f : ℤ → ℂ) (n : ℤ) : ℂ := ∑' k, c k * f (n - k)

/-- **Multiplier estimate on `H^s(𝕋)`.** For `s ≥ 0`, if `∑ₖ λₖ^s |cₖ| < ∞` and `f ∈ H^s`, then
the convolution series converge, `c ⋆ f ∈ H^s`, and
`‖c ⋆ f‖²_{H^s} ≤ (∑ₖ λₖ^s |cₖ|)² ‖f‖²_{H^s}`. -/
theorem sobNormSq_seqConv_le {s : ℝ} (hs : 0 ≤ s) {c f : ℤ → ℂ} (hc : IsWL1 s c)
    (hf : IsSobolevSeq s f) :
    (∀ n, Summable fun k => c k * f (n - k)) ∧ IsSobolevSeq s (seqConv c f) ∧
      sobNormSq s (seqConv c f) ≤ wl1Norm s c ^ 2 * sobNormSq s f := by
  set a : ℤ → ℝ := fun k => sobWeight k ^ s * ‖c k‖ with ha
  set b : ℤ → ℝ := fun n => sobWeight n ^ s * ‖f n‖ with hb
  have ha0 : ∀ k, 0 ≤ a k := fun k => by have := sobWeight_pos k; positivity
  have hb0 : ∀ n, 0 ≤ b n := fun n => by have := sobWeight_pos n; positivity
  have hw1 : ∀ n, 1 ≤ sobWeight n ^ s := fun n => Real.one_le_rpow (one_le_sobWeight n) hs
  have hca : ∀ k, ‖c k‖ ≤ a k := fun k => le_mul_of_one_le_left (norm_nonneg _) (hw1 k)
  have hfb : ∀ n, ‖f n‖ ≤ b n := fun n => le_mul_of_one_le_left (norm_nonneg _) (hw1 n)
  set S := sobNormSq s f with hS
  set M := wl1Norm s c with hM
  have hbB : ∀ n, b n ≤ Real.sqrt S := fun n =>
    Real.le_sqrt_of_sq_le (hf.le_tsum n fun m _ => sq_nonneg _)
  have hsum : ∀ n, Summable fun k => c k * f (n - k) := fun n =>
    Summable.of_norm_bounded (hc.mul_right (Real.sqrt S)) fun k => by
      rw [norm_mul]
      exact mul_le_mul (hca k) ((hfb _).trans (hbB _)) (norm_nonneg _) (ha0 k)
  have hab : ∀ n, Summable fun k => a k * b (n - k) := fun n =>
    Summable.of_nonneg_of_le (fun k => mul_nonneg (ha0 k) (hb0 _))
      (fun k => mul_le_mul_of_nonneg_left (hbB _) (ha0 k)) (hc.mul_right (Real.sqrt S))
  -- pointwise bound by the convolution of the weighted sequences
  have hpt : ∀ n, sobWeight n ^ s * ‖seqConv c f n‖ ≤ ∑' k, a k * b (n - k) := by
    intro n
    have hn1 : Summable fun k => ‖c k * f (n - k)‖ := (hsum n).norm
    calc sobWeight n ^ s * ‖seqConv c f n‖
        ≤ sobWeight n ^ s * ∑' k, ‖c k * f (n - k)‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hn1) (by linarith [hw1 n])
      _ = ∑' k, sobWeight n ^ s * ‖c k * f (n - k)‖ := (tsum_mul_left).symm
      _ ≤ ∑' k, a k * b (n - k) := by
          refine Summable.tsum_le_tsum (fun k => ?_) (hn1.mul_left _) (hab n)
          rw [norm_mul, ha, hb]
          have hp := sobWeight_rpow_le_mul hs n k
          have := norm_nonneg (c k); have := norm_nonneg (f (n - k))
          calc sobWeight n ^ s * (‖c k‖ * ‖f (n - k)‖)
              ≤ (sobWeight (n - k) ^ s * sobWeight k ^ s) * (‖c k‖ * ‖f (n - k)‖) :=
                mul_le_mul_of_nonneg_right hp (by positivity)
            _ = _ := by ring
  -- Young's inequality in `ℝ≥0∞`
  set g : ℤ → ℝ := fun n => (sobWeight n ^ s * ‖seqConv c f n‖) ^ 2 with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => sq_nonneg _
  have hY := young_ennreal (fun k => ENNReal.ofReal (a k)) (fun n => ENNReal.ofReal (b n))
  have hMe : ∑' k, ENNReal.ofReal (a k) = ENNReal.ofReal M :=
    (ENNReal.ofReal_tsum_of_nonneg ha0 hc).symm
  have hSe : ∑' n, ENNReal.ofReal (b n) ^ 2 = ENNReal.ofReal S := by
    rw [hS, sobNormSq, ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hf]
    refine tsum_congr fun n => ?_
    rw [ENNReal.ofReal_pow (hb0 n)]
  have hgle : ∀ n, ENNReal.ofReal (g n) ≤
      (∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal (b (n - k))) ^ 2 := by
    intro n
    have e : ∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal (b (n - k)) =
        ENNReal.ofReal (∑' k, a k * b (n - k)) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (ha0 k) (hb0 _)) (hab n)]
      refine tsum_congr fun k => ?_
      rw [ENNReal.ofReal_mul (ha0 k)]
    rw [e, ← ENNReal.ofReal_pow (tsum_nonneg fun k => mul_nonneg (ha0 k) (hb0 _))]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hpt n
    have h0 : 0 ≤ sobWeight n ^ s * ‖seqConv c f n‖ :=
      mul_nonneg (by linarith [hw1 n]) (norm_nonneg _)
    exact pow_le_pow_left₀ h0 this 2
  have htot : ∑' n, ENNReal.ofReal (g n) ≤ ENNReal.ofReal (M ^ 2 * S) := by
    calc ∑' n, ENNReal.ofReal (g n) ≤ _ := ENNReal.tsum_le_tsum hgle
      _ ≤ _ := hY
      _ = ENNReal.ofReal (M ^ 2 * S) := by
        rw [hMe, hSe, ENNReal.ofReal_mul (sq_nonneg _),
          ENNReal.ofReal_pow (show 0 ≤ M from tsum_nonneg ha0)]
  have hgs : Summable g := by
    have := ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top htot)
    simpa [ENNReal.toReal_ofReal (hg0 _)] using this
  refine ⟨hsum, hgs, ?_⟩
  have hS0 : 0 ≤ S := tsum_nonneg fun n => sq_nonneg _
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), sobNormSq,
    ENNReal.ofReal_tsum_of_nonneg hg0 hgs]
  exact htot

/-- **Algebra property.** For `s ≥ 0` the weighted `ℓ¹` space is closed under convolution and
its norm is submultiplicative: `∑ₙ λₙ^s |(c ⋆ d)ₙ| ≤ (∑ λₖ^s |cₖ|)(∑ λₖ^s |dₖ|)`. -/
theorem wl1Norm_seqConv_le {s : ℝ} (hs : 0 ≤ s) {c d : ℤ → ℂ} (hc : IsWL1 s c)
    (hd : IsWL1 s d) :
    (∀ n, Summable fun k => c k * d (n - k)) ∧ IsWL1 s (seqConv c d) ∧
      wl1Norm s (seqConv c d) ≤ wl1Norm s c * wl1Norm s d := by
  set a : ℤ → ℝ := fun k => sobWeight k ^ s * ‖c k‖ with ha
  set b : ℤ → ℝ := fun n => sobWeight n ^ s * ‖d n‖ with hb
  have ha0 : ∀ k, 0 ≤ a k := fun k => by have := sobWeight_pos k; positivity
  have hb0 : ∀ n, 0 ≤ b n := fun n => by have := sobWeight_pos n; positivity
  have hw1 : ∀ n, 1 ≤ sobWeight n ^ s := fun n => Real.one_le_rpow (one_le_sobWeight n) hs
  have hca : ∀ k, ‖c k‖ ≤ a k := fun k => le_mul_of_one_le_left (norm_nonneg _) (hw1 k)
  have hdb : ∀ n, ‖d n‖ ≤ b n := fun n => le_mul_of_one_le_left (norm_nonneg _) (hw1 n)
  set N := wl1Norm s d with hN
  set M := wl1Norm s c with hM
  have hbB : ∀ n, b n ≤ N := fun n => hd.le_tsum n fun m _ => hb0 m
  have hsum : ∀ n, Summable fun k => c k * d (n - k) := fun n =>
    Summable.of_norm_bounded (hc.mul_right N) fun k => by
      rw [norm_mul]
      exact mul_le_mul (hca k) ((hdb _).trans (hbB _)) (norm_nonneg _) (ha0 k)
  have hab : ∀ n, Summable fun k => a k * b (n - k) := fun n =>
    Summable.of_nonneg_of_le (fun k => mul_nonneg (ha0 k) (hb0 _))
      (fun k => mul_le_mul_of_nonneg_left (hbB _) (ha0 k)) (hc.mul_right N)
  have hpt : ∀ n, sobWeight n ^ s * ‖seqConv c d n‖ ≤ ∑' k, a k * b (n - k) := by
    intro n
    have hn1 : Summable fun k => ‖c k * d (n - k)‖ := (hsum n).norm
    calc sobWeight n ^ s * ‖seqConv c d n‖
        ≤ sobWeight n ^ s * ∑' k, ‖c k * d (n - k)‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hn1) (by linarith [hw1 n])
      _ = ∑' k, sobWeight n ^ s * ‖c k * d (n - k)‖ := (tsum_mul_left).symm
      _ ≤ ∑' k, a k * b (n - k) := by
          refine Summable.tsum_le_tsum (fun k => ?_) (hn1.mul_left _) (hab n)
          rw [norm_mul, ha, hb]
          have hp := sobWeight_rpow_le_mul hs n k
          have := norm_nonneg (c k); have := norm_nonneg (d (n - k))
          calc sobWeight n ^ s * (‖c k‖ * ‖d (n - k)‖)
              ≤ (sobWeight (n - k) ^ s * sobWeight k ^ s) * (‖c k‖ * ‖d (n - k)‖) :=
                mul_le_mul_of_nonneg_right hp (by positivity)
            _ = _ := by ring
  set g : ℤ → ℝ := fun n => sobWeight n ^ s * ‖seqConv c d n‖ with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => mul_nonneg (by linarith [hw1 n]) (norm_nonneg _)
  have hgle : ∀ n, ENNReal.ofReal (g n) ≤
      ∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal (b (n - k)) := by
    intro n
    have e : ∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal (b (n - k)) =
        ENNReal.ofReal (∑' k, a k * b (n - k)) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (ha0 k) (hb0 _)) (hab n)]
      refine tsum_congr fun k => ?_
      rw [ENNReal.ofReal_mul (ha0 k)]
    rw [e]
    exact ENNReal.ofReal_le_ofReal (hpt n)
  have htot : ∑' n, ENNReal.ofReal (g n) ≤ ENNReal.ofReal (M * N) := by
    calc ∑' n, ENNReal.ofReal (g n)
        ≤ ∑' n, ∑' k, ENNReal.ofReal (a k) * ENNReal.ofReal (b (n - k)) :=
          ENNReal.tsum_le_tsum hgle
      _ = ∑' k, ENNReal.ofReal (a k) * ∑' n, ENNReal.ofReal (b (n - k)) := by
          rw [ENNReal.tsum_comm]; simp_rw [ENNReal.tsum_mul_left]
      _ = (∑' k, ENNReal.ofReal (a k)) * ∑' n, ENNReal.ofReal (b n) := by
          have : ∀ k : ℤ, ∑' n, ENNReal.ofReal (b (n - k)) = ∑' n, ENNReal.ofReal (b n) :=
            fun k => (Equiv.subRight k).tsum_eq (fun n => ENNReal.ofReal (b n))
          simp_rw [this, ENNReal.tsum_mul_right]
      _ = ENNReal.ofReal (M * N) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg ha0 hc, ← ENNReal.ofReal_tsum_of_nonneg hb0 hd,
            ← ENNReal.ofReal_mul (tsum_nonneg ha0)]
          rfl
  have hgs : Summable g := by
    have := ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top htot)
    simpa [ENNReal.toReal_ofReal (hg0 _)] using this
  refine ⟨hsum, hgs, ?_⟩
  have hM0 : 0 ≤ M := tsum_nonneg ha0
  have hN0 : 0 ≤ N := tsum_nonneg hb0
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), wl1Norm,
    ENNReal.ofReal_tsum_of_nonneg hg0 hgs]
  exact htot

/-! ### Powers: multipliers `γ^j` -/

/-- The unit of convolution, the coefficient sequence of the constant function `1`. -/
def seqDelta (n : ℤ) : ℂ := if n = 0 then 1 else 0

/-- Convolution powers `c^{⋆j}`, the coefficient sequences of the powers of a function. -/
def seqConvPow (c : ℤ → ℂ) : ℕ → ℤ → ℂ
  | 0 => seqDelta
  | j + 1 => seqConv c (seqConvPow c j)

lemma isWL1_seqDelta (s : ℝ) : IsWL1 s seqDelta := by
  refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
  simp only [Finset.mem_singleton] at hn
  simp [seqDelta, hn]

lemma wl1Norm_seqDelta (s : ℝ) : wl1Norm s seqDelta = 1 := by
  rw [wl1Norm, tsum_eq_single 0 fun n hn => by simp [seqDelta, hn]]
  simp [seqDelta, sobWeight]

/-- **Multiplier norms of powers.** For `s ≥ 0` the powers satisfy
`∑ₙ λₙ^s |(c^{⋆j})ₙ| ≤ (∑ₖ λₖ^s |cₖ|)^j`; with the multiplier estimate this bounds
multiplication by `γ^j` on `H^s(𝕋)` by `R^j`, as used in Lemma 5.3. -/
theorem wl1Norm_seqConvPow_le {s : ℝ} (hs : 0 ≤ s) {c : ℤ → ℂ} (hc : IsWL1 s c) (j : ℕ) :
    IsWL1 s (seqConvPow c j) ∧ wl1Norm s (seqConvPow c j) ≤ wl1Norm s c ^ j := by
  induction j with
  | zero => exact ⟨isWL1_seqDelta s, (wl1Norm_seqDelta s).le.trans (by simp)⟩
  | succ j ih =>
    obtain ⟨-, h1, h2⟩ := wl1Norm_seqConv_le hs hc ih.1
    refine ⟨h1, h2.trans ?_⟩
    have h0 : 0 ≤ wl1Norm s c :=
      tsum_nonneg fun k => by have := sobWeight_pos k; positivity
    rw [pow_succ']
    exact mul_le_mul_of_nonneg_left ih.2 h0

/-! ### Inverting the tangential derivative -/

/-- The primitive on the Fourier side, `pₙ = ψₙ / (i n)` (and `p₀ = 0`). -/
def primSeq (ψ : ℤ → ℂ) (n : ℤ) : ℂ := ψ n / (Complex.I * n)

lemma sobWeight_rpow_mul_norm_primSeq_le (s : ℝ) (ψ : ℤ → ℂ) (n : ℤ) :
    sobWeight n ^ (s + 1) * ‖primSeq ψ n‖ ≤ 2 * (sobWeight n ^ s * ‖ψ n‖) := by
  have hw := sobWeight_pos n
  by_cases hn : n = 0
  · subst hn; simp [primSeq]; positivity
  have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
  have hnorm : ‖primSeq ψ n‖ = ‖ψ n‖ / |(n : ℝ)| := by
    simp [primSeq, Complex.norm_intCast]
  rw [hnorm, Real.rpow_add hw, Real.rpow_one]
  have hle : sobWeight n ≤ 2 * |(n : ℝ)| := by unfold sobWeight; linarith
  have hpos : 0 < |(n : ℝ)| := by linarith
  have h1 := norm_nonneg (ψ n)
  have h2 : 0 ≤ sobWeight n ^ s := by positivity
  rw [mul_div_assoc', div_le_iff₀ hpos]
  calc sobWeight n ^ s * sobWeight n * ‖ψ n‖
      ≤ sobWeight n ^ s * (2 * |(n : ℝ)|) * ‖ψ n‖ := by gcongr
    _ = _ := by ring

/-- **Inversion of tangential differentiation gains one derivative.** If `ψ ∈ H^s`, the Fourier
primitive `pₙ = ψₙ/(i n)` lies in `H^{s+1}` with `‖p‖²_{H^{s+1}} ≤ 4 ‖ψ‖²_{H^s}`. -/
theorem sobNormSq_primSeq_le (s : ℝ) {ψ : ℤ → ℂ} (hψ : IsSobolevSeq s ψ) :
    IsSobolevSeq (s + 1) (primSeq ψ) ∧ sobNormSq (s + 1) (primSeq ψ) ≤ 4 * sobNormSq s ψ := by
  have hpt : ∀ n, (sobWeight n ^ (s + 1) * ‖primSeq ψ n‖) ^ 2 ≤
      4 * (sobWeight n ^ s * ‖ψ n‖) ^ 2 := by
    intro n
    have h := sobWeight_rpow_mul_norm_primSeq_le s ψ n
    have h0 : 0 ≤ sobWeight n ^ (s + 1) * ‖primSeq ψ n‖ := by
      have := sobWeight_pos n; positivity
    nlinarith
  have hs : IsSobolevSeq (s + 1) (primSeq ψ) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hpt (hψ.mul_left 4)
  refine ⟨hs, ?_⟩
  rw [sobNormSq, sobNormSq, ← tsum_mul_left]
  exact Summable.tsum_le_tsum hpt hs (hψ.mul_left 4)

/-- On `[a, b]`, the Fourier coefficients of a closed primitive: if `Ψ' = ψ` and
`Ψ(b) = Ψ(a)`, then `Ψ̂(n) = (b - a) ψ̂(n) / (2π i n)` for `n ≠ 0`. For `b - a = 2π` this is
`primSeq` applied to the coefficients of `ψ`. -/
theorem fourierCoeffOn_primitive {a b : ℝ} (hab : a < b) {Ψ ψ : ℝ → ℂ}
    (hd : ∀ x ∈ Set.uIcc a b, HasDerivAt Ψ (ψ x) x)
    (hi : IntervalIntegrable ψ MeasureTheory.volume a b) (hper : Ψ b = Ψ a) {n : ℤ}
    (hn : n ≠ 0) :
    fourierCoeffOn hab Ψ n = (b - a) / (2 * Real.pi) * primSeq (fourierCoeffOn hab ψ) n := by
  rw [fourierCoeffOn_of_hasDerivAt hab hn hd hi, hper, sub_self, mul_zero, zero_sub, primSeq]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  field_simp

/-- **Lemma 5.2 on the Fourier side (primitive bound).** Let the coefficient `a` (in the paper,
the Fourier coefficients of `conj γ'` in conformal coordinates) satisfy `∑ₖ λₖ^s |aₖ| < ∞`,
`s ≥ 0`, and let `h ∈ H^s`. Then the Fourier primitive of the product `a·h`, with coefficients
`(a ⋆ h)ₙ / (i n)`, lies in `H^{s+1}` and
`‖primitive‖_{H^{s+1}} ≤ 2 (∑ₖ λₖ^s |aₖ|) ‖h‖_{H^s}`. -/
theorem sobNormSq_primSeq_seqConv_le {s : ℝ} (hs : 0 ≤ s) {a h : ℤ → ℂ} (ha : IsWL1 s a)
    (hh : IsSobolevSeq s h) :
    IsSobolevSeq (s + 1) (primSeq (seqConv a h)) ∧
      sobNormSq (s + 1) (primSeq (seqConv a h)) ≤ 4 * wl1Norm s a ^ 2 * sobNormSq s h := by
  obtain ⟨-, h1, h2⟩ := sobNormSq_seqConv_le hs ha hh
  obtain ⟨h3, h4⟩ := sobNormSq_primSeq_le s h1
  refine ⟨h3, h4.trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h2 (by norm_num)

/-! ### Products of functions are convolutions of coefficients -/

open MeasureTheory in
/-- **Fourier coefficients of a product.** If `c` is continuous on the circle with absolutely
summable Fourier coefficients and `φ` is integrable, then `(cφ)^(n) = ∑ₖ ĉ(k) φ̂(n - k)`, i.e.
the coefficient sequence of `cφ` is `seqConv ĉ φ̂`. -/
theorem fourierCoeff_mul_hasSum {T : ℝ} [Fact (0 < T)] (c : C(AddCircle T, ℂ))
    (hc : Summable (fourierCoeff c)) {φ : AddCircle T → ℂ}
    (hφ : Integrable φ AddCircle.haarAddCircle) (n : ℤ) :
    HasSum (fun k => fourierCoeff c k * fourierCoeff φ (n - k))
      (fourierCoeff (fun x => c x * φ x) n) := by
  have hint : ∀ ψ : C(AddCircle T, ℂ),
      Integrable (fun t => fourier (-n) t * (ψ t * φ t)) AddCircle.haarAddCircle := by
    intro ψ
    have h1 : Integrable (fun t => ψ t * φ t) AddCircle.haarAddCircle :=
      hφ.bdd_mul ψ.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => ψ.norm_coe_le_norm t)
    exact h1.bdd_mul (c := 1) (fourier (-n)).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by simp)
  let Lin : C(AddCircle T, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => ∫ t, fourier (-n) t * (ψ t * φ t) ∂AddCircle.haarAddCircle
      map_add' := fun ψ χ => by
        rw [← integral_add (hint ψ) (hint χ)]
        congr 1; ext t; simp; ring
      map_smul' := fun a ψ => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        congr 1; ext t; simp; ring }
  let L : C(AddCircle T, ℂ) →L[ℂ] ℂ := Lin.mkContinuous (∫ t, ‖φ t‖ ∂AddCircle.haarAddCircle)
    (fun ψ => by
      change ‖∫ t, fourier (-n) t * (ψ t * φ t) ∂AddCircle.haarAddCircle‖ ≤ _
      calc _ ≤ ∫ t, ‖fourier (-n) t * (ψ t * φ t)‖ ∂AddCircle.haarAddCircle :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ t, ‖ψ‖ * ‖φ t‖ ∂AddCircle.haarAddCircle := by
            refine integral_mono (hint ψ).norm (hφ.norm.const_mul _) fun t => ?_
            simp only [norm_mul]
            rw [show ‖fourier (-n) t‖ = 1 by simp, one_mul]
            exact mul_le_mul_of_nonneg_right (ψ.norm_coe_le_norm t) (norm_nonneg _)
        _ = _ := by rw [integral_const_mul]; ring)
  have hs := (hasSum_fourier_series_of_summable hc).mapL L
  have e1 : L c = fourierCoeff (fun x => c x * φ x) n := by
    change ∫ t, fourier (-n) t * (c t * φ t) ∂AddCircle.haarAddCircle = _
    rfl
  rw [e1] at hs
  convert hs using 1
  ext k
  change _ = ∫ t, fourier (-n) t * ((fourierCoeff c k • fourier k) t * φ t)
    ∂AddCircle.haarAddCircle
  generalize fourierCoeff c k = a
  rw [fourierCoeff, ← integral_const_mul]
  congr 1; ext t
  have : fourier (-(n - k)) t = fourier (-n) t * fourier k t := by
    rw [← fourier_add]; ring_nf
  simp only [ContinuousMap.smul_apply, smul_eq_mul, this]
  ring

open MeasureTheory in
/-- In the notation of this file: the coefficient sequence of `cφ` is `seqConv ĉ φ̂`. -/
theorem fourierCoeff_mul_eq_seqConv {T : ℝ} [Fact (0 < T)] (c : C(AddCircle T, ℂ))
    (hc : Summable (fourierCoeff c)) {φ : AddCircle T → ℂ}
    (hφ : Integrable φ AddCircle.haarAddCircle) :
    fourierCoeff (fun x => c x * φ x) = seqConv (fourierCoeff c) (fourierCoeff φ) :=
  funext fun n => (fourierCoeff_mul_hasSum c hc hφ n).tsum_eq.symm

/-! ### Monotonicity and point evaluation -/

lemma sobNormSq_nonneg (s : ℝ) (f : ℤ → ℂ) : 0 ≤ sobNormSq s f :=
  tsum_nonneg fun _ => sq_nonneg _

lemma sobWeight_rpow_mono {s t : ℝ} (hst : s ≤ t) (n : ℤ) :
    sobWeight n ^ s ≤ sobWeight n ^ t :=
  Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) hst

/-- `H^t ⊆ H^s` for `s ≤ t`, with `‖f‖_{H^s} ≤ ‖f‖_{H^t}`. -/
theorem sobNormSq_mono {s t : ℝ} (hst : s ≤ t) {f : ℤ → ℂ} (hf : IsSobolevSeq t f) :
    IsSobolevSeq s f ∧ sobNormSq s f ≤ sobNormSq t f := by
  have hpt : ∀ n, (sobWeight n ^ s * ‖f n‖) ^ 2 ≤ (sobWeight n ^ t * ‖f n‖) ^ 2 := by
    intro n
    have h0 : 0 ≤ sobWeight n ^ s * ‖f n‖ := by have := sobWeight_pos n; positivity
    exact pow_le_pow_left₀ h0
      (mul_le_mul_of_nonneg_right (sobWeight_rpow_mono hst n) (norm_nonneg _)) 2
  have hs : IsSobolevSeq s f := Summable.of_nonneg_of_le (fun n => sq_nonneg _) hpt hf
  exact ⟨hs, Summable.tsum_le_tsum hpt hs hf⟩

/-- The constant `Z = ∑ₙ λₙ^{-2}` controlling point evaluation on `H^1`. -/
def evalConst : ℝ := ∑' n : ℤ, 1 / sobWeight n ^ 2

lemma summable_inv_sobWeight_sq : Summable fun n : ℤ => 1 / sobWeight n ^ 2 := by
  have h1 := Real.summable_abs_int_rpow (b := 2) (by norm_num)
  have h2 : Summable fun n : ℤ => if n = 0 then (1 : ℝ) else 0 :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by
      simp only [Finset.mem_singleton] at hn; simp [hn]
  refine Summable.of_nonneg_of_le (fun n => by have := sobWeight_pos n; positivity)
    (fun n => ?_) (h1.add h2)
  by_cases hn : n = 0
  · subst hn; simp [sobWeight]
  · have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
    simp only [hn, if_false, add_zero]
    rw [Real.rpow_neg (abs_nonneg _), Real.rpow_two, one_div]
    have : |(n : ℝ)| ≤ sobWeight n := by unfold sobWeight; linarith
    gcongr

/-- **Point evaluation on `H^{s+1}`, `s ≥ 0`.** The coefficients are absolutely summable and
`(∑ₙ |pₙ|)² ≤ Z ‖p‖²_{H^{s+1}}`, `Z = ∑ λₙ^{-2}`. -/
theorem sq_tsum_norm_le {s : ℝ} (hs : 0 ≤ s) {p : ℤ → ℂ} (hp : IsSobolevSeq (s + 1) p) :
    Summable (fun n => ‖p n‖) ∧ (∑' n, ‖p n‖) ^ 2 ≤ evalConst * sobNormSq (s + 1) p := by
  set w : ℤ → ℝ := fun n => sobWeight n ^ (s + 1) with hw
  have hw1 : ∀ n, 1 ≤ w n := fun n => Real.one_le_rpow (one_le_sobWeight n) (by linarith)
  have hw0 : ∀ n, 0 < w n := fun n => by linarith [hw1 n]
  have hwge : ∀ n, sobWeight n ≤ w n := fun n => by
    have := Real.rpow_le_rpow_of_exponent_le (one_le_sobWeight n) (by linarith : (1:ℝ) ≤ s + 1)
    simpa [hw] using this
  set C : ℤ → ℝ := fun n => 1 / w n ^ 2 with hC
  set G : ℤ → ℝ := fun n => w n ^ 2 * ‖p n‖ with hG
  have hC0 : ∀ n, 0 ≤ C n := fun n => by have := hw0 n; positivity
  have hG0 : ∀ n, 0 ≤ G n := fun n => by have := hw0 n; positivity
  have hCle : ∀ n, C n ≤ 1 / sobWeight n ^ 2 := fun n => by
    have := sobWeight_pos n
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ this.le (hwge n) 2)
  have hCs : Summable C := Summable.of_nonneg_of_le hC0 hCle summable_inv_sobWeight_sq
  have hCG : ∀ n, C n * G n = ‖p n‖ := fun n => by
    have := (hw0 n).ne'; simp only [hC, hG]; field_simp
  have hCG2 : ∀ n, C n * G n ^ 2 = (w n * ‖p n‖) ^ 2 := fun n => by
    have := (hw0 n).ne'; simp only [hC, hG]; field_simp
  have hcs := ennreal_tsum_cs (fun n => ENNReal.ofReal (C n)) (fun n => ENNReal.ofReal (G n))
  simp only [← ENNReal.ofReal_mul (hC0 _), ← ENNReal.ofReal_pow (hG0 _), hCG, hCG2] at hcs
  rw [← ENNReal.ofReal_tsum_of_nonneg hC0 hCs,
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hp] at hcs
  have hfin : ∑' n, ENNReal.ofReal ‖p n‖ ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.top_pow two_ne_zero] at hcs
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top (top_le_iff.mp hcs)
  have hps : Summable fun n => ‖p n‖ := by
    have := ENNReal.summable_toReal hfin
    simpa [ENNReal.toReal_ofReal (norm_nonneg _)] using this
  refine ⟨hps, ?_⟩
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) hps,
    ← ENNReal.ofReal_pow (tsum_nonneg fun n => norm_nonneg _),
    ← ENNReal.ofReal_mul (tsum_nonneg hC0)] at hcs
  have h0 : 0 ≤ evalConst * sobNormSq (s + 1) p :=
    mul_nonneg (tsum_nonneg fun n => by have := sobWeight_pos n; positivity)
      (sobNormSq_nonneg _ _)
  have h1 := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (tsum_nonneg hC0)
    (sobNormSq_nonneg _ _))).mp hcs
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (sobNormSq_nonneg _ _))
  exact Summable.tsum_le_tsum hCle hCs summable_inv_sobWeight_sq

end PolyaNeumann
