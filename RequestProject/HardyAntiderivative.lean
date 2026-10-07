module

public import RequestProject.BoundaryTransmutation

/-!
# Conditional Hardy support for the Fourier antiderivative

If the multiplier coefficients have strictly negative support and the
input coefficients have nonpositive support, their convolution has zero
coefficients at every nonnegative frequency. Consequently the existing
normalized `antiPrim` preserves nonpositive support and its Fourier
derivative is the full convolution, including at frequency zero.

These are conditional coefficient statements. This file does not identify
the multiplier with a physical conformal boundary derivative, construct an
interior antiholomorphic extension, or establish Vekua endpoint identities.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

/-- A coefficient sequence supported on the nonpositive Fourier modes. -/
def IsNonpositiveFourierSupport (h : ℤ → ℂ) : Prop :=
  ∀ n, 0 < n → h n = 0

/-- A coefficient sequence supported on the strictly negative Fourier modes. -/
def IsStrictNegativeFourierSupport (a : ℤ → ℂ) : Prop :=
  ∀ n, 0 ≤ n → a n = 0

/-- A strictly negative multiplier and a nonpositive input have no
nonnegative convolution coefficients. Every summand is zero, so no
summability hypothesis is needed for this support statement. -/
theorem seqConv_eq_zero_of_strictNegative_nonpositive {a h : ℤ → ℂ}
    (ha : IsStrictNegativeFourierSupport a)
    (hh : IsNonpositiveFourierSupport h) {n : ℤ} (hn : 0 ≤ n) :
    seqConv a h n = 0 := by
  unfold seqConv
  calc
    (∑' k, a k * h (n - k)) = ∑' _ : ℤ, (0 : ℂ) := by
      apply tsum_congr
      intro k
      by_cases hk : 0 ≤ k
      · rw [ha k hk, zero_mul]
      · rw [hh (n - k) (by omega), mul_zero]
    _ = 0 := tsum_zero

/-- In particular, the product has zero mean, as required by a periodic
antiderivative. -/
theorem seqConv_zero_of_strictNegative_nonpositive {a h : ℤ → ℂ}
    (ha : IsStrictNegativeFourierSupport a)
    (hh : IsNonpositiveFourierSupport h) : seqConv a h 0 = 0 :=
  seqConv_eq_zero_of_strictNegative_nonpositive ha hh le_rfl

/-- The normalization changes only the constant coefficient and hence
preserves the nonpositive Fourier sector. -/
theorem antiPrim_nonpositive {a h : ℤ → ℂ}
    (ha : IsStrictNegativeFourierSupport a)
    (hh : IsNonpositiveFourierSupport h) :
    IsNonpositiveFourierSupport (antiPrim a h) := by
  intro n hn
  rw [antiPrim, if_neg (ne_of_gt hn), primSeq,
    seqConv_eq_zero_of_strictNegative_nonpositive ha hh hn.le, zero_div]

/-- The true Fourier derivative identity for the normalized primitive.
The zero-frequency case follows from the zero mean of the product. -/
theorem antiPrim_fourier_derivative {a h : ℤ → ℂ}
    (ha : IsStrictNegativeFourierSupport a)
    (hh : IsNonpositiveFourierSupport h) (n : ℤ) :
    (Complex.I * (n : ℂ)) * antiPrim a h n = seqConv a h n := by
  by_cases hn : n = 0
  · subst n
    rw [seqConv_zero_of_strictNegative_nonpositive ha hh]
    simp
  · rw [antiPrim, if_neg hn, primSeq]
    exact mul_div_cancel₀ _ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hn))

/-- Every iterated normalized primitive remains in the same Fourier sector. -/
theorem antiPrimIter_nonpositive {a h : ℤ → ℂ}
    (ha : IsStrictNegativeFourierSupport a)
    (hh : IsNonpositiveFourierSupport h) (j : ℕ) :
    IsNonpositiveFourierSupport (antiPrimIter a j h) := by
  induction j with
  | zero => exact hh
  | succ j ih =>
      change IsNonpositiveFourierSupport ((antiPrim a)^[j + 1] h)
      rw [Function.iterate_succ_apply']
      exact antiPrim_nonpositive ha ih

end PolyaNeumann

end
