module

public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

/-!
# One-dimensional stretching maps (towards External theorem BZ)

For `T > 0` and `|b| ≤ T/2`, the piecewise linear map `σ_b(a) = a + b θ(a)`, with the tent
`θ(a) = max(0, 1 - |a|/T)`, is a bi-Lipschitz homeomorphism of `ℝ` with `σ_b(0) = b` that is the
identity outside `(-T, T)`. We record its inverse and Lipschitz bounds, uniform in `b`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

/-- The tent `θ(a) = max(0, 1 - |a|/T)`. -/
def tentθ (T a : ℝ) : ℝ := max 0 (1 - |a| / T)

/-- The stretching map `σ_b(a) = a + b θ(a)`. -/
def sigmaMap (T b a : ℝ) : ℝ := a + b * tentθ T a

variable {T : ℝ}

lemma tentθ_nonneg (a : ℝ) : 0 ≤ tentθ T a := le_max_left _ _

lemma tentθ_le_one (hT : 0 < T) (a : ℝ) : tentθ T a ≤ 1 :=
  max_le zero_le_one (by have : 0 ≤ |a| / T := by positivity
                         linarith)

lemma tentθ_eq_zero (hT : 0 < T) {a : ℝ} (ha : T ≤ |a|) : tentθ T a = 0 := by
  unfold tentθ
  refine max_eq_left ?_
  have : 1 ≤ |a| / T := by rw [le_div_iff₀ hT]; linarith
  linarith

lemma tentθ_zero : tentθ T 0 = 1 := by
  simp [tentθ]

lemma abs_tentθ_sub_le (hT : 0 < T) (a a' : ℝ) : |tentθ T a - tentθ T a'| ≤ |a - a'| / T := by
  unfold tentθ
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp; positivity) ?_)
  rw [show 1 - |a| / T - (1 - |a'| / T) = (|a'| - |a|) / T by ring, abs_div, abs_of_pos hT]
  exact div_le_div_of_nonneg_right
    (by rw [abs_sub_comm a a']; exact abs_abs_sub_abs_le_abs_sub a' a) hT.le

lemma continuous_tentθ (T : ℝ) : Continuous (tentθ T) := by
  unfold tentθ; fun_prop

variable {b b' : ℝ}

lemma continuous_sigmaMap (T b : ℝ) : Continuous (sigmaMap T b) := by
  unfold sigmaMap; exact continuous_id.add (continuous_const.mul (continuous_tentθ T))

lemma sigmaMap_zero : sigmaMap T b 0 = b := by
  simp [sigmaMap, tentθ_zero]

lemma sigmaMap_of_le_abs (hT : 0 < T) {a : ℝ} (ha : T ≤ |a|) : sigmaMap T b a = a := by
  simp [sigmaMap, tentθ_eq_zero hT ha]

/-- `σ_b` increases at rate at least `1/2`. -/
lemma sigmaMap_sub_ge (hT : 0 < T) (hb : |b| ≤ T / 2) {a a' : ℝ} (h : a' ≤ a) :
    (a - a') / 2 ≤ sigmaMap T b a - sigmaMap T b a' := by
  unfold sigmaMap
  have h1 := abs_tentθ_sub_le hT a a'
  have h2 : |b * (tentθ T a - tentθ T a')| ≤ (a - a') / 2 := by
    rw [abs_mul]
    calc |b| * |tentθ T a - tentθ T a'| ≤ (T / 2) * (|a - a'| / T) :=
          mul_le_mul hb h1 (abs_nonneg _) (by positivity)
      _ = (a - a') / 2 := by rw [abs_of_nonneg (by linarith)]; field_simp
  have := neg_abs_le (b * (tentθ T a - tentθ T a'))
  nlinarith

lemma sigmaMap_strictMono (hT : 0 < T) (hb : |b| ≤ T / 2) : StrictMono (sigmaMap T b) :=
  fun a' a h => by have := sigmaMap_sub_ge hT hb h.le; linarith

lemma abs_sigmaMap_sub_param (hT : 0 < T) (a : ℝ) :
    |sigmaMap T b a - sigmaMap T b' a| ≤ |b - b'| := by
  unfold sigmaMap
  rw [show a + b * tentθ T a - (a + b' * tentθ T a) = (b - b') * tentθ T a by ring, abs_mul,
    abs_of_nonneg (tentθ_nonneg a)]
  exact mul_le_of_le_one_right (abs_nonneg _) (tentθ_le_one hT a)

lemma abs_sigmaMap_lt (hT : 0 < T) (hb : |b| ≤ T / 2) {a : ℝ} (ha : |a| < T) :
    |sigmaMap T b a| < T := by
  have hm := sigmaMap_strictMono hT hb
  have h1 : sigmaMap T b (-T) = -T := sigmaMap_of_le_abs hT (by rw [abs_neg, abs_of_pos hT])
  have h2 : sigmaMap T b T = T := sigmaMap_of_le_abs hT (by rw [abs_of_pos hT])
  obtain ⟨ha1, ha2⟩ := abs_lt.mp ha
  have := hm ha1
  have := hm ha2
  rw [abs_lt]; constructor <;> linarith

lemma sigmaMap_pos (hT : 0 < T) (hb : |b| ≤ T / 2) (hb0 : 0 ≤ b) {a : ℝ} (ha : 0 < a) :
    0 < sigmaMap T b a := by
  have := sigmaMap_strictMono hT hb ha
  rw [sigmaMap_zero] at this; linarith

lemma existsUnique_sigmaMap_eq (hT : 0 < T) (hb : |b| ≤ T / 2) (w : ℝ) :
    ∃! a, sigmaMap T b a = w := by
  have hm := sigmaMap_strictMono hT hb
  refine existsUnique_of_exists_of_unique ?_ (fun a a' h1 h2 => hm.injective (h1.trans h2.symm))
  by_cases hw : T ≤ |w|
  · exact ⟨w, sigmaMap_of_le_abs hT hw⟩
  · push_neg at hw
    have h1 : sigmaMap T b (-T) = -T := sigmaMap_of_le_abs hT (by rw [abs_neg, abs_of_pos hT])
    have h2 : sigmaMap T b T = T := sigmaMap_of_le_abs hT (by rw [abs_of_pos hT])
    obtain ⟨a, -, ha⟩ := intermediate_value_Icc (show -T ≤ T by linarith)
      (continuous_sigmaMap T b).continuousOn
      (show w ∈ Set.Icc (sigmaMap T b (-T)) (sigmaMap T b T) by
        rw [h1, h2]; exact ⟨(abs_lt.mp hw).1.le, (abs_lt.mp hw).2.le⟩)
    exact ⟨a, ha⟩

open Classical in
/-- The inverse of `σ_b` (for `|b| ≤ T/2`; the identity otherwise). -/
def sigmaInv (T b w : ℝ) : ℝ :=
  if h : 0 < T ∧ |b| ≤ T / 2 then (existsUnique_sigmaMap_eq h.1 h.2 w).exists.choose else w

lemma sigmaMap_sigmaInv (hT : 0 < T) (hb : |b| ≤ T / 2) (w : ℝ) :
    sigmaMap T b (sigmaInv T b w) = w := by
  simp only [sigmaInv, dif_pos (And.intro hT hb)]
  exact (existsUnique_sigmaMap_eq hT hb w).exists.choose_spec

lemma sigmaInv_sigmaMap (hT : 0 < T) (hb : |b| ≤ T / 2) (a : ℝ) :
    sigmaInv T b (sigmaMap T b a) = a :=
  (sigmaMap_strictMono hT hb).injective (sigmaMap_sigmaInv hT hb _)

lemma sigmaInv_of_le_abs (hT : 0 < T) (hb : |b| ≤ T / 2) {w : ℝ} (hw : T ≤ |w|) :
    sigmaInv T b w = w := by
  conv_lhs => rw [← sigmaMap_of_le_abs (b := b) hT hw]
  exact sigmaInv_sigmaMap hT hb w

lemma abs_sigmaInv_lt (hT : 0 < T) (hb : |b| ≤ T / 2) {w : ℝ} (hw : |w| < T) :
    |sigmaInv T b w| < T := by
  by_contra h
  push_neg at h
  have := sigmaMap_of_le_abs (b := b) hT h
  rw [sigmaMap_sigmaInv hT hb] at this
  rw [this] at hw
  linarith

lemma sigmaInv_pos_iff (hT : 0 < T) (hb : |b| ≤ T / 2) (w : ℝ) :
    0 < sigmaInv T b w ↔ b < w := by
  have hm := sigmaMap_strictMono hT hb
  have h0 := sigmaMap_zero (T := T) (b := b)
  have h1 := sigmaMap_sigmaInv hT hb w
  constructor
  · intro h
    have := hm h
    rwa [h0, h1] at this
  · intro h
    by_contra hle
    push_neg at hle
    have := hm.monotone hle
    rw [h0, h1] at this
    linarith

lemma abs_sigmaInv_sub_le (hT : 0 < T) (hb : |b| ≤ T / 2) (hb' : |b'| ≤ T / 2) (w w' : ℝ) :
    |sigmaInv T b w - sigmaInv T b' w'| ≤ 2 * |w - w'| + 2 * |b - b'| := by
  set a := sigmaInv T b w
  set a' := sigmaInv T b' w'
  have hw : sigmaMap T b a = w := sigmaMap_sigmaInv hT hb w
  have hw' : sigmaMap T b' a' = w' := sigmaMap_sigmaInv hT hb' w'
  have h1 : |a - a'| / 2 ≤ |sigmaMap T b a - sigmaMap T b a'| := by
    rcases le_total a' a with h | h
    · have := sigmaMap_sub_ge hT hb h
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; exact this
    · have := sigmaMap_sub_ge hT hb h
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  have h2 := abs_sigmaMap_sub_param (b := b) (b' := b') hT a'
  have h3 : |sigmaMap T b a - sigmaMap T b a'| ≤ |w - w'| + |b - b'| := by
    calc |sigmaMap T b a - sigmaMap T b a'|
        = |(w - w') + (sigmaMap T b' a' - sigmaMap T b a')| := by rw [← hw, ← hw']; ring_nf
      _ ≤ |w - w'| + |sigmaMap T b' a' - sigmaMap T b a'| := abs_add_le _ _
      _ ≤ |w - w'| + |b - b'| := by rw [abs_sub_comm (sigmaMap T b' a')]; linarith
  linarith

end PolyaNeumann

end
