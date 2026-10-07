module

public import RequestProject.BZDist

/-!
# A transversal vector field (towards External theorem BZ)

For a bounded Lipschitz domain we glue the inward chart directions with a finite Lipschitz
partition into a bounded Lipschitz vector field `X` along which the signed distance increases at a
definite rate near the boundary (`exists_transversalField`):
`d_Ω(z) + κ t ≤ d_Ω(z + t X(z))` for `|d_Ω(z)| < r₀`, `0 ≤ t ≤ τ`.
-/

@[expose] public section

open Set Filter Metric
open scoped ComplexConjugate Real Topology

noncomputable section

namespace PolyaNeumann

/-- A segment from a point of `Ω` to a point outside meets the frontier. -/
lemma exists_frontier_mem_segment {Ω : Set ℂ} {a b : ℂ} (ha : a ∈ Ω) (hb : b ∉ Ω) :
    ∃ q ∈ frontier Ω, q ∈ segment ℝ a b := by
  by_contra hno
  push_neg at hno
  have hsub : segment ℝ a b ⊆ interior Ω ∪ (closure Ω)ᶜ := by
    intro q hq
    by_cases h1 : q ∈ interior Ω
    · exact Or.inl h1
    · right
      intro h2
      exact hno q ⟨h2, h1⟩ hq
  rcases (convex_segment a b).isPreconnected.subset_or_subset isOpen_interior
      isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset_closure) hsub with h | h
  · exact hb (interior_subset (h (right_mem_segment ℝ a b)))
  · exact h (left_mem_segment ℝ a b) (subset_closure ha)

/-- Points with small signed distance are close to the boundary. -/
lemma exists_frontier_near_of_abs_signedDist_lt {Ω : Set ℂ} (hΩne : Ω.Nonempty)
    (hΩu : Ωᶜ.Nonempty) {z : ℂ} {r : ℝ} (hz : |signedDist Ω z| < r) :
    ∃ q ∈ frontier Ω, ‖z - q‖ < r := by
  by_cases hzΩ : z ∈ Ω
  · rw [signedDist_of_mem hzΩ, abs_of_nonneg infDist_nonneg] at hz
    obtain ⟨y, hy, hzy⟩ := (infDist_lt_iff hΩu).mp hz
    obtain ⟨q, hq, hqs⟩ := exists_frontier_mem_segment hzΩ hy
    refine ⟨q, hq, ?_⟩
    have := segment_subset_closedBall_left z y hqs
    rw [mem_closedBall, dist_comm] at this
    rw [← dist_eq_norm]; linarith
  · rw [signedDist_of_notMem hzΩ, abs_neg, abs_of_nonneg infDist_nonneg] at hz
    obtain ⟨y, hy, hzy⟩ := (infDist_lt_iff hΩne).mp hz
    obtain ⟨q, hq, hqs⟩ := exists_frontier_mem_segment hy hzΩ
    refine ⟨q, hq, ?_⟩
    have := segment_subset_closedBall_right y z hqs
    rw [mem_closedBall, dist_comm y z, dist_comm q z] at this
    rw [← dist_eq_norm]; linarith

/-- Chaining increments along the summands of a convex-type combination. -/
lemma le_comp_add_sum {ι : Type*} (φ : ℂ → ℝ) (F : Finset ι) (w : ι → ℝ) (v : ι → ℂ)
    (κ : ℝ) (z : ℂ) {t : ℝ} (ht : 0 ≤ t) (hw : ∀ i ∈ F, 0 ≤ w i)
    (hstep : ∀ i ∈ F, 0 < w i → ∀ y : ℂ, ‖y - z‖ ≤ t * ∑ j ∈ F, w j * ‖v j‖ →
      φ y + κ * (t * w i) ≤ φ (y + ((t * w i : ℝ) : ℂ) * v i)) :
    φ z + κ * t * ∑ i ∈ F, w i ≤ φ (z + (t : ℂ) * ∑ i ∈ F, (w i : ℂ) * v i) := by
  classical
  have key : ∀ G ⊆ F, φ z + κ * t * ∑ i ∈ G, w i ≤
      φ (z + (t : ℂ) * ∑ i ∈ G, (w i : ℂ) * v i) := by
    intro G
    induction G using Finset.induction_on with
    | empty => intro _; simp
    | insert a G ha ih =>
      intro hGF
      have haF : a ∈ F := hGF (Finset.mem_insert_self a G)
      have hG : G ⊆ F := fun x hx => hGF (Finset.mem_insert_of_mem hx)
      have ih' := ih hG
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rcases (hw a haF).eq_or_lt with h0 | hpos
      · rw [← h0]; simpa using ih'
      set y := z + (t : ℂ) * ∑ i ∈ G, (w i : ℂ) * v i
      have hy : ‖y - z‖ ≤ t * ∑ j ∈ F, w j * ‖v j‖ := by
        simp only [y, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ht]
        refine mul_le_mul_of_nonneg_left ?_ ht
        refine (norm_sum_le _ _).trans ?_
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc ∑ i ∈ G, |w i| * ‖v i‖ = ∑ i ∈ G, w i * ‖v i‖ :=
              Finset.sum_congr rfl fun i hi => by rw [abs_of_nonneg (hw i (hG hi))]
          _ ≤ ∑ j ∈ F, w j * ‖v j‖ := Finset.sum_le_sum_of_subset_of_nonneg hG
              fun i hi _ => mul_nonneg (hw i hi) (norm_nonneg _)
      have hs := hstep a haF hpos y hy
      have heq : y + ((t * w a : ℝ) : ℂ) * v a =
          z + (t : ℂ) * ((w a : ℂ) * v a + ∑ i ∈ G, (w i : ℂ) * v i) := by
        simp only [y]; push_cast; ring
      rw [heq] at hs
      nlinarith
  exact key F (Finset.Subset.refl F)

/-- The Lipschitz bump `max(0, 1 - ‖z - p‖/s)`. -/
def tentBump (p : ℂ) (s : ℝ) (z : ℂ) : ℝ := max 0 (1 - ‖z - p‖ / s)

lemma tentBump_nonneg (p : ℂ) (s : ℝ) (z : ℂ) : 0 ≤ tentBump p s z := le_max_left _ _

lemma tentBump_le_one {p : ℂ} {s : ℝ} (hs : 0 < s) (z : ℂ) : tentBump p s z ≤ 1 :=
  max_le zero_le_one (by have : 0 ≤ ‖z - p‖ / s := by positivity
                         linarith)

lemma norm_sub_lt_of_tentBump_pos {p : ℂ} {s : ℝ} (hs : 0 < s) {z : ℂ}
    (h : 0 < tentBump p s z) : ‖z - p‖ < s := by
  unfold tentBump at h
  rcases lt_max_iff.mp h with h | h
  · exact absurd h (lt_irrefl 0)
  · have : ‖z - p‖ / s < 1 := by linarith
    rwa [div_lt_one hs] at this

lemma half_lt_tentBump {p : ℂ} {s : ℝ} (hs : 0 < s) {z : ℂ} (h : ‖z - p‖ < s / 2) :
    1 / 2 < tentBump p s z := by
  unfold tentBump
  refine lt_max_of_lt_right ?_
  have : ‖z - p‖ / s < 1 / 2 := by rw [div_lt_iff₀ hs]; linarith
  linarith

lemma abs_tentBump_sub_le {p : ℂ} {s : ℝ} (hs : 0 < s) (z y : ℂ) :
    |tentBump p s z - tentBump p s y| ≤ (1 / s) * ‖z - y‖ := by
  unfold tentBump
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp; positivity) ?_)
  have h1 : |(1 - ‖z - p‖ / s) - (1 - ‖y - p‖ / s)| = |‖y - p‖ - ‖z - p‖| / s := by
    rw [show (1 - ‖z - p‖ / s) - (1 - ‖y - p‖ / s) = (‖y - p‖ - ‖z - p‖) / s by ring,
      abs_div, abs_of_pos hs]
  rw [h1, div_eq_mul_inv, one_div, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := abs_norm_sub_norm_le (y - p) (z - p)
  rwa [show y - p - (z - p) = y - z by ring, norm_sub_rev y z] at this

/-- **Transversal vector field.** A bounded Lipschitz domain carries a bounded Lipschitz vector
field `X` such that, near the boundary, the signed distance increases along `X` at a definite
rate. -/
theorem exists_transversalField {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hΩne : Ω.Nonempty) (hΩu : Ωᶜ.Nonempty) :
    ∃ (X : ℂ → ℂ) (LX : NNReal) (M r₀ τ κ : ℝ), LipschitzWith LX X ∧ (∀ z, ‖X z‖ ≤ M) ∧
      0 < r₀ ∧ 0 < τ ∧ 0 < κ ∧
      ∀ z, |signedDist Ω z| < r₀ → ∀ t, 0 ≤ t → t ≤ τ →
        signedDist Ω z + κ * t ≤ signedDist Ω (z + t * X z) := by
  classical
  have hΩo := hL.1.1
  obtain ⟨ρ, H, K, hρ, hH, -, hch⟩ := exists_uniform_charts hb hL
  choose! c f hcf using hch
  set R : ℝ := min ρ H / 10 with hR
  have hR0 : 0 < R := by positivity
  obtain ⟨T, hTsub, hTfin, hTcov⟩ :=
    finite_cover_balls_of_compact (frontier_isCompact hb) (show 0 < R / 16 by positivity)
  set F := hTfin.toFinset
  have hFsub : ∀ p ∈ F, p ∈ frontier Ω := fun p hp => hTsub (by simpa [F] using hp)
  set n : ℂ → ℂ := fun p => conj (c p) * Complex.I
  have hn1 : ∀ p ∈ F, ‖n p‖ = 1 := fun p hp => by
    simp [n, (hcf p (hFsub p hp)).1]
  set ψ : ℂ → ℂ → ℝ := fun p z => tentBump p (R / 2) z
  set X : ℂ → ℂ := fun z => ∑ p ∈ F, (ψ p z : ℂ) * n p
  set m : ℝ := (F.card : ℝ)
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hR2 : 0 < R / 2 := by positivity
  -- bound
  have hXb : ∀ z, ‖X z‖ ≤ m := by
    intro z
    refine (norm_sum_le _ _).trans ?_
    calc ∑ p ∈ F, ‖(ψ p z : ℂ) * n p‖ ≤ ∑ p ∈ F, (1 : ℝ) := Finset.sum_le_sum fun p hp => by
          rw [norm_mul, hn1 p hp, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (tentBump_nonneg _ _ _)]
          exact tentBump_le_one hR2 z
      _ = m := by simp [m]
  -- Lipschitz
  have hXl : LipschitzWith (Real.toNNReal (m * (1 / (R / 2)))) X := by
    refine LipschitzWith.of_dist_le_mul fun z y => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    have : X z - X y = ∑ p ∈ F, ((ψ p z - ψ p y : ℝ) : ℂ) * n p := by
      simp only [X, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      push_cast; ring
    rw [this]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ p ∈ F, ‖((ψ p z - ψ p y : ℝ) : ℂ) * n p‖
        ≤ ∑ p ∈ F, (1 / (R / 2)) * ‖z - y‖ := Finset.sum_le_sum fun p hp => by
          rw [norm_mul, hn1 p hp, mul_one, Complex.norm_real, Real.norm_eq_abs]
          exact abs_tentBump_sub_le hR2 z y
      _ = m * (1 / (R / 2)) * ‖z - y‖ := by simp [m]; ring
  set κ : ℝ := 1 / (2 * (K + 1))
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hκ0 : 0 < κ := by positivity
  set τ : ℝ := R / (2 * m + 2)
  have hτ0 : 0 < τ := by positivity
  refine ⟨X, _, m, R / 16, τ, κ / 2, hXl, hXb, by positivity, hτ0, by positivity, ?_⟩
  intro z hz t ht0 htτ
  obtain ⟨q, hq, hzq⟩ := exists_frontier_near_of_abs_signedDist_lt hΩne hΩu hz
  obtain ⟨p₀, hp₀T, hqp₀⟩ := mem_iUnion₂.mp (hTcov hq)
  have hp₀F : p₀ ∈ F := by simpa [F] using hp₀T
  have hzp₀ : ‖z - p₀‖ < R / 4 := by
    rw [mem_ball, dist_eq_norm] at hqp₀
    have : ‖z - p₀‖ ≤ ‖z - q‖ + ‖q - p₀‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]; exact dist_triangle _ _ _
    linarith
  have hψ₀ : 1 / 2 < ψ p₀ z := half_lt_tentBump hR2 (by linarith)
  have hsum : 1 / 2 ≤ ∑ p ∈ F, ψ p z := by
    have := Finset.single_le_sum (f := fun p => ψ p z) (fun p _ => tentBump_nonneg _ _ _) hp₀F
    linarith
  have hτm : t * m ≤ R / 2 := by
    have : τ * m ≤ R / 2 := by
      simp only [τ]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hchain := le_comp_add_sum (signedDist Ω) F (fun p => ψ p z) n κ z ht0
    (fun p _ => tentBump_nonneg _ _ _) (by
      intro p hp hpos y hy
      have hzp : ‖z - p‖ < R / 2 := norm_sub_lt_of_tentBump_pos hR2 hpos
      have hyz : ‖y - z‖ ≤ R / 2 := by
        refine hy.trans ?_
        calc t * ∑ j ∈ F, ψ j z * ‖n j‖ ≤ t * m := by
              refine mul_le_mul_of_nonneg_left ?_ ht0
              calc ∑ j ∈ F, ψ j z * ‖n j‖ ≤ ∑ j ∈ F, (1 : ℝ) :=
                    Finset.sum_le_sum fun j hj => by
                      rw [hn1 j hj, mul_one]; exact tentBump_le_one hR2 z
                _ = m := by simp [m]
          _ ≤ R / 2 := hτm
      have hyp : ‖y - p‖ < min ρ H / 10 := by
        have : ‖y - p‖ ≤ ‖y - z‖ + ‖z - p‖ := by
          rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]; exact dist_triangle _ _ _
        rw [← hR]; linarith
      have htw0 : 0 ≤ t * ψ p z := mul_nonneg ht0 (tentBump_nonneg _ _ _)
      have htw : t * ψ p z ≤ min ρ H / 10 := by
        have h1 : t * ψ p z ≤ t := mul_le_of_le_one_right ht0 (tentBump_le_one hR2 z)
        have h2 : τ ≤ R := by
          simp only [τ]; rw [div_le_iff₀ (by positivity)]; nlinarith
        rw [← hR]; linarith
      have := signedDist_add_le_of_chart hΩo hΩne hΩu (hcf p (hFsub p hp)) (hFsub p hp) hyp
        htw0 htw
      convert this using 2
      simp only [κ]; ring)
  have : κ / 2 * t ≤ κ * t * ∑ p ∈ F, ψ p z := by
    nlinarith [mul_nonneg (mul_nonneg hκ0.le ht0) (sub_nonneg.mpr hsum)]
  simp only [X] at hchain ⊢
  linarith

end PolyaNeumann

end
