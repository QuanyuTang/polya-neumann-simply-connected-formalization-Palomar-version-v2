module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

/-!
# Flows of bounded Lipschitz vector fields on short times (towards External theorem BZ)

For a bounded Lipschitz vector field `X` on `ℂ` we construct (by Picard–Lindelöf) a flow
`Φ : ℝ → ℂ → ℂ` on the time interval `(-3, 3)` and prove the elementary estimates used in the
construction of the Ball–Zarnescu maps: the group law on short times, the speed bound
`‖Φ_t x - Φ_s x‖ ≤ M |t - s|`, the Grönwall bound `‖Φ_t x - Φ_t y‖ ≤ e^{L|t|} ‖x - y‖`, and the
second-order bound `‖Φ_t x - x - t X(x)‖ ≤ L M t²`.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal

noncomputable section

namespace PolyaNeumann

/-- `Φ` is a flow of `X` on the time interval `(-3, 3)`. -/
structure IsShortFlow (X : ℂ → ℂ) (Φ : ℝ → ℂ → ℂ) : Prop where
  zero : ∀ x, Φ 0 x = x
  deriv : ∀ x, ∀ t ∈ Ioo (-3 : ℝ) 3, HasDerivAt (fun s => Φ s x) (X (Φ t x)) t

/-- Existence of the short-time flow of a bounded Lipschitz vector field. -/
theorem exists_isShortFlow {X : ℂ → ℂ} {LX : ℝ≥0} (hX : LipschitzWith LX X) {M : ℝ}
    (hM : ∀ z, ‖X z‖ ≤ M) : ∃ Φ, IsShortFlow X Φ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hsol : ∀ x : ℂ, ∃ α : ℝ → ℂ, α 0 = x ∧
      ∀ t ∈ Ioo (-3 : ℝ) 3, HasDerivAt α (X (α t)) t := by
    intro x
    have hPL : IsPicardLindelof (fun _ => X) (tmin := -3) (tmax := 3)
        ⟨0, by norm_num⟩ x ⟨3 * M, by positivity⟩ 0 ⟨M, hM0⟩ LX :=
      IsPicardLindelof.of_time_independent (fun y _ => hM y) hX.lipschitzOnWith
        (by change M * max (3 - (0:ℝ)) (0 - -3) ≤ 3 * M - 0; simp; linarith)
    obtain ⟨α, h0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨α, h0, fun t ht =>
      (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩
  choose α h0 hα using hsol
  exact ⟨fun t x => α x t, h0, fun x t ht => hα x t ht⟩

variable {X : ℂ → ℂ} {LX : ℝ≥0} {M : ℝ} {Φ : ℝ → ℂ → ℂ}

lemma IsShortFlow.continuousOn (hΦ : IsShortFlow X Φ) (x : ℂ) :
    ContinuousOn (fun s => Φ s x) (Ioo (-3 : ℝ) 3) :=
  fun t ht => (hΦ.deriv x t ht).continuousAt.continuousWithinAt

/-- Speed bound. -/
lemma IsShortFlow.norm_sub_le (hΦ : IsShortFlow X Φ) (hM : ∀ z, ‖X z‖ ≤ M) (x : ℂ) {s t : ℝ}
    (hs : s ∈ Ioo (-3 : ℝ) 3) (ht : t ∈ Ioo (-3 : ℝ) 3) :
    ‖Φ t x - Φ s x‖ ≤ M * |t - s| := by
  have := (convex_Ioo (-3 : ℝ) 3).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u => Φ u x) (fun u hu => (hΦ.deriv x u hu).hasDerivWithinAt)
    (fun u _ => hM _) hs ht
  simpa [Real.norm_eq_abs] using this

lemma IsShortFlow.norm_sub_self_le (hΦ : IsShortFlow X Φ) (hM : ∀ z, ‖X z‖ ≤ M) (x : ℂ) {t : ℝ}
    (ht : t ∈ Ioo (-3 : ℝ) 3) : ‖Φ t x - x‖ ≤ M * |t| := by
  have := hΦ.norm_sub_le hM x (s := 0) (by norm_num) ht
  rwa [hΦ.zero, sub_zero] at this

/-- Group law on short times. -/
lemma IsShortFlow.add (hΦ : IsShortFlow X Φ) (hX : LipschitzWith LX X) (x : ℂ) {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-1 : ℝ) 1) : Φ s (Φ t x) = Φ (s + t) x := by
  have h1 : ∀ u ∈ Ioo (-2 : ℝ) 2, HasDerivAt (fun u => Φ u (Φ t x)) (X (Φ u (Φ t x))) u ∧
      Φ u (Φ t x) ∈ (univ : Set ℂ) := fun u hu =>
    ⟨hΦ.deriv _ u ⟨by linarith [hu.1], by linarith [hu.2]⟩, trivial⟩
  have h2 : ∀ u ∈ Ioo (-2 : ℝ) 2, HasDerivAt (fun u => Φ (u + t) x) (X (Φ (u + t) x)) u ∧
      Φ (u + t) x ∈ (univ : Set ℂ) := fun u hu =>
    ⟨(hΦ.deriv x (u + t) ⟨by linarith [hu.1, ht.1], by linarith [hu.2, ht.2]⟩).comp_add_const
      u t, trivial⟩
  have := ODE_solution_unique_of_mem_Ioo (v := fun _ => X) (s := fun _ => univ) (K := LX)
    (fun _ _ => hX.lipschitzOnWith) (t₀ := 0) (by norm_num) h1 h2 (by simp [hΦ.zero])
  exact this hs

/-- Grönwall bound for the dependence on the initial point. -/
lemma IsShortFlow.dist_le (hΦ : IsShortFlow X Φ) (hX : LipschitzWith LX X) (x y : ℂ) {t : ℝ}
    (ht : t ∈ Icc (-2 : ℝ) 2) :
    dist (Φ t x) (Φ t y) ≤ dist x y * Real.exp (LX * |t|) := by
  rcases le_total 0 t with h0 | h0
  · have hsub : Icc 0 t ⊆ Ioo (-3 : ℝ) 3 := fun u hu =>
      ⟨by linarith [hu.1], by linarith [hu.2, ht.2]⟩
    have := dist_le_of_trajectories_ODE (v := fun _ => X) (K := LX) (fun _ => hX)
      (f := fun u => Φ u x) (g := fun u => Φ u y) (a := 0) (b := t) (δ := dist x y)
      ((hΦ.continuousOn x).mono hsub)
      (fun u hu => (hΦ.deriv x u (hsub (Ico_subset_Icc_self hu))).hasDerivWithinAt)
      ((hΦ.continuousOn y).mono hsub)
      (fun u hu => (hΦ.deriv y u (hsub (Ico_subset_Icc_self hu))).hasDerivWithinAt)
      (by simp [hΦ.zero]) t ⟨h0, le_rfl⟩
    simpa [abs_of_nonneg h0] using this
  · have hsub : ∀ u ∈ Icc 0 (-t), -u ∈ Ioo (-3 : ℝ) 3 := fun u hu =>
      ⟨by linarith [hu.2, ht.1], by linarith [hu.1]⟩
    have hd : ∀ z, ∀ u ∈ Icc 0 (-t), HasDerivAt (fun u => Φ (-u) z) (-X (Φ (-u) z)) u :=
      fun z u hu => by
        have := (hΦ.deriv z (-u) (hsub u hu)).scomp u (hasDerivAt_neg u)
        simpa [Function.comp_def] using this
    have hlip : ∀ _ : ℝ, LipschitzWith LX (fun z => -X z) := fun _ => by
      simpa [Function.comp_def] using (LipschitzWith.id.neg (α := ℂ)).comp hX |>.weaken (by simp)
    have := dist_le_of_trajectories_ODE (v := fun _ z => -X z) (K := LX) hlip
      (f := fun u => Φ (-u) x) (g := fun u => Φ (-u) y) (a := 0) (b := -t) (δ := dist x y)
      (fun u hu => (hd x u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hd x u (Ico_subset_Icc_self hu)).hasDerivWithinAt)
      (fun u hu => (hd y u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hd y u (Ico_subset_Icc_self hu)).hasDerivWithinAt)
      (by simp [hΦ.zero]) (-t) ⟨by linarith, le_rfl⟩
    simpa [abs_of_nonpos h0] using this

/-- Second-order bound: `‖Φ_t x - x - t X(x)‖ ≤ L M t²`. -/
lemma IsShortFlow.norm_sub_sub_le (hΦ : IsShortFlow X Φ) (hX : LipschitzWith LX X)
    (hM : ∀ z, ‖X z‖ ≤ M) (x : ℂ) {t : ℝ} (ht : t ∈ Ioo (-3 : ℝ) 3) :
    ‖Φ t x - x - t * X x‖ ≤ LX * M * t ^ 2 := by
  have hsub : uIcc 0 t ⊆ Ioo (-3 : ℝ) 3 := by
    intro u hu
    rcases le_total 0 t with h | h
    · rw [uIcc_of_le h] at hu; exact ⟨by linarith [hu.1, ht.1], by linarith [hu.2, ht.2]⟩
    · rw [uIcc_of_ge h] at hu; exact ⟨by linarith [hu.1, ht.1], by linarith [hu.2, ht.2]⟩
  have hd : ∀ u ∈ uIcc 0 t, HasDerivWithinAt (fun u => Φ u x - u * X x)
      (X (Φ u x) - X x) (uIcc 0 t) u := fun u hu => by
    have h1 := hΦ.deriv x u (hsub hu)
    have h2 : HasDerivAt (fun u : ℝ => (u : ℂ) * X x) (X x) u := by
      simpa using ((hasDerivAt_id u).ofReal_comp).mul_const (X x)
    exact (h1.sub h2).hasDerivWithinAt
  have hb : ∀ u ∈ uIcc 0 t, ‖X (Φ u x) - X x‖ ≤ LX * M * |t| := fun u hu => by
    have h1 : ‖X (Φ u x) - X x‖ ≤ LX * ‖Φ u x - x‖ := by
      rw [← dist_eq_norm, ← dist_eq_norm]; exact hX.dist_le_mul _ _
    have h2 := hΦ.norm_sub_self_le hM x (hsub hu)
    have h3 : |u| ≤ |t| := by
      rcases le_total 0 t with h | h
      · rw [uIcc_of_le h] at hu
        rw [abs_of_nonneg hu.1, abs_of_nonneg h]; exact hu.2
      · rw [uIcc_of_ge h] at hu
        rw [abs_of_nonpos hu.2, abs_of_nonpos h]; linarith [hu.1]
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    calc ‖X (Φ u x) - X x‖ ≤ LX * (M * |u|) := h1.trans (by gcongr)
      _ ≤ LX * M * |t| := by rw [← mul_assoc]; gcongr
  have := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    left_mem_uIcc right_mem_uIcc
  simp only [hΦ.zero, Complex.ofReal_zero, zero_mul, sub_zero, Real.norm_eq_abs] at this
  calc ‖Φ t x - x - t * X x‖ = ‖Φ t x - t * X x - x‖ := by ring_nf
    _ ≤ LX * M * |t| * |t| := this
    _ = LX * M * t ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

end PolyaNeumann

end
