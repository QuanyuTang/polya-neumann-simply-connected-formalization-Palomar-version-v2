module

public import RequestProject.BZConstruct
public import RequestProject.SmoothDomain

/-!
# The collar homeomorphism (towards External theorem BZ)

For level data `D` (parameter `T`), the collar map `f = collarMap Φ C a b T` is a homeomorphism of
the plane (`BZLevelData.homeo`) with uniformly controlled bi-Lipschitz constants, which maps `Ω`
into itself, onto the smooth domain `f(Ω)` (`BZLevelData.isSmoothDomain_image`), is the identity
off `{|d_Ω| ≤ 2 M T}` and moves points by at most `M T / 2`.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal ContDiff

noncomputable section

namespace PolyaNeumann

namespace BZSetting

variable {Ω : Set ℂ} (S : BZSetting Ω)

/-- Uniform Lipschitz constant of the collar maps. -/
def K₁ : ℝ := S.M * (S.Lb + S.La / 2) + 1 / 2 + Real.exp S.LX

/-- Uniform Lipschitz constant of the inverse collar maps. -/
def K₂ : ℝ := S.M * (3 * S.La + 2 * S.Lb) + 1 / 2 + Real.exp S.LX

lemma K₁_nonneg : 0 ≤ S.K₁ := by
  have := S.M_pos; have := S.La_nonneg; have := S.Lb_nonneg; unfold K₁; positivity

lemma K₂_nonneg : 0 ≤ S.K₂ := by
  have := S.M_pos; have := S.La_nonneg; have := S.Lb_nonneg; unfold K₂; positivity

end BZSetting

namespace BZLevelData

variable {Ω : Set ℂ} {S : BZSetting Ω} (D : BZLevelData S)

lemma C_sub_U₁ {x : ℂ} (hx : x ∈ D.C) : x ∈ S.U₁ := by
  have hx' : |signedDist Ω x| < 4 * S.M * D.T := hx
  have := D.path_bound
  have := S.M_pos; have := D.T₁_pos
  show |signedDist Ω x| < S.r₀ / 2
  nlinarith

/-- Points of the collar lie above the level `ρ = ε` exactly when the crossing time is negative. -/
lemma lt_ρ_iff_s_neg {x : ℂ} (hx : x ∈ D.C) : D.ε < D.ρ x ↔ D.s x < 0 := by
  obtain ⟨hu, h0⟩ := D.cross_ρ_spec hx
  have hx' : |signedDist Ω x| < 4 * S.M * D.T := hx
  have hT1 := D.T₁_le
  have hκ : 0 < S.κ₀ / 2 := half_pos S.hκ₀
  have hpath : ∀ v, |v| ≤ D.T₁ → S.Φ v x ∈ S.U₁ := fun v hv =>
    D.flow_mem_U₁ hx' (by linarith [D.T₁_pos])
  rcases lt_trichotomy (D.s x) 0 with hneg | hzero | hpos
  · have := S.hΦ.lt_of_transversal S.hX S.hM D.lip S.hτ₀ hκ D.trans x
      (s := D.s x) (t := 0) (by linarith [hu.1]) hneg (by norm_num)
      (fun v hv => hpath v (abs_le.mpr ⟨by linarith [hv.1, hu.1], by linarith [hv.2, D.T₁_pos]⟩))
    rw [S.hΦ.zero, h0] at this
    constructor <;> intro _ <;> linarith
  · rw [hzero, S.hΦ.zero] at h0
    rw [h0, hzero]; simp
  · have := S.hΦ.lt_of_transversal S.hX S.hM D.lip S.hτ₀ hκ D.trans x
      (s := 0) (t := D.s x) (by norm_num) hpos (by linarith [hu.2])
      (fun v hv => hpath v (abs_le.mpr ⟨by linarith [hv.1, D.T₁_pos], by linarith [hv.2, hu.2]⟩))
    rw [S.hΦ.zero, h0] at this
    constructor <;> intro h <;> linarith

/-- The collar map. -/
def f : ℂ → ℂ := collarMap S.Φ D.C D.a D.b D.T

/-- The inverse collar map. -/
def g : ℂ → ℂ := collarMapInv S.Φ D.C D.a D.b D.T

lemma g_f (x : ℂ) : D.g (D.f x) = x :=
  IsFlowCollar.collarMapInv_collarMap S.hΦ S.hX D.isFlowCollar x

lemma f_g (y : ℂ) : D.f (D.g y) = y :=
  IsFlowCollar.collarMap_collarMapInv S.hΦ S.hX D.isFlowCollar y

lemma dist_f_le (x y : ℂ) : dist (D.f x) (D.f y) ≤ S.K₁ * dist x y := by
  have h := IsFlowCollar.collarMap_lipschitz S.hΦ S.hX S.hM D.isFlowCollar x y
  have e : S.M * ((S.Lb + S.La / 2) + (D.T / 2) / (S.M * D.T)) + Real.exp S.LX = S.K₁ := by
    have := S.M_pos.ne'; have := D.T_pos.ne'
    unfold BZSetting.K₁; field_simp
  rw [e] at h; exact h

lemma dist_g_le (x y : ℂ) : dist (D.g x) (D.g y) ≤ S.K₂ * dist x y := by
  have h := IsFlowCollar.collarMapInv_lipschitz S.hΦ S.hX S.hM D.isFlowCollar x y
  have e : S.M * ((3 * S.La + 2 * S.Lb) + (D.T / 2) / (S.M * D.T)) + Real.exp S.LX = S.K₂ := by
    have := S.M_pos.ne'; have := D.T_pos.ne'
    unfold BZSetting.K₂; field_simp
  rw [e] at h; exact h

lemma lipschitzWith_f : LipschitzWith (Real.toNNReal S.K₁) D.f :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.coe_toNNReal _ S.K₁_nonneg]; exact D.dist_f_le x y

lemma lipschitzWith_g : LipschitzWith (Real.toNNReal S.K₂) D.g :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.coe_toNNReal _ S.K₂_nonneg]; exact D.dist_g_le x y

/-- The collar homeomorphism. -/
def homeo : ℂ ≃ₜ ℂ where
  toFun := D.f
  invFun := D.g
  left_inv := D.g_f
  right_inv := D.f_g
  continuous_toFun := D.lipschitzWith_f.continuous
  continuous_invFun := D.lipschitzWith_g.continuous

lemma coe_homeo : (D.homeo : ℂ → ℂ) = D.f := rfl

lemma coe_homeo_symm : (D.homeo.symm : ℂ → ℂ) = D.g := rfl

lemma f_eq_self {x : ℂ} (hx : 2 * S.M * D.T < |signedDist Ω x|) : D.f x = x := by
  have h0 : collarShift D.C D.a D.b D.T x = 0 := by
    refine D.isFlowCollar.collarShift_eq_zero ?_
    by_cases hC : x ∈ D.C
    · right
      have h1 := D.abs_d_le hC
      have hM := S.M_pos
      by_contra hlt
      push_neg at hlt
      have : S.M * |D.a x| ≤ S.M * D.T := mul_le_mul_of_nonneg_left hlt.le hM.le
      linarith
    · left; exact hC
  simp only [f, collarMap, h0, S.hΦ.zero]

lemma norm_f_sub_le (x : ℂ) : ‖D.f x - x‖ ≤ S.M * (D.T / 2) := by
  have hu := D.isFlowCollar.abs_collarShift_le x
  have hT := D.T_lt
  have := S.hΦ.norm_sub_self_le S.hM x (t := collarShift D.C D.a D.b D.T x)
    ⟨by linarith [(abs_le.mp hu).1], by linarith [(abs_le.mp hu).2]⟩
  exact this.trans (mul_le_mul_of_nonneg_left hu S.M_pos.le)

lemma f_mem (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty) {x : ℂ} (hx : x ∈ Ω) : D.f x ∈ Ω := by
  have hc := D.isFlowCollar
  by_cases h : x ∈ D.C ∧ |D.a x| < D.T
  · obtain ⟨hxC, hax⟩ := h
    have hT := D.T_pos
    set u := collarShift D.C D.a D.b D.T x
    have hu : |u| ≤ D.T / 2 := hc.abs_collarShift_le x
    have hueq : u = D.b x * tentθ D.T (D.a x) := by simp [u, collarShift, hxC]
    obtain ⟨hyC, hya, -⟩ := hc.flow x hxC hax u (by linarith)
    have hpos := (D.mem_iff_a_pos hΩo hΩu hxC).mp hx
    have hb := D.b_mem hxC
    have hσ : 0 < sigmaMap D.T (D.b x) (D.a x) :=
      sigmaMap_pos hT (hc.b_le x hxC) hb.1 hpos
    show S.Φ u x ∈ Ω
    rw [D.mem_iff_a_pos hΩo hΩu hyC, hya, hueq]
    exact hσ
  · have h0 : collarShift D.C D.a D.b D.T x = 0 := hc.collarShift_eq_zero (by
      by_cases h' : x ∈ D.C
      · exact Or.inr (by push_neg at h; exact h h')
      · exact Or.inl h')
    simp only [f, collarMap, h0, S.hΦ.zero]; exact hx

lemma mem_image_iff (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty) {w : ℂ} (hw : w ∈ D.C)
    (haw : |D.a w| < D.T) : w ∈ D.f '' Ω ↔ D.ε < D.ρ w := by
  have hc := D.isFlowCollar
  have h1 : w ∈ D.f '' Ω ↔ D.g w ∈ Ω := by
    constructor
    · rintro ⟨x, hx, rfl⟩; rwa [D.g_f]
    · intro h; exact ⟨D.g w, h, D.f_g w⟩
  obtain ⟨hgC, hga⟩ := hc.a_collarMapInv hw haw
  rw [h1, show D.g w = collarMapInv S.Φ D.C D.a D.b D.T w from rfl,
    D.mem_iff_a_pos hΩo hΩu hgC, hga, sigmaInv_pos_iff D.T_pos (hc.b_le w hw),
    D.lt_ρ_iff_s_neg hw]
  simp only [b]
  constructor <;> intro h <;> linarith

/-- The collar map sends boundary points into `Ω` (onto the level `ρ = ε`). -/
lemma f_mem_of_frontier (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty) {q : ℂ} (hq : q ∈ frontier Ω) :
    D.f q ∈ Ω := by
  have hT := D.T_pos
  have hM := S.M_pos
  have hd : signedDist Ω q = 0 := signedDist_eq_zero_of_frontier hΩo hq
  have hqC : q ∈ D.C := by
    show |signedDist Ω q| < 4 * S.M * D.T
    rw [hd, abs_zero]; positivity
  have haq : D.a q = 0 := by
    have := D.a_eq hqC (u := 0) ⟨by linarith [D.T₁_pos], D.T₁_pos.le⟩ (by rw [S.hΦ.zero]; exact hd)
    rw [this, neg_zero]
  have hshift : collarShift D.C D.a D.b D.T q = D.s q := by
    simp only [collarShift, if_pos hqC, haq, tentθ_zero, mul_one, b, zero_add]
  have hfq : D.f q = S.Φ (D.s q) q := by simp only [f, collarMap, hshift]
  have hρp : D.ρ (D.f q) = D.ε := by rw [hfq]; exact (D.cross_ρ_spec hqC).2
  have hε : D.ε = S.κ₀ * D.T / 24 := rfl
  have hc := D.close (D.f q)
  have hκ := S.hκ₀
  rw [← signedDist_pos_iff hΩo hΩu]
  rw [hρp, hε] at hc
  have := (abs_le.mp hc).2
  have : 0 < S.κ₀ * D.T := mul_pos hκ hT
  linarith

/-- The collar map sends `Ω̄` into `Ω`. -/
lemma f_mem_of_mem_closure (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty) {x : ℂ} (hx : x ∈ closure Ω) :
    D.f x ∈ Ω := by
  by_cases h : x ∈ Ω
  · exact D.f_mem hΩo hΩu h
  · exact D.f_mem_of_frontier hΩo hΩu ⟨hx, by rwa [hΩo.interior_eq]⟩

/-- The image `f(Ω)` is a smooth domain. -/
theorem isSmoothDomain_image (hΩ : IsDomain Ω) (hΩu : Ωᶜ.Nonempty) :
    IsSmoothDomain (D.f '' Ω) := by
  have hc := D.isFlowCollar
  have hT := D.T_pos
  have hM := S.M_pos
  have hLa := S.La_nonneg
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← D.coe_homeo]; exact D.homeo.isOpenMap _ hΩ.1
  · exact hΩ.2.image _ D.lipschitzWith_f.continuous.continuousOn
  intro p hp
  rw [← D.coe_homeo, ← Homeomorph.image_frontier] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rw [D.coe_homeo]
  have hd : signedDist Ω q = 0 := signedDist_eq_zero_of_frontier hΩ.1 hq
  have hqC : q ∈ D.C := by
    show |signedDist Ω q| < 4 * S.M * D.T
    rw [hd, abs_zero]; positivity
  have haq : D.a q = 0 := by
    have := D.a_eq hqC (u := 0) ⟨by linarith [D.T₁_pos], D.T₁_pos.le⟩ (by rw [S.hΦ.zero]; exact hd)
    rw [this, neg_zero]
  have hshift : collarShift D.C D.a D.b D.T q = D.s q := by
    simp only [collarShift, if_pos hqC, haq, tentθ_zero, mul_one, b, zero_add]
  have hfq : D.f q = S.Φ (D.s q) q := by simp only [f, collarMap, hshift]
  have hρp : D.ρ (D.f q) = D.ε := by rw [hfq]; exact (D.cross_ρ_spec hqC).2
  have hbq := D.b_mem hqC
  have hbs : D.b q = D.s q := by simp only [b, haq, zero_add]
  obtain ⟨hpC, hpa, -⟩ := hc.flow q hqC (by rw [haq, abs_zero]; exact hT) (D.s q)
    (by rw [← hbs, abs_of_nonneg hbq.1]; linarith [hbq.2])
  rw [← hfq] at hpC hpa
  rw [haq, zero_add, ← hbs] at hpa
  set R : ℝ := min (S.M * D.T) (D.T / (2 * S.La + 1))
  have hR : 0 < R := lt_min (by positivity) (by positivity)
  have hball : ∀ w ∈ ball (D.f q) R, w ∈ D.C ∧ |D.a w| < D.T := by
    intro w hw
    have hw' : ‖w - D.f q‖ < R := by rwa [mem_ball, dist_eq_norm] at hw
    have hR1 : R ≤ S.M * D.T := min_le_left _ _
    have hR2 : R ≤ D.T / (2 * S.La + 1) := min_le_right _ _
    have hdp := D.abs_d_le hpC
    rw [hpa, abs_of_nonneg hbq.1] at hdp
    have hwC : w ∈ D.C := by
      have h2 := (lipschitzWith_signedDist Ω).dist_le_mul w (D.f q)
      rw [Real.dist_eq, dist_eq_norm] at h2
      push_cast at h2
      have h3 := abs_sub_abs_le_abs_sub (signedDist Ω w) (signedDist Ω (D.f q))
      have : S.M * D.b q ≤ S.M * (D.T / 8) := mul_le_mul_of_nonneg_left hbq.2 hM.le
      show |signedDist Ω w| < 4 * S.M * D.T
      nlinarith
    refine ⟨hwC, ?_⟩
    have h4 := hc.a_lip w hwC (D.f q) hpC
    rw [hpa] at h4
    have h5 : S.La * ‖w - D.f q‖ ≤ S.La * R := mul_le_mul_of_nonneg_left hw'.le hLa
    have h6 : S.La * (D.T / (2 * S.La + 1)) ≤ D.T / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h7 : S.La * R ≤ S.La * (D.T / (2 * S.La + 1)) := mul_le_mul_of_nonneg_left hR2 hLa
    have h8 := abs_sub_abs_le_abs_sub (D.a w) (D.b q)
    rw [abs_of_nonneg hbq.1] at h8
    linarith [hbq.2]
  exact smoothChart_of_level D.smooth D.lip S.hX S.hτ₀ (half_pos S.hκ₀) D.trans hR
    (fun w hw => D.C_sub_U₁ (hball w hw).1) hρp
    (fun w hw => D.mem_image_iff hΩ.1 hΩu (hball w hw).1 (hball w hw).2)

end BZLevelData

end PolyaNeumann

end
