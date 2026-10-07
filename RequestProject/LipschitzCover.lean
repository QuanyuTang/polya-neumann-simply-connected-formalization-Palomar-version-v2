module

public import RequestProject.Defs

/-!
# A cover of a bounded Lipschitz domain by shiftable pieces

A bounded Lipschitz domain `Ω` is covered by finitely many open sets `W_j ⊆ Ω` such that, for
every `η > 0`, each `W_j` admits a closed ball `B̄(a_j, r_j)` with `‖a_j‖ + r_j ≤ η` of
admissible shifts: all segments `t - s z` (`t ∈ W_j`, `z ∈ B̄(a_j, r_j)`, `0 ≤ s ≤ 1`) stay in
`Ω`. Near the boundary the shifts point into the domain, inside a cone around the inward
direction of a Lipschitz chart; away from the boundary any small shift works.
-/

@[expose] public section

open Filter Topology Metric Set

noncomputable section

namespace PolyaNeumann

/-- The segment condition in a Lipschitz chart: in the box of half the chart size, every shift
in a small ball around `δ` times the inward normal direction keeps the domain. -/
lemma chart_segment {Ω : Set ℂ} {p c : ℂ} {r h : ℝ} {K : NNReal} {f : ℝ → ℝ}
    (hc : ‖c‖ = 1) (hf : LipschitzWith K f)
    (hΩ : ∀ w : ℂ, |(c * (w - p)).re| < r → |(c * (w - p)).im| < h →
      (w ∈ Ω ↔ f (c * (w - p)).re < (c * (w - p)).im))
    {δ : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hδh : δ ≤ h / 3)
    {t : ℂ} (ht : t ∈ Ω) (htX : |(c * (t - p)).re| < r / 2) (htY : |(c * (t - p)).im| < h / 2)
    {z : ℂ} (hz : z ∈ closedBall (-(starRingEnd ℂ c) * Complex.I * δ) (δ / (2 * (K + 1))))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    t - s • z ∈ Ω := by
  set a : ℂ := -(starRingEnd ℂ c) * Complex.I * δ
  set r' : ℝ := δ / (2 * (K + 1))
  have hK0 : (0 : ℝ) ≤ K := K.2
  have hr'0 : 0 ≤ r' := by positivity
  have hr'δ : ((K : ℝ) + 1) * r' = δ / 2 := by
    simp only [r']; field_simp
  have hr'2 : r' ≤ δ / 2 := by nlinarith
  set e : ℂ := c * (z - a)
  have he : ‖e‖ ≤ r' := by
    simp only [e, norm_mul, hc, one_mul]; rw [← dist_eq_norm]; exact hz
  have hcc : c * (starRingEnd ℂ c) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; norm_num
  have hcz : c * z = -Complex.I * δ + e := by
    simp only [e, a]
    linear_combination (-(Complex.I * δ)) * hcc
  have hζ : c * (t - s • z - p) = c * (t - p) + s * (Complex.I * δ - e) := by
    rw [Complex.real_smul]
    linear_combination (-(s:ℂ)) * hcz
  set X := (c * (t - p)).re
  set Y := (c * (t - p)).im
  have hX' : (c * (t - s • z - p)).re = X - s * e.re := by
    rw [hζ]; simp [X]; ring
  have hY' : (c * (t - s • z - p)).im = Y + s * (δ - e.im) := by
    rw [hζ]; simp [Y]
  have hre : |e.re| ≤ r' := (Complex.abs_re_le_norm e).trans he
  have him : |e.im| ≤ r' := (Complex.abs_im_le_norm e).trans he
  obtain ⟨hs0, hs1⟩ := hs
  have hfX : f X < Y := (hΩ t (by linarith [abs_nonneg X]) (by linarith [abs_nonneg Y])).mp ht
  have hsre : |s * e.re| ≤ s * r' := by
    rw [abs_mul, abs_of_nonneg hs0]; exact mul_le_mul_of_nonneg_left hre hs0
  have hsr : s * r' ≤ r' := mul_le_of_le_one_left hr'0 hs1
  have hXa := abs_le.mp hsre
  have hXb := abs_lt.mp htX
  have hYb := abs_lt.mp htY
  have heim := abs_le.mp him
  have hd1 : 0 ≤ δ - e.im := by linarith
  have hd2 : δ - e.im ≤ 3 * δ / 2 := by linarith
  have hsd1 : 0 ≤ s * (δ - e.im) := mul_nonneg hs0 hd1
  have hsd2 : s * (δ - e.im) ≤ 3 * δ / 2 := (mul_le_of_le_one_left hd1 hs1).trans hd2
  have hmemX : |X - s * e.re| < r := by
    rw [abs_lt]; constructor <;> linarith
  have hmemY : |Y + s * (δ - e.im)| < h := by
    rw [abs_lt]; constructor <;> linarith
  rw [hΩ _ (by rwa [hX']) (by rwa [hY']), hX', hY']
  have hlip : f (X - s * e.re) ≤ f X + K * (s * r') := by
    have h1 := hf.dist_le_mul (X - s * e.re) X
    rw [Real.dist_eq, Real.dist_eq] at h1
    have h2 : |X - s * e.re - X| ≤ s * r' := by simpa using hsre
    have h3 := (le_abs_self _).trans h1
    have h4 : (K : ℝ) * |X - s * e.re - X| ≤ K * (s * r') := mul_le_mul_of_nonneg_left h2 hK0
    linarith
  have hkey : (K : ℝ) * (s * r') ≤ s * (δ - e.im) := by
    have : (K : ℝ) * r' + r' = δ / 2 := by linarith
    have h5 : (K : ℝ) * r' ≤ δ - e.im := by linarith
    calc (K : ℝ) * (s * r') = s * (K * r') := by ring
      _ ≤ s * (δ - e.im) := mul_le_mul_of_nonneg_left h5 hs0
  linarith

/-- The cover, indexed by a finite type. -/
lemma lipschitz_cover_aux {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) :
    ∃ (ι : Type) (_ : Fintype ι) (W : ι → Set ℂ), (∀ j, IsOpen (W j)) ∧ (∀ j, W j ⊆ Ω) ∧
      Ω ⊆ ⋃ j, W j ∧ ∀ η > 0, ∀ j, ∃ a : ℂ, ∃ r > 0, ‖a‖ + r ≤ η ∧
        ∀ t ∈ W j, ∀ z ∈ closedBall a r, ∀ s ∈ Icc (0 : ℝ) 1, t - s • z ∈ Ω := by
  classical
  have hΩo : IsOpen Ω := hL.1.1
  choose! c r h K f hc hr hh hf _ _ hΩ using hL.2
  set O : ℂ → Set ℂ := fun p =>
    {w | |(c p * (w - p)).re| < r p / 2 ∧ |(c p * (w - p)).im| < h p / 2}
  have hOo : ∀ p, IsOpen (O p) := fun p => by
    have h1 : Continuous fun w : ℂ => |(c p * (w - p)).re| := by fun_prop
    have h2 : Continuous fun w : ℂ => |(c p * (w - p)).im| := by fun_prop
    exact (isOpen_lt h1 continuous_const).inter (isOpen_lt h2 continuous_const)
  have hfr : IsCompact (frontier Ω) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨T, hT⟩ := hfr.elim_finite_subcover (fun q : frontier Ω => O q) (fun q => hOo q)
    (fun p hp => mem_iUnion.mpr ⟨⟨p, hp⟩, by
      have h1 := hr p hp; have h2 := hh p hp
      simp [O, h1, h2]⟩)
  set K0 := closure Ω \ ⋃ q ∈ T, O q
  have hK0c : IsCompact K0 :=
    hb.isCompact_closure.diff (isOpen_biUnion fun q _ => hOo q)
  have hK0Ω : K0 ⊆ Ω := by
    intro x ⟨hx1, hx2⟩
    by_contra hx
    have : x ∈ frontier Ω := by
      rw [frontier, hΩo.interior_eq]; exact ⟨hx1, hx⟩
    exact hx2 (hT this)
  obtain ⟨δ0, hδ0, hδ0Ω⟩ := hK0c.exists_cthickening_subset_open hΩo hK0Ω
  let W : Option T → Set ℂ := fun j => match j with
    | none => thickening (δ0 / 2) K0
    | some q => Ω ∩ O q
  refine ⟨Option T, inferInstance, W, ?_, ?_, ?_, ?_⟩
  · rintro (_ | q)
    · exact isOpen_thickening
    · exact hΩo.inter (hOo _)
  · rintro (_ | q)
    · exact (thickening_subset_cthickening_of_le (by linarith) K0).trans hδ0Ω
    · exact inter_subset_left
  · intro x hx
    by_cases hxO : x ∈ ⋃ q ∈ T, O q
    · obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hxO
      exact mem_iUnion.mpr ⟨some ⟨q, hq⟩, hx, hxq⟩
    · exact mem_iUnion.mpr ⟨none, self_subset_thickening (by linarith) K0
        ⟨subset_closure hx, hxO⟩⟩
  · intro η hη j
    rcases j with _ | ⟨q, hq⟩
    · refine ⟨0, min (δ0 / 2) (η / 2), by positivity, ?_, ?_⟩
      · simp only [norm_zero, zero_add]
        exact (min_le_right _ _).trans (by linarith)
      · intro t ht z hz s hs
        obtain ⟨y, hy, hty⟩ := mem_thickening_iff.mp ht
        apply hδ0Ω
        apply thickening_subset_cthickening
        refine mem_thickening_iff.mpr ⟨y, hy, ?_⟩
        have hz' : ‖z‖ ≤ δ0 / 2 := by
          rw [mem_closedBall, dist_zero_right] at hz; exact hz.trans (min_le_left _ _)
        have hsz : ‖s • z‖ ≤ δ0 / 2 := by
          rw [norm_smul, Real.norm_of_nonneg hs.1]
          exact (mul_le_of_le_one_left (norm_nonneg _) hs.2).trans hz'
        calc dist (t - s • z) y ≤ dist t y + ‖s • z‖ := by
              rw [dist_eq_norm, dist_eq_norm]
              calc ‖t - s • z - y‖ = ‖(t - y) - s • z‖ := by congr 1; abel
                _ ≤ ‖t - y‖ + ‖s • z‖ := norm_sub_le _ _
          _ < δ0 / 2 + δ0 / 2 := by linarith
          _ = δ0 := by ring
    · have hqf : q.1 ∈ frontier Ω := q.2
      set δ := min (min (r q) (h q / 3)) (η / 2)
      have hδ : 0 < δ := lt_min (lt_min (hr _ hqf) (by linarith [hh _ hqf])) (by linarith)
      have hK0 : (0 : ℝ) ≤ K q := (K q).2
      refine ⟨-(starRingEnd ℂ (c q)) * Complex.I * δ, δ / (2 * (K q + 1)), by positivity, ?_, ?_⟩
      · have hn : ‖-(starRingEnd ℂ (c q)) * Complex.I * (δ : ℂ)‖ = δ := by
          rw [norm_mul, norm_mul, norm_neg, Complex.norm_conj, hc _ hqf, Complex.norm_I,
            Complex.norm_real, Real.norm_of_nonneg hδ.le]; ring
        rw [hn]
        have h1 : δ / (2 * (K q + 1)) ≤ δ / 2 := by
          apply div_le_div_of_nonneg_left hδ.le (by norm_num); linarith
        have h2 : δ ≤ η / 2 := min_le_right _ _
        linarith
      · rintro t ⟨htΩ, htX, htY⟩ z hz s hs
        exact chart_segment (hc _ hqf) (hf _ hqf) (hΩ _ hqf) hδ
          ((min_le_left _ _).trans (min_le_left _ _)) ((min_le_left _ _).trans (min_le_right _ _))
          htΩ htX htY hz hs

/-- **Cover of a bounded Lipschitz domain by shiftable pieces.** -/
theorem lipschitz_cover {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) :
    ∃ (m : ℕ) (W : Fin m → Set ℂ), (∀ j, IsOpen (W j)) ∧ (∀ j, W j ⊆ Ω) ∧
      Ω ⊆ ⋃ j, W j ∧ ∀ η > 0, ∀ j, ∃ a : ℂ, ∃ r > 0, ‖a‖ + r ≤ η ∧
        ∀ t ∈ W j, ∀ z ∈ closedBall a r, ∀ s ∈ Icc (0 : ℝ) 1, t - s • z ∈ Ω := by
  obtain ⟨ι, _, W, hWo, hWΩ, hcov, hsh⟩ := lipschitz_cover_aux hb hL
  set e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j => W (e.symm j), fun j => hWo _, fun j => hWΩ _, ?_,
    fun η hη j => hsh η hη _⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hx)
  exact mem_iUnion.mpr ⟨e i, by simpa using hi⟩

end PolyaNeumann

end
