module

public import RequestProject.LocalDirichletNormalBootstrap

/-! Genuine domain membership is retained with the actual elliptic chart.
The same datum and chart serve every finite derivative order. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann
open Set Metric Filter Complex MeasureTheory
open scoped Topology

theorem exists_riemannMapping_flattened_genuine_chart_h1 {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (d : smoothTraceTests) (c : ℂ) (hc : c ≠ 0)
      (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (K : NNReal) (a b : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < a ∧ 0 < b ∧
      (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
       let v := riemannMappingDirichletRemainder F d ∘ Ψ
       (∀ z : ℂ, |z.re| < a → |z.im| < b → (Ψ z ∈ Ω ↔ 0 < z.im)) ∧
       MapsTo Ψ (smoothDirichletClosedHalfBox a b) (closure Ω) ∧
       MapsTo Ψ (smoothDirichletHalfBox a b) Ω ∧
       ContinuousOn v (smoothDirichletClosedHalfBox a b) ∧
       ContDiffOn ℝ (⊤ : ℕ∞) v (smoothDirichletHalfBox a b) ∧
       (∀ x : ℝ, |x| < a → v (x : ℂ) = 0) ∧
       ∃ u : NeumannH1 (smoothDirichletHalfBox a b),
         (h1Value _ u : ℂ → ℂ) =ᵐ[volume.restrict (smoothDirichletHalfBox a b)] v ∧
         ∀ i : Fin 2, (h1Gradient _ i u : ℂ → ℂ)
           =ᵐ[volume.restrict (smoothDirichletHalfBox a b)] dirD v (coordDir i)) := by
  obtain ⟨d, u, hvcont, hvsmooth, hvzero, hu, hgu, _, _⟩ :=
    exists_riemannMapping_zero_boundary_poisson_problem hb hS hsc F hF hinj himage
  obtain ⟨c, hc, f, hf, K, a, b, hc₁, hLip, hf₀, ha, hb₀, hchart⟩ :=
    exists_smoothDomain_flattening_rectangle hS hp
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let V := smoothDirichletHalfBox (a / 2) (b / 2)
  let v := riemannMappingDirichletRemainder F d ∘ Ψ
  have hV : IsOpen V := isOpen_smoothDirichletHalfBox _ _
  have hmap : MapsTo Ψ V Ω := by
    intro z hz
    apply (hchart z (hz.1.trans (by linarith)) ?_).mpr hz.2.1
    rw [abs_of_pos hz.2.1]
    exact hz.2.2.trans (by linarith)
  have hclosed : MapsTo Ψ (smoothDirichletClosedHalfBox (a / 2) (b / 2)) (closure Ω) := by
    intro z hz
    have hzr : |z.re| < a := hz.1.trans_lt (by linarith)
    have hzi : |z.im| < b := by rw [abs_of_nonneg hz.2.1]; linarith [hz.2.2]
    rcases eq_or_lt_of_le hz.2.1 with heq | hpos
    · have hzreal : z = (z.re : ℂ) := by
        apply Complex.ext <;> simp [← heq]
      rw [hzreal]
      exact frontier_subset_closure
        (smoothDirichletGraphChart_mem_frontier hS.1.1 p c hc f hf.continuous hb₀ hchart hzr)
    · exact subset_closure ((hchart z hzr hzi).mpr hpos)
  have hvs : ContDiffOn ℝ (⊤ : ℕ∞) v V :=
    hvsmooth.comp (smoothDirichletGraphChart_contDiff p c hc hf).contDiffOn hmap
  have hvm : MemLp (riemannMappingDirichletRemainder F d) 2 (volume.restrict Ω) :=
    (Lp.memLp (h1Value Ω u)).ae_eq hu
  have hgm (i : Fin 2) : MemLp (dirD (riemannMappingDirichletRemainder F d) (coordDir i))
      2 (volume.restrict Ω) := (Lp.memLp (h1Gradient Ω i u)).ae_eq (hgu i)
  obtain ⟨hvm', hgm'⟩ := smoothDirichletGraphChart_pullback_memLp
    hS.1.1 hV p c hc hc₁ hf hLip (mapsTo_iff_image_subset.mp hmap) hvsmooth hvm hgm
  have hw := isWeakGradient_of_contDiffOn hV hvs hvm' hgm'
  refine ⟨d, c, hc, f, hf, K, a / 2, b / 2, hc₁, hLip, hf₀, by positivity,
    by positivity, ?_, hclosed, hmap, ?_, hvs, ?_, h1Vector hw, ?_, ?_⟩
  · intro z hzr hzi
    exact hchart z (hzr.trans (by linarith)) (hzi.trans (by linarith))
  · exact hvcont.comp Ψ.continuous.continuousOn hclosed
  · intro x hx
    exact smoothDirichletGraphChart_zero_boundary hS.1.1 p c hc f hf.continuous
      hb₀ hchart _ hvzero (hx.trans (by linarith))
  · rw [h1Value_h1Vector]
    exact hvm'.coeFn_toLp
  · intro i
    rw [h1Gradient_h1Vector]
    exact (hgm' i).coeFn_toLp

theorem exists_riemannMapping_flattened_genuine_chart_all_mixed_orders {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ (d : smoothTraceTests) (c : ℂ) (hc : c ≠ 0)
      (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (K : NNReal) (A b : ℝ),
      ‖c‖ = 1 ∧ LipschitzWith K f ∧ f 0 = 0 ∧ 0 < A ∧ 0 < b ∧
      (let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
       let u := riemannMappingDirichletRemainder F d ∘ Ψ
       let U := smoothDirichletHalfBox A b
       (∀ z : ℂ, |z.re| < A → |z.im| < b → (Ψ z ∈ Ω ↔ 0 < z.im)) ∧
       MapsTo Ψ (smoothDirichletClosedHalfBox A b) (closure Ω) ∧
       MapsTo Ψ U Ω ∧ ContinuousOn u (smoothDirichletClosedHalfBox A b) ∧
       ContDiffOn ℝ (⊤ : ℕ∞) u U ∧
       (∀ x : ℝ, |x| < A → u (x : ℂ) = 0) ∧
       MemLp u 2 (volume.restrict U) ∧
       (∀ i : Fin 2, MemLp (dirD u (coordDir i)) 2 (volume.restrict U)) ∧
       ∀ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ρ < A / 2 ∧ ρ < b ∧
         ∀ j q : ℕ, j + q ≤ N → MemLp (dirichletMixedDerivative j q u) 2
           (volume.restrict (smoothDirichletHalfBox ρ ρ))) := by
  obtain ⟨d, c, hc, f, hf, K, A, b, hc₁, hLip, hf₀, hA, hb₀,
    hchart, hclosed, hmap, hu, hs, hz, v, hv, hgv⟩ :=
    exists_riemannMapping_flattened_genuine_chart_h1 hb hS hsc F hF hinj himage hp
  let Ψ := smoothDirichletGraphChart p c hc f hf.continuous
  let u := riemannMappingDirichletRemainder F d ∘ Ψ
  let G := lap (d : ℂ → ℂ) ∘ Ψ
  let U := smoothDirichletHalfBox A b
  have hvm : MemLp u 2 (volume.restrict U) :=
    (Lp.memLp (h1Value U v)).ae_eq hv
  have hvg (i : Fin 2) : MemLp (dirD u (coordDir i)) 2 (volume.restrict U) :=
    (Lp.memLp (h1Gradient U i v)).ae_eq (hgv i)
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G :=
    d.property.lap.1.comp (smoothDirichletGraphChart_contDiff p c hc hf)
  have hstrong (z : ℂ) (hzU : z ∈ U) : dirichletFlattenedDivergence f u z = -G z := by
    rw [dirichletFlattenedDivergence_pullback hS.1.1 p c hc hc₁ hf
      (riemannMappingDirichletRemainder_contDiffOn hb hS hsc F hF hinj himage d) (hmap hzU)]
    exact riemannMappingDirichletRemainder_lap hb hS hsc F hF hinj himage d (hmap hzU)
  refine ⟨d, c, hc, f, hf, K, A, b, hc₁, hLip, hf₀, hA, hb₀,
    hchart, hclosed, hmap, hu, hs, hz, hvm, hvg, ?_⟩
  intro N
  exact exists_dirichlet_halfBox_mixed_derivative_memLp hA hb₀ hf hLip hu hs hz hvm hvg
    hstrong hGs N

end PolyaNeumann
end
