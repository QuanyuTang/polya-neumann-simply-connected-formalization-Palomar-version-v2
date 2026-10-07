module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic

/-!
# The weighted shift (Section 4 of the paper, Definition 4.1 and Lemma 4.2)

On `ℋ = ℓ²(ℕ₀)` with orthonormal basis `(e_n)`, the weighted shift is
`S_N e_0 = √2 e_1`, `S_N e_n = e_{n+1}` (`n ≥ 1`), and `D_N = 2 P_0 - P_1`.
-/

@[expose] public section

open scoped ComplexConjugate

noncomputable section

namespace PolyaNeumann

/-- The Hilbert space `ℋ = ℓ²(ℕ₀)`. -/
abbrev Ell2 := lp (fun _ : ℕ => ℂ) 2

/-! ### Instance normalisation for the Lean/Mathlib `v4.35.0-rc2` port

With Lean/Mathlib `v4.35.0-rc2`, type-class search elaborates the additive and module
structures of the `lp` model of `ℋ` through the subtype (`AddSubmonoidClass`) path, and the
stricter transparency discipline of the new unifier then no longer identifies these with the
structures expected by generic lemmas such as `add_smul` or by instances on `ℋ →L[ℂ] ℋ`.
The instances below fix one canonical choice: each is the standard Mathlib instance (all are
definitionally equal to the previously inferred ones), registered with high priority so that
every statement is elaborated with it.  They change no definition or statement of the
development. -/

instance (priority := high) instIsTopologicalAddGroupComplex : IsTopologicalAddGroup ℂ :=
  SeminormedAddCommGroup.toIsTopologicalAddGroup

instance (priority := high) instAddCommGroupEll2 : AddCommGroup Ell2 :=
  NormedAddCommGroup.toAddCommGroup

instance (priority := high) instAddCommMonoidEll2 : AddCommMonoid Ell2 :=
  AddCommGroup.toAddCommMonoid

instance (priority := high) instModuleComplexEll2 : Module ℂ Ell2 :=
  NormedSpace.toModule

instance (priority := high) instModuleRealEll2 : Module ℝ Ell2 :=
  NormedSpace.toModule

instance (priority := high) instIsTopologicalAddGroupEll2 : IsTopologicalAddGroup Ell2 :=
  SeminormedAddCommGroup.toIsTopologicalAddGroup

instance : ContinuousStar (Ell2 →L[ℂ] Ell2) :=
  @NormedStarGroup.to_continuousStar (Ell2 →L[ℂ] Ell2) _ _ _

instance : StarModule ℝ (Ell2 →L[ℂ] Ell2) :=
  @StarModule.complexToReal (Ell2 →L[ℂ] Ell2) _ _ _ _

instance : IsScalarTower ℝ (Ell2 →L[ℂ] Ell2) (Ell2 →L[ℂ] Ell2) :=
  @IsScalarTower.right ℝ (Ell2 →L[ℂ] Ell2) _ _ _

instance : SMulCommClass ℝ (Ell2 →L[ℂ] Ell2) (Ell2 →L[ℂ] Ell2) :=
  @Algebra.to_smulCommClass ℝ (Ell2 →L[ℂ] Ell2) _ _ _

/-- `r • x = (r : ℂ) • x` for real scalars acting on `ℋ`. -/
lemma real_smul_eq_coe_smul_ell2 (r : ℝ) (x : Ell2) : r • x = (r : ℂ) • x :=
  (Complex.coe_smul r x).symm

/-- `r • A = (r : ℂ) • A` for real scalars acting on `ℋ →L[ℂ] ℋ`. -/
lemma real_smul_eq_coe_smul_clm (r : ℝ) (A : Ell2 →L[ℂ] Ell2) : r • A = (r : ℂ) • A :=
  (Complex.coe_smul r A).symm

/-- The weights of the shift: `w_0 = √2`, `w_n = 1` for `n ≥ 1`. -/
def shiftWeight (n : ℕ) : ℂ := if n = 0 then (Real.sqrt 2 : ℂ) else 1

lemma conj_shiftWeight (n : ℕ) : conj (shiftWeight n) = shiftWeight n := by
  unfold shiftWeight; split_ifs <;> simp

lemma norm_shiftWeight_sq_le (n : ℕ) : ‖shiftWeight n‖ ^ 2 ≤ 2 := by
  unfold shiftWeight; split_ifs <;> simp

lemma shiftWeight_mul_self (n : ℕ) :
    shiftWeight n * shiftWeight n = if n = 0 then 2 else 1 := by
  unfold shiftWeight; split_ifs
  · rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; simp
  · simp

/-- Coordinates of `S_N f`. -/
def shiftFun (f : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => shiftWeight n * f n

/-- Coordinates of `S_N^* f`. -/
def shiftAdjFun (f : ℕ → ℂ) : ℕ → ℂ := fun n => shiftWeight n * f (n + 1)

lemma two_toReal : (2 : ENNReal).toReal = 2 := by simp

lemma summable_sq (f : Ell2) : Summable fun n => ‖(f : ℕ → ℂ) n‖ ^ 2 := by
  have := (memℓp_gen_iff (p := 2) (by simp)).mp f.2
  simpa [two_toReal] using this

lemma memℓp_of_summable_sq {g : ℕ → ℂ} (h : Summable fun n => ‖g n‖ ^ 2) :
    Memℓp g 2 := by
  rw [memℓp_gen_iff (by simp)]
  simpa [two_toReal] using h

lemma tsum_sq_eq_norm_sq (f : Ell2) : ∑' n, ‖(f : ℕ → ℂ) n‖ ^ 2 = ‖f‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by simp) f
  simp only [two_toReal, Real.rpow_two] at this
  exact this.symm

lemma shift_sq_bound (f : Ell2) (n : ℕ) :
    ‖shiftWeight n * (f : ℕ → ℂ) n‖ ^ 2 ≤ 2 * ‖(f : ℕ → ℂ) n‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (norm_shiftWeight_sq_le n) (by positivity)

lemma shiftAdj_sq_bound (f : Ell2) (n : ℕ) :
    ‖shiftWeight n * (f : ℕ → ℂ) (n + 1)‖ ^ 2 ≤ 2 * ‖(f : ℕ → ℂ) (n + 1)‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (norm_shiftWeight_sq_le n) (by positivity)

lemma summable_shiftFun (f : Ell2) : Summable fun n => ‖shiftFun f n‖ ^ 2 := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
    ((summable_sq f).mul_left 2)
  exact shift_sq_bound f n

lemma summable_shiftAdjFun (f : Ell2) : Summable fun n => ‖shiftAdjFun f n‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => shiftAdj_sq_bound f n)
    (((summable_nat_add_iff 1).mpr (summable_sq f)).mul_left 2)

/-- `S_N` as a linear map. -/
def shiftLin : Ell2 →ₗ[ℂ] Ell2 where
  toFun f := ⟨shiftFun f, memℓp_of_summable_sq (summable_shiftFun f)⟩
  map_add' f g := by
    apply lp.ext; funext n
    change shiftFun (⇑(f + g)) n = shiftFun ⇑f n + shiftFun ⇑g n
    cases n <;> simp [shiftFun, mul_add]
  map_smul' c f := by
    apply lp.ext; funext n
    change shiftFun (⇑(c • f)) n = c • shiftFun ⇑f n
    cases n <;> simp [shiftFun]; ring

/-- `S_N^*` as a linear map. -/
def shiftAdjLin : Ell2 →ₗ[ℂ] Ell2 where
  toFun f := ⟨shiftAdjFun f, memℓp_of_summable_sq (summable_shiftAdjFun f)⟩
  map_add' f g := by
    apply lp.ext; funext n
    change shiftAdjFun (⇑(f + g)) n = shiftAdjFun ⇑f n + shiftAdjFun ⇑g n
    simp [shiftAdjFun, mul_add]
  map_smul' c f := by
    apply lp.ext; funext n
    change shiftAdjFun (⇑(c • f)) n = c • shiftAdjFun ⇑f n
    simp [shiftAdjFun]; ring

lemma shiftLin_norm_le (f : Ell2) : ‖shiftLin f‖ ≤ Real.sqrt 2 * ‖f‖ := by
  apply lp.norm_le_of_tsum_le (p := 2) (by simp) (by positivity)
  simp only [two_toReal, Real.rpow_two]
  rw [mul_pow, Real.sq_sqrt (by norm_num), ← tsum_sq_eq_norm_sq, ← tsum_mul_left]
  change ∑' n, ‖shiftFun f n‖ ^ 2 ≤ _
  rw [(summable_shiftFun f).tsum_eq_zero_add]
  simp only [shiftFun, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_add]
  calc ∑' n, ‖shiftWeight n * (f : ℕ → ℂ) n‖ ^ 2 ≤ ∑' n, 2 * ‖(f : ℕ → ℂ) n‖ ^ 2 :=
        Summable.tsum_le_tsum (fun n => shift_sq_bound f n)
          ((summable_nat_add_iff 1).mpr (summable_shiftFun f))
          ((summable_sq f).mul_left 2)
    _ ≤ _ := le_rfl

lemma shiftAdjLin_norm_le (f : Ell2) : ‖shiftAdjLin f‖ ≤ Real.sqrt 2 * ‖f‖ := by
  apply lp.norm_le_of_tsum_le (p := 2) (by simp) (by positivity)
  simp only [two_toReal, Real.rpow_two]
  rw [mul_pow, Real.sq_sqrt (by norm_num), ← tsum_sq_eq_norm_sq, ← tsum_mul_left]
  change ∑' n, ‖shiftAdjFun f n‖ ^ 2 ≤ _
  calc ∑' n, ‖shiftAdjFun f n‖ ^ 2 ≤ ∑' n, 2 * ‖(f : ℕ → ℂ) (n + 1)‖ ^ 2 :=
        Summable.tsum_le_tsum (fun n => shiftAdj_sq_bound f n) (summable_shiftAdjFun f)
          (((summable_nat_add_iff 1).mpr (summable_sq f)).mul_left 2)
    _ ≤ ∑' n, 2 * ‖(f : ℕ → ℂ) n‖ ^ 2 := by
      rw [((summable_sq f).mul_left 2).tsum_eq_zero_add]
      exact le_add_of_nonneg_left (by positivity)

/-- The weighted shift `S_N`: `S_N e_0 = √2 e_1`, `S_N e_n = e_{n+1}` for `n ≥ 1`. -/
def shiftN : Ell2 →L[ℂ] Ell2 := shiftLin.mkContinuous (Real.sqrt 2) shiftLin_norm_le

/-- The concrete formula for `S_N^*`. -/
def shiftNAdj : Ell2 →L[ℂ] Ell2 := shiftAdjLin.mkContinuous (Real.sqrt 2) shiftAdjLin_norm_le

@[simp] lemma shiftN_apply_zero (f : Ell2) : (shiftN f : ℕ → ℂ) 0 = 0 := rfl

@[simp] lemma shiftN_apply_succ (f : Ell2) (n : ℕ) :
    (shiftN f : ℕ → ℂ) (n + 1) = shiftWeight n * (f : ℕ → ℂ) n := rfl

@[simp] lemma shiftNAdj_apply (f : Ell2) (n : ℕ) :
    (shiftNAdj f : ℕ → ℂ) n = shiftWeight n * (f : ℕ → ℂ) (n + 1) := rfl

/-- `shiftNAdj` is the Hilbert-space adjoint of `S_N`. -/
lemma shiftNAdj_eq_adjoint : shiftNAdj = ContinuousLinearMap.adjoint shiftN := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  have hs : Summable fun i => inner ℂ ((f : ℕ → ℂ) i) ((shiftN g : ℕ → ℂ) i) :=
    lp.summable_inner f (shiftN g)
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, hs.tsum_eq_zero_add]
  simp only [shiftNAdj_apply, shiftN_apply_zero, shiftN_apply_succ,
    RCLike.inner_apply]
  rw [zero_mul, zero_add]
  congr 1; funext n
  rw [map_mul, conj_shiftWeight]; ring

/-- The operator `D_N = 2 P_0 - P_1`, i.e. the diagonal operator with entries
`(2, -1, 0, 0, …)`. -/
def diagN : Ell2 →L[ℂ] Ell2 :=
  (2 : ℂ) • (ContinuousLinearMap.toSpanSingleton ℂ (lp.single 2 0 (1 : ℂ) : Ell2)).comp
      (innerSL ℂ (lp.single 2 0 (1 : ℂ) : Ell2)) -
    (ContinuousLinearMap.toSpanSingleton ℂ (lp.single 2 1 (1 : ℂ) : Ell2)).comp
      (innerSL ℂ (lp.single 2 1 (1 : ℂ) : Ell2))

/-- The diagonal entries of `D_N`. -/
def diagEntry (n : ℕ) : ℂ := if n = 0 then 2 else if n = 1 then -1 else 0

lemma inner_single (f : Ell2) (k : ℕ) :
    inner ℂ (lp.single 2 k (1 : ℂ) : Ell2) f = (f : ℕ → ℂ) k := by
  rw [lp.inner_eq_tsum, tsum_eq_single k]
  · simp
  · intro b hb; simp [lp.single_apply, hb]

lemma diagN_apply (f : Ell2) (n : ℕ) :
    (diagN f : ℕ → ℂ) n = diagEntry n * (f : ℕ → ℂ) n := by
  simp only [diagN, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_single,
    ContinuousLinearMap.toSpanSingleton_apply, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply,
    Pi.smul_apply, lp.single_apply, diagEntry]
  rcases n with _ | _ | n <;> simp

/-- Lemma 4.2: `[S_N^*, S_N] = D_N`. -/
theorem shift_commutator :
    ContinuousLinearMap.adjoint shiftN * shiftN - shiftN * ContinuousLinearMap.adjoint shiftN
      = diagN := by
  rw [← shiftNAdj_eq_adjoint]
  ext1 f
  apply lp.ext; funext n
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, lp.coeFn_sub,
    Pi.sub_apply, diagN_apply, shiftNAdj_apply, shiftN_apply_succ]
  rcases n with _ | _ | n
  · simp [shiftWeight_mul_self, diagEntry, ← mul_assoc]
  · simp only [shiftN_apply_succ, shiftNAdj_apply, diagEntry]
    rw [← mul_assoc, ← mul_assoc, shiftWeight_mul_self, shiftWeight_mul_self]; norm_num; ring
  · simp only [shiftN_apply_succ, shiftNAdj_apply, diagEntry]
    rw [← mul_assoc, ← mul_assoc, shiftWeight_mul_self, shiftWeight_mul_self]; simp

/-- `S_N` is bounded with `‖S_N‖ ≤ √2`. -/
lemma shiftN_norm_le : ‖shiftN‖ ≤ Real.sqrt 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) shiftLin_norm_le

/-- `G_x = -i (S_N + S_N^*) / 2`. -/
def Gx : Ell2 →L[ℂ] Ell2 :=
  (-Complex.I / 2) • (shiftN + ContinuousLinearMap.adjoint shiftN)

/-- `G_y = (S_N^* - S_N) / 2`. -/
def Gy : Ell2 →L[ℂ] Ell2 :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.adjoint shiftN - shiftN)

/-- Lemma 4.2: `G_x^* = -G_x`. -/
theorem Gx_adjoint : ContinuousLinearMap.adjoint Gx = -Gx := by
  simp only [Gx, map_smulₛₗ, map_add, ContinuousLinearMap.adjoint_adjoint]
  rw [show (starRingEnd ℂ) (-Complex.I / 2) = Complex.I / 2 by
    simp [map_div₀, Complex.conj_I, Complex.conj_ofNat]]
  rw [add_comm]; ext1 v; simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply]
  rw [← neg_smul]; congr 1; ring

/-- Lemma 4.2: `G_y^* = -G_y`. -/
theorem Gy_adjoint : ContinuousLinearMap.adjoint Gy = -Gy := by
  simp only [Gy, map_smulₛₗ, map_sub, ContinuousLinearMap.adjoint_adjoint]
  rw [show (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 by simp [Complex.conj_ofNat]]
  ext1 v; simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply]
  rw [← smul_neg, ← ContinuousLinearMap.neg_apply, neg_sub]

/-- Lemma 4.2: `[G_x, G_y] = (i/2) D_N`. -/
theorem Gx_Gy_commutator : Gx * Gy - Gy * Gx = (Complex.I / 2) • diagN := by
  rw [← shift_commutator]
  ext1 v
  simp only [Gx, Gy, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, map_add, map_sub, map_smul]
  module

/-- The standard basis vector `e_n` of `ℓ²(ℕ₀)`. -/
def basisVec (n : ℕ) : Ell2 := lp.single 2 n (1 : ℂ)

lemma diagN_basisVec (n : ℕ) : diagN (basisVec n) = diagEntry n • basisVec n := by
  apply lp.ext; funext m
  rw [diagN_apply]
  simp only [basisVec, lp.single_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases h : m = n
  · subst h; simp
  · simp [h]

/-- Lemma 4.2: `tr D_N = ∑ ⟨e_n, D_N e_n⟩ = 1`. -/
theorem trace_diagN : ∑' n, inner ℂ (basisVec n) (diagN (basisVec n)) = 1 := by
  have : ∀ n, inner ℂ (basisVec n) (diagN (basisVec n)) = diagEntry n := by
    intro n
    rw [diagN_basisVec, inner_smul_right, basisVec, inner_single]; simp
  simp only [this]
  rw [tsum_eq_sum (s := {0, 1})]
  · simp [diagEntry]; norm_num
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    simp [diagEntry, hb.1, hb.2]

/-- Lemma 4.2: `‖D_N‖_{𝒮₁} = 3`.  Since `D_N` is diagonal in the orthonormal basis `(e_n)`
(`diagN_basisVec`), its singular values are the moduli `|2|, |-1|, 0, …` of its diagonal
entries, whose sum is `3`. -/
theorem traceNorm_diagN : ∑' n, ‖diagEntry n‖ = 3 := by
  rw [tsum_eq_sum (s := {0, 1})]
  · simp [diagEntry]; norm_num
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    simp [diagEntry, hb.1, hb.2]

end PolyaNeumann

end
