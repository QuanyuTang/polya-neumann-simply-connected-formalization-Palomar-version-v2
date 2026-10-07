module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.NatCast
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic

/-!
# Antiholomorphic transmutation: the algebraic identities (Section 5)

This file formalizes the algebraic content of Lemmas 5.4 and 5.5 of the paper: the
identities satisfied by the Vekua-type transmutation series

  `𝒱_E h = ∑_{j ≥ 0} (-E/4)^j / j! · z^j J^j h`,

where `J` is the normalized antiholomorphic primitive (`∂̄ J h = h`).

The analytic part of the paper (convergence of the series in Sobolev norms, Lemma 5.3) is not
formalized. Instead, `𝒱_E h` is treated as a *formal power series in the energy `E`*, with
coefficients in an abstract commutative `ℚ`-algebra `R` of functions, carrying two commuting
derivations `∂` (`D`) and `∂̄` (`Dbar`) with `∂ z = 1`, `∂̄ z = 0`. Antiholomorphic functions form
a submodule `A` on which `∂` vanishes and which `J` preserves. Every identity below is an
identity of coefficients of `E^j`, so it holds for any convergent realization of the series
in which termwise differentiation is justified (as in the paper).

Main results:
* `vekua_helmholtz` (Lemma 5.4, first part): `4 ∂ ∂̄ 𝒱_E h = -E 𝒱_E h`, i.e.
  `(-Δ - E) 𝒱_E h = 0`, since `Δ = 4 ∂ ∂̄`;
* `vekua_deriv` (Lemma 5.4, second part): `∂ⁿ 𝒱_E h = (-E/4)ⁿ 𝒱_E Jⁿ h`;
* `vekua_inverse` (Lemma 5.5): `∑_n (-z)ⁿ / n! · ∂ⁿ 𝒱_E h = h`, coefficientwise in `E`;
* `alternating_factorial_sum` (the combinatorial identity used in Lemma 5.5):
  `∑_{n=0}^ℓ (-1)ⁿ / (n! (ℓ-n)!) = [ℓ = 0]`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open PowerSeries

/-- The combinatorial identity in the proof of Lemma 5.5:
`∑_{n=0}^ℓ (-1)ⁿ / (n! (ℓ - n)!) = 1` if `ℓ = 0` and `0` otherwise. -/
theorem alternating_factorial_sum (l : ℕ) :
    ∑ n ∈ Finset.range (l + 1), ((-1 : ℚ) ^ n / (n.factorial * (l - n).factorial)) =
      if l = 0 then 1 else 0 := by
  have key : ∀ n ∈ Finset.range (l + 1), ((-1 : ℚ) ^ n / (n.factorial * (l - n).factorial)) =
      ((-1) ^ n * (l.choose n : ℚ)) / l.factorial := by
    intro n hn
    rw [Finset.mem_range] at hn
    rw [div_eq_div_iff (by positivity) (by positivity),
      ← Nat.choose_mul_factorial_mul_factorial (show n ≤ l by omega)]
    push_cast; ring
  rw [Finset.sum_congr rfl key, ← Finset.sum_div]
  have h2 : ∑ n ∈ Finset.range (l + 1), ((-1 : ℚ) ^ n * (l.choose n : ℚ)) =
      ((∑ n ∈ Finset.range (l + 1), ((-1 : ℤ) ^ n * (l.choose n : ℤ)) : ℤ) : ℚ) := by
    push_cast; rfl
  rw [h2, Int.alternating_sum_range_choose]
  split_ifs with h <;> simp [h]

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The `j`-th coefficient (in powers of `E`) of the transmutation series:
`(-1/4)^j / j! · z^j J^j h`. -/
def vekuaCoeff (z : R) (J : R →ₗ[ℚ] R) (h : R) (j : ℕ) : R :=
  ((-1 / 4 : ℚ) ^ j / (j.factorial : ℚ)) • (z ^ j * (J ^ j) h)

/-- The antiholomorphic transmutation `𝒱_E h = ∑_j (-E/4)^j / j! · z^j J^j h`
(equation (5.1) of the paper), as a formal power series in the energy `E`. -/
def vekua (z : R) (J : R →ₗ[ℚ] R) (h : R) : PowerSeries R :=
  PowerSeries.mk (vekuaCoeff z J h)

/-- The standing hypotheses of Section 5, in algebraic form: `∂` and `∂̄` are derivations with
`∂ z = 1`, `∂̄ z = 0`; antiholomorphic functions (`A`) are killed by `∂`, preserved by `J`
and by `∂̄`, and `J` is a right inverse of `∂̄` on `A`. -/
structure TransmutationData (D Dbar : Derivation ℚ R R) (z : R) (J : R →ₗ[ℚ] R)
    (A : Submodule ℚ R) : Prop where
  D_z : D z = 1
  Dbar_z : Dbar z = 0
  D_antihol : ∀ h ∈ A, D h = 0
  J_mem : ∀ h ∈ A, J h ∈ A
  Dbar_mem : ∀ h ∈ A, Dbar h ∈ A
  Dbar_J : ∀ h ∈ A, Dbar (J h) = h

variable {D Dbar : Derivation ℚ R R} {z : R} {J : R →ₗ[ℚ] R} {A : Submodule ℚ R}

lemma TransmutationData.pow_J_mem (hT : TransmutationData D Dbar z J A) {h : R} (hh : h ∈ A)
    (j : ℕ) : (J ^ j) h ∈ A := by
  induction j with
  | zero => simpa using hh
  | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact hT.J_mem _ ih

/-- Iterated holomorphic derivatives of `z^j a` with `a` antiholomorphic. -/
lemma iterate_D_pow_mul (hDz : D z = 1) {a : R} (ha : D a = 0) (j n : ℕ) :
    (⇑D)^[n] (z ^ j * a) = (j.descFactorial n : ℚ) • (z ^ (j - n) * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, D.map_smul, Derivation.leibniz, Derivation.leibniz_pow,
      ha, hDz, Nat.descFactorial_succ, smul_zero, zero_add]
    rcases Nat.lt_or_ge n j with h | h
    · rw [show j - n - 1 = j - (n + 1) by omega]
      simp only [Algebra.smul_def, Nat.cast_mul, map_mul, map_natCast, Algebra.algebraMap_self,
        RingHom.id_apply, eq_natCast (algebraMap ℕ R)]
      ring
    · rw [Nat.sub_eq_zero_of_le h]; simp

/-- Iterated derivations commute with rational scalars. -/
lemma iterate_derivation_smul (D : Derivation ℚ R R) (n : ℕ) (c : ℚ) (x : R) :
    (⇑D)^[n] (c • x) = c • (⇑D)^[n] x := by
  have e : (⇑D)^[n] = ⇑((D : R →ₗ[ℚ] R) ^ n) :=
    (Module.End.coe_pow (D : R →ₗ[ℚ] R) n).symm
  rw [e, map_smul]

/-- The coefficient form of Lemma 5.4 (Helmholtz equation): `∂∂̄` of the `(j+1)`-st coefficient
is `-1/4` times the `j`-th one. -/
lemma D_Dbar_vekuaCoeff_succ (hT : TransmutationData D Dbar z J A) {h : R} (hh : h ∈ A)
    (j : ℕ) : (4 : ℚ) • D (Dbar (vekuaCoeff z J h (j + 1))) = -vekuaCoeff z J h j := by
  have hJ : (J ^ (j + 1)) h = J ((J ^ j) h) := by rw [pow_succ', Module.End.mul_apply]
  have h1 : Dbar (vekuaCoeff z J h (j + 1)) =
      ((-1 / 4 : ℚ) ^ (j + 1) / ((j + 1).factorial : ℚ)) • (z ^ (j + 1) * (J ^ j) h) := by
    unfold vekuaCoeff
    rw [Dbar.map_smul, Derivation.leibniz, Derivation.leibniz_pow, hT.Dbar_z, hJ,
      hT.Dbar_J _ (hT.pow_J_mem hh j)]
    simp
  have h2 : D (z ^ (j + 1) * (J ^ j) h) = ((j + 1 : ℕ) : ℚ) • (z ^ j * (J ^ j) h) := by
    have := iterate_D_pow_mul hT.D_z (hT.D_antihol _ (hT.pow_J_mem hh j)) (j + 1) 1
    simpa using this
  rw [h1, D.map_smul, h2, smul_smul, smul_smul]
  unfold vekuaCoeff
  rw [← neg_smul]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma D_Dbar_vekuaCoeff_zero (hT : TransmutationData D Dbar z J A) {h : R} (hh : h ∈ A) :
    D (Dbar (vekuaCoeff z J h 0)) = 0 := by
  simpa [vekuaCoeff] using hT.D_antihol _ (hT.Dbar_mem h hh)

/-- **Lemma 5.4 (Helmholtz equation).** Coefficientwise in `E`,
`4 ∂ ∂̄ 𝒱_E h = -E 𝒱_E h`; since `Δ = 4 ∂ ∂̄`, this is `(-Δ - E) 𝒱_E h = 0`. -/
theorem vekua_helmholtz (hT : TransmutationData D Dbar z J A) {h : R} (hh : h ∈ A) :
    PowerSeries.mk (fun j => (4 : ℚ) • D (Dbar (coeff j (vekua z J h)))) =
      -(X * vekua z J h) := by
  ext j
  cases j with
  | zero => simp [vekua, D_Dbar_vekuaCoeff_zero hT hh]
  | succ j => simp [vekua, D_Dbar_vekuaCoeff_succ hT hh]

/-- **Lemma 5.4 (holomorphic derivatives).** Coefficientwise in `E`,
`∂ⁿ 𝒱_E h = (-E/4)ⁿ 𝒱_E (Jⁿ h)`. -/
theorem vekua_deriv (hT : TransmutationData D Dbar z J A) {h : R} (hh : h ∈ A) (n : ℕ) :
    PowerSeries.mk (fun k => (⇑D)^[n] (coeff k (vekua z J h))) =
      (-1 / 4 : ℚ) ^ n • (X ^ n * vekua z J ((J ^ n) h)) := by
  ext k
  rw [coeff_mk, PowerSeries.coeff_smul, coeff_X_pow_mul']
  simp only [vekua, coeff_mk, vekuaCoeff]
  rw [iterate_derivation_smul,
    iterate_D_pow_mul hT.D_z (hT.D_antihol _ (hT.pow_J_mem hh k)), smul_smul]
  split_ifs with hnk
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnk
    rw [show n + j - n = j by omega, smul_smul, ← Module.End.mul_apply, ← pow_add,
      add_comm j n]
    congr 1
    have hd := Nat.factorial_mul_descFactorial (show n ≤ n + j by omega)
    rw [show n + j - n = j by omega] at hd
    have hd' : ((n + j).descFactorial n : ℚ) = (n + j).factorial / j.factorial := by
      rw [eq_div_iff (by positivity)]; exact_mod_cast (by rw [mul_comm]; exact hd)
    rw [hd']
    field_simp
    ring
  · rw [(Nat.descFactorial_eq_zero_iff_lt).2 (by omega)]
    simp

/-- **Lemma 5.5 (inversion formula).** For every power `E^k`, the coefficient of
`∑_n (-z)ⁿ / n! · ∂ⁿ 𝒱_E h` equals that of `h` (only `n ≤ k` contribute, since `∂ⁿ 𝒱_E h` is
divisible by `Eⁿ`). -/
theorem vekua_inverse (hT : TransmutationData D Dbar z J A) {h : R} (hh : h ∈ A) (k : ℕ) :
    ∑ n ∈ Finset.range (k + 1),
        ((-1 : ℚ) ^ n / (n.factorial : ℚ)) • (z ^ n * (⇑D)^[n] (coeff k (vekua z J h))) =
      if k = 0 then h else 0 := by
  have hterm : ∀ n ∈ Finset.range (k + 1),
      ((-1 : ℚ) ^ n / (n.factorial : ℚ)) • (z ^ n * (⇑D)^[n] (coeff k (vekua z J h))) =
        ((-1 / 4 : ℚ) ^ k * ((-1 : ℚ) ^ n / (n.factorial * (k - n).factorial))) •
          (z ^ k * (J ^ k) h) := by
    intro n hn
    rw [Finset.mem_range] at hn
    simp only [vekua, coeff_mk, vekuaCoeff]
    rw [iterate_derivation_smul,
      iterate_D_pow_mul hT.D_z (hT.D_antihol _ (hT.pow_J_mem hh k)), smul_smul,
      mul_smul_comm, ← mul_assoc, ← pow_add, show n + (k - n) = k by omega, smul_smul]
    congr 1
    have hd := Nat.factorial_mul_descFactorial (show n ≤ k by omega)
    have hd' : (k.descFactorial n : ℚ) = k.factorial / (k - n).factorial := by
      rw [eq_div_iff (by positivity)]; exact_mod_cast (by rw [mul_comm]; exact hd)
    rw [hd']
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul, ← Finset.mul_sum,
    alternating_factorial_sum]
  split_ifs with hk
  · subst hk; simp
  · simp

/-- The `E⁰` coefficient of `𝒱_E h` is `h`; in particular `h ↦ 𝒱_E h` is injective
(the formal counterpart of the injectivity statement of Lemma 5.5). -/
theorem vekua_constantCoeff (h : R) : constantCoeff (vekua z J h) = h := by
  simp [vekua, vekuaCoeff, ← coeff_zero_eq_constantCoeff_apply]

theorem vekua_injective : Function.Injective (vekua z J) := fun h₁ h₂ e => by
  simpa [vekua_constantCoeff] using congrArg constantCoeff e

end PolyaNeumann
