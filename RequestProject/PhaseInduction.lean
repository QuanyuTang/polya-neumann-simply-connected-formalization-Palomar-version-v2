module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

/-!
# The induction across eigenvalues (Lemma 9.6, abstract form)

The proof of Lemma 9.6 (`M(E) ≤ N_N(E)`) is an induction across the finitely many positive
eigenvalues below `E`, using the initial value of the phase count (Lemma 8.7), its constancy
away from the spectrum (Lemma 9.4) and the jump bound at an eigenvalue (Lemma 9.5).
This file isolates that induction for an arbitrary real sequence `lam` (standing for the
Neumann eigenvalues, listed with multiplicity) and an arbitrary real function `M`. Unlike
`le_one_add_sum_of_jumps` (which bounds an integer-valued `M` by `1 + ∑ m(μ)`), the conclusion is
stated directly in terms of the count `#{j | lam j < E}`, so no counting identity is needed.
-/

@[expose] public section

open Set

namespace PolyaNeumann

/-- Lemma 9.6, abstract form. Let `lam : ℕ → ℝ` with `lam 0 = 0`, and let `M : ℝ → ℝ`.
Call `E` nonresonant if no `lam j` equals `E`. Suppose
* (initial value) `M E ≤ 1` for all sufficiently small nonresonant `E > 0`;
* (constancy) `M E₂ ≤ M E₁` whenever `0 < E₁ ≤ E₂` and no `lam j` lies in `[E₁, E₂]`;
* (jump bound) at every positive value `μ = lam j`, of multiplicity `m = #{i | lam i = μ}`,
  `M E₂ ≤ M E₁ + m` for nonresonant `0 < E₁ < μ < E₂` close enough to `μ`.

Then `M E ≤ #{j | lam j < E}` for every nonresonant `E > 0` for which this set is finite. -/
theorem phase_le_count_of_jumps (lam : ℕ → ℝ) (h0 : lam 0 = 0) (M : ℝ → ℝ)
    (hinit : ∃ δ > 0, ∀ E, 0 < E → E < δ → (∀ j, lam j ≠ E) → M E ≤ 1)
    (hconst : ∀ E₁ E₂, 0 < E₁ → E₁ ≤ E₂ → (∀ j, lam j ∉ Icc E₁ E₂) → M E₂ ≤ M E₁)
    (hjump : ∀ j, 0 < lam j → ∀ m : ℕ, {i | lam i = lam j}.encard = m →
      ∃ δ > 0, ∀ E₁ E₂, 0 < E₁ → lam j - δ < E₁ → E₁ < lam j →
      lam j < E₂ → E₂ < lam j + δ → (∀ i, lam i ≠ E₁) → (∀ i, lam i ≠ E₂) → M E₂ ≤ M E₁ + m)
    (E : ℝ) (hE : 0 < E) (hnr : ∀ j, lam j ≠ E) (hfin : {j | lam j < E}.Finite) :
    M E ≤ {j | lam j < E}.ncard := by
  obtain ⟨δ0, hδ0, hinit⟩ := hinit
  induction h : (lam '' {j | 0 < lam j ∧ lam j < E}).ncard using Nat.strong_induction_on
    generalizing E with
  | _ n ih =>
  set P := lam '' {j | 0 < lam j ∧ lam j < E} with hP
  have hPfin : P.Finite := (hfin.subset (fun j hj => hj.2)).image lam
  have hone : (1 : ℝ) ≤ {j | lam j < E}.ncard := by
    have : 0 < {j | lam j < E}.ncard := (Set.ncard_pos hfin).2 ⟨0, by simp [h0, hE]⟩
    exact_mod_cast this
  rcases P.eq_empty_or_nonempty with hPe | hPne
  · set E' := min (δ0 / 2) E
    have hE'pos : 0 < E' := lt_min (by positivity) hE
    have hE'le : E' ≤ E := min_le_right _ _
    have hno : ∀ j, lam j ∉ Icc E' E := by
      intro j hj
      have hlt : lam j < E := lt_of_le_of_ne hj.2 (hnr j)
      have : lam j ∈ P := ⟨j, ⟨hE'pos.trans_le hj.1, hlt⟩, rfl⟩
      rw [hPe] at this; exact this
    have h1 := hconst E' E hE'pos hE'le hno
    have h2 := hinit E' hE'pos (lt_of_le_of_lt (min_le_left _ _) (by linarith))
      (fun j hj => hno j (by rw [hj]; exact ⟨le_rfl, hE'le⟩))
    linarith
  · have hne : hPfin.toFinset.Nonempty := by simpa using hPne
    set e := hPfin.toFinset.max' hne with he
    have heP : e ∈ P := by simpa using hPfin.toFinset.max'_mem hne
    have hemax : ∀ x ∈ P, x ≤ e := fun x hx =>
      hPfin.toFinset.le_max' x (by simpa using hx)
    set A := insert (0 : ℝ) (hPfin.toFinset.erase e) with hA
    have hAne : A.Nonempty := Finset.insert_nonempty _ _
    set a := A.max' hAne with ha
    have ha0 : 0 ≤ a := A.le_max' 0 (Finset.mem_insert_self _ _)
    have haP : ∀ x ∈ P, x ≠ e → x ≤ a := fun x hx hxe =>
      A.le_max' x (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hxe, by simpa using hx⟩))
    obtain ⟨j0, ⟨hj0pos, hj0E⟩, hj0e⟩ := heP
    have hepos : 0 < e := hj0e ▸ hj0pos
    have heE : e < E := hj0e ▸ hj0E
    have hae : a < e := by
      have hmem := A.max'_mem hAne
      rw [← ha] at hmem
      rcases Finset.mem_insert.1 hmem with h0' | h0'
      · rw [h0']; exact hepos
      · obtain ⟨hne', hm⟩ := Finset.mem_erase.1 h0'
        exact lt_of_le_of_ne (hemax a (by simpa using hm)) hne'
    -- the multiplicity of `e`
    have hsub : {i | lam i = e} ⊆ {j | lam j < E} := fun i hi => by
      simp only [mem_setOf_eq] at hi ⊢; rw [hi]; exact heE
    have hmfin : {i | lam i = e}.Finite := hfin.subset hsub
    have hm := hmfin.cast_ncard_eq
    obtain ⟨δ, hδ, hjump⟩ := hjump j0 hj0pos _ (by rw [hj0e]; exact hm.symm)
    rw [hj0e] at hjump
    set E₁ := (max a (e - δ) + e) / 2 with hE₁
    set E₂ := (e + min (e + δ) E) / 2 with hE₂
    have hmax : max a (e - δ) < e := max_lt hae (by linarith)
    have hE₁lo : max a (e - δ) < E₁ := by rw [hE₁]; linarith
    have hE₁hi : E₁ < e := by rw [hE₁]; linarith
    have haE₁ : a < E₁ := lt_of_le_of_lt (le_max_left _ _) hE₁lo
    have hδE₁ : e - δ < E₁ := lt_of_le_of_lt (le_max_right _ _) hE₁lo
    have hE₁pos : 0 < E₁ := lt_of_le_of_lt ha0 haE₁
    have hmin : e < min (e + δ) E := lt_min (by linarith) heE
    have hE₂lo : e < E₂ := by rw [hE₂]; linarith
    have hE₂hi : E₂ < min (e + δ) E := by rw [hE₂]; linarith
    have hE₂δ : E₂ < e + δ := lt_of_lt_of_le hE₂hi (min_le_left _ _)
    have hE₂E : E₂ < E := lt_of_lt_of_le hE₂hi (min_le_right _ _)
    have hnr₁ : ∀ i, lam i ≠ E₁ := by
      intro i hi
      have hiP : lam i ∈ P := ⟨i, ⟨hi ▸ hE₁pos, hi ▸ hE₁hi.trans heE⟩, rfl⟩
      have := haP _ hiP (by rw [hi]; exact hE₁hi.ne)
      linarith
    have hno₂ : ∀ i, lam i ∉ Icc E₂ E := by
      intro i hi
      have hlt : lam i < E := lt_of_le_of_ne hi.2 (hnr i)
      have hiP : lam i ∈ P := ⟨i, ⟨by linarith [hi.1], hlt⟩, rfl⟩
      have := hemax _ hiP
      linarith [hi.1]
    have hnr₂ : ∀ i, lam i ≠ E₂ := fun i hi => hno₂ i (by rw [hi]; exact ⟨le_rfl, hE₂E.le⟩)
    have hjmp := hjump E₁ E₂ hE₁pos hδE₁ hE₁hi hE₂lo hE₂δ hnr₁ hnr₂
    -- the induction hypothesis at `E₁`
    have hfin₁ : {j | lam j < E₁}.Finite :=
      hfin.subset fun j hj => lt_trans hj (hE₁hi.trans heE)
    have hlt : (lam '' {j | 0 < lam j ∧ lam j < E₁}).ncard < n := by
      rw [← h]
      refine Set.ncard_lt_ncard ?_ hPfin
      refine ⟨?_, ?_⟩
      · rintro _ ⟨j, ⟨hj1, hj2⟩, rfl⟩
        exact ⟨j, ⟨hj1, hj2.trans (hE₁hi.trans heE)⟩, rfl⟩
      · intro hsub'
        obtain ⟨j, ⟨-, hj2⟩, hje⟩ := hsub' ⟨j0, ⟨hj0pos, hj0E⟩, hj0e⟩
        linarith
    have hih := ih _ hlt E₁ hE₁pos hnr₁ hfin₁ rfl
    -- the count splits at `e`
    have hsplit : {j | lam j < E} = {j | lam j < E₁} ∪ {i | lam i = e} := by
      ext j
      simp only [mem_setOf_eq, mem_union]
      constructor
      · intro hj
        by_cases hj0 : lam j ≤ 0
        · left; linarith
        · have hjP : lam j ∈ P := ⟨j, ⟨lt_of_not_ge hj0, hj⟩, rfl⟩
          by_cases hje : lam j = e
          · right; exact hje
          · left; exact lt_of_le_of_lt (haP _ hjP hje) haE₁
      · rintro (hj | hj)
        · exact hj.trans (hE₁hi.trans heE)
        · rw [hj]; exact heE
    have hdisj : Disjoint {j | lam j < E₁} {i | lam i = e} := by
      rw [Set.disjoint_left]
      intro j hj1 hj2
      simp only [mem_setOf_eq] at hj1 hj2
      linarith
    have hcount : ({j | lam j < E}.ncard : ℝ) =
        {j | lam j < E₁}.ncard + {i | lam i = e}.ncard := by
      rw [hsplit, Set.ncard_union_eq hdisj hfin₁ hmfin]; push_cast; ring
    have hc := hconst E₂ E (hE₁pos.trans (hE₁hi.trans hE₂lo)) hE₂E.le hno₂
    rw [hcount]
    linarith

end PolyaNeumann
