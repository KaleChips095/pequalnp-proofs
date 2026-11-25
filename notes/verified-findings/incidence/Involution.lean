import Mathlib

namespace CoverInvolution
open scoped Classical

/-- A matching of a vertex cover into its complement extends to an involution.
All unmatched vertices are independent. -/
theorem exists_mate {V : Type*} [Fintype V] (S : Finset V) (f : ↥S ↪ V)
    (fout : ∀ s, f s ∉ S) (A : V → V → Prop) (symm : ∀ u v, A u v → A v u)
    (edges : ∀ s, A s.val (f s)) (cover : ∀ u v, A u v → u ∈ S ∨ v ∈ S) :
    ∃ mate : V → V, Function.Involutive mate ∧ (∀ s : ↥S, mate s.val = f s) ∧
      (∀ v, mate v ≠ v → A v (mate v)) ∧
      (∀ u v, mate u = u → mate v = v → ¬ A u v) ∧
      Fintype.card V = 2*S.card + (Finset.univ.filter fun v => mate v = v).card := by
  classical
  let mate (v : V) := if h : v ∈ S then f ⟨v,h⟩ else
    if h' : ∃ s, f s = v then h'.choose.val else v
  have left (s : ↥S) : mate s.val = f s := by simp [mate, s.property]
  have right (s : ↥S) : mate (f s) = s.val := by
    have h : ∃ t, f t = f s := ⟨s,rfl⟩
    have he : h.choose = s := f.injective h.choose_spec
    simp only [mate, dite_eq_right (fout s), dite_eq_left h, he]
  have other {v : V} (hs : v ∉ S) (ht : ¬ ∃ t, f t = v) : mate v = v := by
    simp only [mate, dite_eq_right hs, dite_eq_right ht]
  have notfix (s : ↥S) : mate s.val ≠ s.val := by
    rw [left]
    exact fun he => fout s (he ▸ s.property)
  have fixOut {v : V} (hf : mate v = v) : v ∉ S := fun h => notfix ⟨v,h⟩ hf
  refine ⟨mate, ?_, left, ?_, ?_, ?_⟩
  · intro v
    by_cases hs : v ∈ S
    · exact (congrArg mate (left ⟨v,hs⟩)).trans (right ⟨v,hs⟩)
    · by_cases ht : ∃ t, f t = v
      · obtain ⟨t,rfl⟩ := ht
        rw [right, left]
      · rw [other hs ht, other hs ht]
  · intro v hn
    by_cases hs : v ∈ S
    · exact (left ⟨v,hs⟩).symm ▸ edges ⟨v,hs⟩
    · by_cases ht : ∃ t, f t = v
      · obtain ⟨t,rfl⟩ := ht
        rw [right]
        exact symm _ _ (edges t)
      · exact (hn (other hs ht)).elim
  · intro u v hu hv he
    exact (cover u v he).elim (fixOut hu) (fixOut hv)
  · let T := Finset.univ.map f
    have hT (v : V) : v ∈ T ↔ ∃ t, f t = v := by simp [T]
    have disj : Disjoint S T := by
      apply Finset.disjoint_left.mpr
      intro v hs ht
      obtain ⟨t,rfl⟩ := (hT v).mp ht
      exact fout t hs
    have hfixed : (Finset.univ.filter fun v => mate v = v) = Finset.univ \ (S ∪ T) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro hf
        rintro (hs | ht)
        · exact fixOut hf hs
        · obtain ⟨t,rfl⟩ := (hT v).mp ht
          rw [right] at hf
          exact fout t (hf ▸ t.property)
      · intro h
        exact other (fun hs => h (.inl hs)) (fun ht => h (.inr ((hT v).mpr ht)))
    have htcard : T.card = S.card := by simp [T]
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (S ∪ T))
    rw [Finset.card_union_of_disjoint disj, htcard, Finset.card_univ] at hc
    rw [hfixed]
    omega

#print axioms exists_mate
end CoverInvolution
