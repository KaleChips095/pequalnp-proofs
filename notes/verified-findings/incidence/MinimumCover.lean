import Mathlib

namespace MinimumCover

def Covers {P L : Type*} (R : P → L → Prop) (X : Finset P) (Y : Finset L) :=
  ∀ p l, R p l → p ∈ X ∨ l ∈ Y

theorem exists_minimum {P L : Type*} [Fintype P] (R : P → L → Prop) :
    ∃ (X : Finset P) (Y : Finset L), Covers R X Y ∧
      ∀ U W, Covers R U W → X.card + Y.card ≤ U.card + W.card := by
  classical
  let h : ∃ k : ℕ, ∃ (U : Finset P) (W : Finset L), Covers R U W ∧ U.card + W.card = k :=
    ⟨_, Finset.univ, ∅, (fun _ _ _ => Or.inl (Finset.mem_univ _)), rfl⟩
  obtain ⟨X,Y,hc,he⟩ := Nat.find_spec h
  exact ⟨X,Y,hc,fun U W hUW => he ▸ Nat.find_min' h ⟨U,W,hUW,rfl⟩⟩

/-- Replacing covered vertices on one shore by their uncovered neighbors proves Hall's condition. -/
theorem shore {P L : Type*} [Fintype L] (R : P → L → Prop) (X : Finset P) (Y : Finset L)
    (hc : Covers R X Y) (hm : ∀ U W, Covers R U W → X.card + Y.card ≤ U.card + W.card) :
    ∃ f : ↥X ↪ L, ∀ u : ↥X, R u.val (f u) ∧ f u ∉ Y := by
  classical
  let N (p : ↥X) := Finset.univ.filter fun l => R p.val l ∧ l ∉ Y
  have hall (s : Finset ↥X) : s.card ≤ (s.biUnion N).card := by
    let T := s.map (Function.Embedding.subtype (· ∈ X))
    have sub : T ⊆ X := by
      intro p hp
      obtain ⟨u,_,rfl⟩ := Finset.mem_map.mp hp
      exact u.property
    have cover : Covers R (X \ T) (Y ∪ s.biUnion N) := by
      intro p l hpl
      by_cases hy : l ∈ Y
      · exact Or.inr (Finset.mem_union_left _ hy)
      have hx : p ∈ X := (hc p l hpl).resolve_right hy
      by_cases ht : p ∈ T
      · obtain ⟨u,hu,he⟩ := Finset.mem_map.mp ht
        change u.val = p at he
        exact Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨u,hu,Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.symm ▸ And.intro hpl hy⟩⟩))
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨hx,ht⟩)
    have hmin := hm _ _ cover
    have hdiff := Finset.card_sdiff_add_card_eq_card sub
    have hcard : T.card = s.card := Finset.card_map _
    have hunion := Finset.card_union_le Y (s.biUnion N)
    omega
  obtain ⟨f,hf,hedge⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hall
  exact ⟨⟨f,hf⟩,fun p => (Finset.mem_filter.mp (hedge p)).2⟩

def adjacency {P L : Type*} (R : P → L → Prop) : P ⊕ L → P ⊕ L → Prop
  | .inl p, .inr l => R p l
  | .inr l, .inl p => R p l
  | _, _ => False

theorem pack {P L : Type*} [Fintype P] [Fintype L] (R : P → L → Prop) :
    ∃ (S : Finset (P ⊕ L)) (f : ↥S ↪ P ⊕ L),
      (∀ u v, adjacency R u v → u ∈ S ∨ v ∈ S) ∧
      (∀ s, f s ∉ S) ∧ (∀ s : ↥S, adjacency R s.val (f s)) := by
  classical
  obtain ⟨X,Y,hc,hm⟩ := exists_minimum R
  obtain ⟨left,hLeft⟩ := shore R X Y hc hm
  have hct : Covers (fun l p => R p l) Y X := fun l p h => (hc p l h).symm
  obtain ⟨right,hRight⟩ := shore (fun l p => R p l) Y X hct (by
    intro U W hc'
    simpa [Nat.add_comm] using hm W U (fun p l h => (hc' l p h).symm))
  let S := X.disjSum Y
  let f : ↥S → P ⊕ L
    | ⟨.inl p,hp⟩ => .inr (left ⟨p, Finset.inl_mem_disjSum.mp hp⟩)
    | ⟨.inr l,hl⟩ => .inl (right ⟨l, Finset.inr_mem_disjSum.mp hl⟩)
  have inj : Function.Injective f := by
    rintro ⟨p,hp⟩ ⟨v,hv⟩ he
    apply Subtype.ext
    cases p <;> cases v <;> simp only [f, Sum.inr.injEq, Sum.inl.injEq] at he ⊢
    · exact congrArg Subtype.val (left.injective he)
    · contradiction
    · contradiction
    · exact congrArg Subtype.val (right.injective he)
  refine ⟨S,⟨f,inj⟩,?_,?_,?_⟩
  · intro u v h
    cases u <;> cases v <;> simp_all [S, adjacency, Covers]
  · rintro ⟨p | l,h⟩
    · exact fun hm => (hLeft _).2 (Finset.inr_mem_disjSum.mp hm)
    · exact fun hm => (hRight _).2 (Finset.inl_mem_disjSum.mp hm)
  · rintro ⟨p | l,h⟩
    · exact (hLeft ⟨p,Finset.inl_mem_disjSum.mp h⟩).1
    · exact (hRight ⟨l,Finset.inr_mem_disjSum.mp h⟩).1

#print axioms pack
end MinimumCover
