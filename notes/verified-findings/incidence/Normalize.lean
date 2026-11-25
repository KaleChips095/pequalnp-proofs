import MinimumCover
import Involution
import Graph
import Circuit
import PEqualNP.Defs.ReadTwo

namespace SymmetricNormalization
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity PEqualNP.ReadTwo
open SymmetricIncidence
attribute [local instance] Classical.propDecidable

def Exact {a b : ℕ} (R : Fin a → Fin b → Prop) (C : Circuit) : Prop :=
  ∀ x, circuitFun (a+b) C x = decide
    (∃ p l, R p l ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true)

theorem incid_card {a b : ℕ} (R : Fin a → Fin b → Prop) :
    (incid R).card = Fintype.card (Inc R) := by
  classical
  exact (Fintype.card_ofFinset (p := {z | R z.1 z.2}) (incid R) (by simp [incid])).symm

theorem normalize {a b : ℕ} (R : Fin a → Fin b → Prop) (C : Circuit)
    (hfour : Lin R) (hc : IsAO2 (a+b) C) (he : Exact R C) :
    ∃ (n : ℕ) (T : Fin n → Fin n → Prop) (D : Circuit) (S : Finset (Fin (a+b))),
      (∀ p l, R p l → Fin.castAdd b p ∈ S ∨ Fin.natAdd a l ∈ S) ∧
      IsAO2 (n+n) D ∧ Exact T D ∧ (∀ i j, T i j → T j i) ∧ Lin T ∧
      (∃ m : Fin n → Fin n, Function.Involutive m ∧ ∀ i, T i (m i)) ∧
      2*((incid R).card+S.card)+D.size ≤ (incid T).card+n+2*C.size+1 := by
  classical
  let V := Fin a ⊕ Fin b
  let e : V ≃ Fin (a+b) := finSumFinEquiv
  obtain ⟨S,f,cover,out,edges⟩ := MinimumCover.pack R
  have symm : ∀ u v, adj R u v → adj R v u := by
    intro u v; cases u <;> cases v <;> simp [adj]
  have adjEq (u v : V) : MinimumCover.adjacency R u v ↔ adj R u v := by
    cases u <;> cases v <;> rfl
  obtain ⟨m,inv,_,hm,hi,hs⟩ := CoverInvolution.exists_mate S f out (adj R) symm
    (fun s => (adjEq ..).mp (edges s)) (fun u v h => cover u v ((adjEq ..).mpr h))
  let U := Finset.univ.filter fun v : V => m v = v
  let U' := U.map e.toEmbedding
  let T := SymmetricPump.relation R U'
  have fix (v : V) : e v ∈ U' ↔ m v = v := by simp [U',U]
  have ir (v w : V) : T (e v) (e w) ↔ liftRel R m v w := by
    change ((∃ p l, R p l ∧ e v = Fin.castAdd b p ∧ e w = Fin.natAdd a l) ∨
      (∃ p l, R p l ∧ e w = Fin.castAdd b p ∧ e v = Fin.natAdd a l) ∨
      (e v = e w ∧ e v ∈ U')) ↔ _
    simp only [show ∀ p : Fin a, Fin.castAdd b p = e (.inl p) from fun _ => rfl,
      show ∀ l : Fin b, Fin.natAdd a l = e (.inr l) from fun _ => rfl,
      e.injective.eq_iff,fix,liftRel]
    cases v <;> cases w <;> simp [adj,eq_comm] <;> grind
  obtain ⟨D,hd,sd,ed⟩ := SymmetricPump.pump R U' C hc he
  obtain ⟨bij,hmatch⟩ := perfect R m inv hm
  let m' := (e.symm.trans (Equiv.ofBijective m bij)).trans e
  let S' := S.map e.toEmbedding
  refine ⟨a+b,T,D,S',?_,hd,ed,?_,?_,⟨m',?_,?_⟩,?_⟩
  · intro p l h
    have h' := cover (.inl p) (.inr l) h
    change e (.inl p) ∈ S' ∨ e (.inr l) ∈ S'
    simpa [S'] using h'
  · intro i j
    obtain ⟨u,rfl⟩ := e.surjective i
    obtain ⟨v,rfl⟩ := e.surjective j
    simpa only [ir] using (symmetric R m u v).mp
  · intro i j k l hij hkl hh
    obtain ⟨i,rfl⟩ := e.surjective i
    obtain ⟨j,rfl⟩ := e.surjective j
    obtain ⟨k,rfl⟩ := e.surjective k
    obtain ⟨l,rfl⟩ := e.surjective l
    have nf : NoFour R := fun p q l t hp hl h => hfour p q l t hp hl ⟨h.1,h.2.2.1,h.2.1,h.2.2.2⟩
    simp only [ir] at hh
    exact noFour R m nf hi i j k l (fun h => hij (congrArg e h))
      (fun h => hkl (congrArg e h)) ⟨hh.1,hh.2.2.1,hh.2.1,hh.2.2.2⟩
  · intro i
    simp [m',inv _]
  · intro i
    obtain ⟨u,rfl⟩ := e.surjective i
    simpa [m',ir] using (ir u (m u)).mpr (hmatch u)
  · have eE : Inc (liftRel R m) ≃ Inc T :=
      (e.prodCongr e).subtypeEquiv (fun z => (ir z.1 z.2).symm)
    have hcard := Fintype.card_congr eE
    have cnt := edges_card R m
    have fixed : Fintype.card (Fixed m) = U.card :=
      Fintype.card_ofFinset (p := {v | m v = v}) U (by simp [U])
    have us : U'.card = U.card := Finset.card_map _
    have ss : S'.card = S.card := Finset.card_map _
    have hs' : Fintype.card (Fin a ⊕ Fin b) = 2*S.card + U.card := by
      rw [hs]; congr 2; ext v; simp [U]
    simp only [Fintype.card_sum,Fintype.card_fin] at hs'
    rw [incid_card,incid_card]
    omega

#print axioms normalize
end SymmetricNormalization
