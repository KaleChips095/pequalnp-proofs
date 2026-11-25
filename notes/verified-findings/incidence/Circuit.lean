import RepairEdges

namespace SymmetricPump
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open Bridge3491

variable {a b : ℕ}
local notation "V" => Fin (a+b)
local notation "W" => Fin ((a+b)+(a+b))

def relation (R : Fin a → Fin b → Prop) (U : Finset V) (u v : V) : Prop :=
  (∃ p l, R p l ∧ u = Fin.castAdd b p ∧ v = Fin.natAdd a l) ∨
  (∃ p l, R p l ∧ v = Fin.castAdd b p ∧ u = Fin.natAdd a l) ∨
  (u = v ∧ u ∈ U)

abbrev left (u : V) : W := Fin.castAdd (a+b) u
abbrev right (u : V) : W := Fin.natAdd (a+b) u

def forward : V → W := Fin.addCases (fun p => left (Fin.castAdd b p))
  (fun l => right (Fin.natAdd a l))
def backward : V → W := Fin.addCases (fun p => right (Fin.castAdd b p))
  (fun l => left (Fin.natAdd a l))

attribute [local instance] Classical.propDecidable

theorem pump (R : Fin a → Fin b → Prop) (U : Finset V) (C : Circuit) (hC : IsAO2 (a+b) C)
    (h : ∀ x, circuitFun (a+b) C x = decide
      (∃ p l, R p l ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true)) :
    ∃ D : Circuit, IsAO2 ((a+b)+(a+b)) D ∧ D.size ≤ 2*C.size+1+2*U.card ∧
      ∀ x, circuitFun ((a+b)+(a+b)) D x = decide
        (∃ u v, relation R U u v ∧ x (left u) = true ∧ x (right v) = true) := by
  classical
  have copy (f : V → W) : ∃ B : Circuit, IsAO2 ((a+b)+(a+b)) B ∧ B.size ≤ C.size ∧
      ∀ x, circuitFun ((a+b)+(a+b)) B x = circuitFun (a+b) C (x ∘ f) := by
    apply restrictOfFalse (fun i => Sum.inr (f i)) C hC
    exact ⟨fun _ => false, by rw [h]; simp [plug]⟩
  obtain ⟨F,hF,sF,eF⟩ := copy forward
  obtain ⟨B,hB,sB,eB⟩ := copy backward
  obtain ⟨J,hJ,sJ,eJ⟩ := orTwo F B hF hB
  let es := U.toList.map (fun u => (left u,right u))
  obtain ⟨D,hD,sD,eD⟩ := IncidenceRepair.repair J hJ es
  have he : es.length = U.card := by simp [es]
  refine ⟨D,hD,by omega,fun x => ?_⟩
  rw [eD,eJ,eF,eB,h,h]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_map, es,
    Bool.and_eq_true, Function.comp_apply, forward, backward, Fin.addCases_left,
    Fin.addCases_right, Finset.mem_toList]
  constructor
  · rintro ((⟨p,l,hpl,hp,hl⟩ | ⟨p,l,hpl,hp,hl⟩) | ⟨_,⟨u,hu,rfl⟩,hp,hl⟩)
    · exact ⟨_,_,Or.inl ⟨p,l,hpl,rfl,rfl⟩,hp,hl⟩
    · exact ⟨_,_,Or.inr (Or.inl ⟨p,l,hpl,rfl,rfl⟩),hl,hp⟩
    · exact ⟨_,_,Or.inr (Or.inr ⟨rfl,hu⟩),hp,hl⟩
  · rintro ⟨u,v,hrel,hu,hv⟩
    rcases hrel with ⟨p,l,hpl,rfl,rfl⟩ | ⟨p,l,hpl,rfl,rfl⟩ | ⟨rfl,hm⟩
    · exact Or.inl (Or.inl ⟨p,l,hpl,hu,hv⟩)
    · exact Or.inl (Or.inr ⟨p,l,hpl,hv,hu⟩)
    · exact Or.inr ⟨_,⟨u,hm,rfl⟩,hu,hv⟩

#print axioms pump
end SymmetricPump
