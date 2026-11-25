import Normalize

namespace CircuitAmplification
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open Bridge3491 SymmetricNormalization
attribute [local instance] Classical.propDecidable

def decode (t n : ℕ) : Fin (t*n) ≃ Fin t × Fin n := finProdFinEquiv.symm

def copies {a b : ℕ} (t : ℕ) (R : Fin a → Fin b → Prop) (u : Fin (t*a)) (v : Fin (t*b)) :=
  (decode t a u).1 = (decode t b v).1 ∧ R (decode t a u).2 (decode t b v).2

def copyWire {t a b : ℕ} (i : Fin t) : Fin (a+b) → Fin (t*a + t*b) :=
  Fin.addCases (fun p => Fin.castAdd (t*b) (finProdFinEquiv (i,p)))
    (fun l => Fin.natAdd (t*a) (finProdFinEquiv (i,l)))

/-- An OR over any positive number of outputs costs at most one gate per join. -/
theorem join {I : Type*} {n s : ℕ} (F : I → (Fin n → Bool) → Bool)
    (available : ∀ i, ∃ C : Circuit, IsAO2 n C ∧ C.size ≤ s ∧ ∀ x, circuitFun n C x = F i x)
    (L : List I) (h : L ≠ []) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size+1 ≤ L.length*(s+1) ∧
      ∀ x, circuitFun n D x = L.any (fun i => F i x) := by
  induction L with
  | nil => exact (h rfl).elim
  | cons i l ih =>
    obtain ⟨C,hC,sC,eC⟩ := available i
    by_cases hl : l = []
    · subst l
      exact ⟨C,hC,by simpa using Nat.add_le_add_right sC 1,by simpa using eC⟩
    · obtain ⟨B,hB,sB,eB⟩ := ih hl
      obtain ⟨D,hD,sD,eD⟩ := orTwo C B hC hB
      exact ⟨D,hD,by rw [List.length_cons,Nat.add_mul]; omega,
        fun x => by rw [eD,eC,eB,List.any_cons]⟩

theorem amplify {a b : ℕ} (t : ℕ) (ht : 0 < t) (R : Fin a → Fin b → Prop) (C : Circuit)
    (hc : IsAO2 (a+b) C) (he : Exact R C) :
    ∃ D : Circuit, IsAO2 (t*a+t*b) D ∧ D.size+1 ≤ t*(C.size+1) ∧ Exact (copies t R) D := by
  classical
  unfold Exact at he
  let F (i : Fin t) (x : Fin (t*a+t*b) → Bool) := circuitFun (a+b) C (x ∘ copyWire i)
  have available (i : Fin t) : ∃ B : Circuit, IsAO2 (t*a+t*b) B ∧ B.size ≤ C.size ∧
      ∀ x, circuitFun (t*a+t*b) B x = F i x := by
    apply restrictOfFalse (fun p => Sum.inr (copyWire i p)) C hc
    exact ⟨fun _ => false, by rw [he]; simp [plug]⟩
  have nonempty : List.finRange t ≠ [] := by
    intro h
    have z := congrArg List.length h
    simp at z
    omega
  obtain ⟨D,hd,sd,ed⟩ := join F available (List.finRange t) nonempty
  refine ⟨D,hd,by simpa using sd, fun x => ?_⟩
  rw [ed]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_finRange, true_and, F, he, decide_eq_true_eq,
    Function.comp_apply,copyWire,Fin.addCases_left,Fin.addCases_right]
  constructor
  · rintro ⟨i,p,l,hpl,hp,hl⟩
    refine ⟨finProdFinEquiv (i,p),finProdFinEquiv (i,l),?_,hp,hl⟩
    simpa [copies,decode] using hpl
  · rintro ⟨u,v,huv,hu,hv⟩
    obtain ⟨⟨i,p⟩,rfl⟩ := finProdFinEquiv.surjective u
    obtain ⟨⟨j,l⟩,rfl⟩ := finProdFinEquiv.surjective v
    simp only [copies,decode,Equiv.symm_apply_apply] at huv
    obtain ⟨rfl,hpl⟩ := huv
    exact ⟨i,p,l,hpl,hu,hv⟩

#print axioms amplify
end CircuitAmplification
