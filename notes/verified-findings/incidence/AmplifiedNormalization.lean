import AmplifyGraph
import AmplifyCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadTwo
open SymmetricNormalization SymmetricAmplification CircuitAmplification

namespace AmplifiedNormalization

theorem normalize : ∀ (a b : ℕ) (R : Fin a → Fin b → Prop) (C : Circuit),
      Lin R → IsAO2 (a+b) C →
      (∀ x, circuitFun (a+b) C x = true ↔
        ∃ p l, R p l ∧ x (Fin.castAdd b p) = true ∧ x (Fin.natAdd a l) = true) →
      ∃ (n₀ : ℕ) (S : Finset (Fin (a+b))),
        (∀ p l, R p l → Fin.castAdd b p ∈ S ∨ Fin.natAdd a l ∈ S) ∧
        ∀ t : ℕ, 0 < t → ∃ (n : ℕ) (T : Fin n → Fin n → Prop) (D : Circuit),
        n ≤ t*n₀ ∧
        IsAO2 (n+n) D ∧
        (∀ x, circuitFun (n+n) D x = true ↔
          ∃ i j, T i j ∧ x (Fin.castAdd n i) = true ∧ x (Fin.natAdd n j) = true) ∧
        (∀ i j, T i j → T j i) ∧ Lin T ∧
        (∃ m : Fin n → Fin n, Function.Involutive m ∧ ∀ i, T i (m i)) ∧
        (2*t)*((incid R).card+S.card)+(D.size+1) ≤ (incid T).card+n+(2*t)*(C.size+1) := by
  classical
  intro a b R C hR hc he
  have hExact : Exact R C := by
    intro x
    apply Bool.eq_iff_iff.mpr
    simpa using he x
  obtain ⟨n,T,B,S,hS,hB,eB,sy,li,⟨m,inv,edge⟩,bound⟩ :=
    SymmetricNormalization.normalize R C hR hc hExact
  refine ⟨n,S,hS,fun t ht => ?_⟩
  obtain ⟨D,hD,sd,eD⟩ := amplify t ht T B hB eB
  refine ⟨t*n,blockRel t T,D,le_rfl,hD,?_,?_,block_lin t li,
    ⟨blockMate t m,block_perfect t inv edge⟩,?_⟩
  · intro x
    rw [eD]
    exact decide_eq_true_iff
  · intro i j
    exact (block_symmetric t (fun u v => ⟨sy u v,sy v u⟩) i j).mp
  · rw [card_incid]
    have scaled := Nat.mul_le_mul_left t bound
    ring_nf at scaled sd ⊢
    omega

#print axioms normalize
end AmplifiedNormalization
