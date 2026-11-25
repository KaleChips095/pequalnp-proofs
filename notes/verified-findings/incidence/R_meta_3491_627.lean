import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadTwo

-- A counterexample can be doubled, reversing its two shores, and its unmatched vertices paired.
-- The resulting symmetric graph has a perfect matching supplied by an involution.
-- Disjoint copies amplify every one-gate violation into a linear deficit.
theorem PEqualNP.Outside.R_meta_3491_627
    (matched : ∀ k : ℕ, 0 < k → ∃ B : ℕ,
      ∀ (n : ℕ) (T : Fin n → Fin n → Prop) (D : Circuit),
      IsAO2 (n+n) D →
      (∀ x, circuitFun (n+n) D x = true ↔
        ∃ i j, T i j ∧ x (Fin.castAdd n i) = true ∧ x (Fin.natAdd n j) = true) →
      (∀ i j, T i j → T j i) → Lin T →
      (∃ m : Fin n → Fin n, Function.Involutive m ∧ ∀ i, T i (m i)) →
      k * ((incid T).card + n) ≤ k * (D.size + 1) + n + B)
    (normalize : ∀ (a b : ℕ) (R : Fin a → Fin b → Prop) (C : Circuit),
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
        (2*t)*((incid R).card+S.card)+(D.size+1) ≤ (incid T).card+n+(2*t)*(C.size+1)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : Finset (Fin (x1 + x2))), (∀ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 → Fin.castAdd x2 x10 ∈ x9 ∨ Fin.natAdd x1 x11 ∈ x9) ∧ (PEqualNP.ReadTwo.incid x3).card + x9.card ≤ x5.size + (1 : ℕ) := by
  intro a b R inst C hfour hC he
  have lin : Lin R := fun p q l t hp hl h =>
    hfour p q l t hp hl ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩
  obtain ⟨n₀,S,hS,copies⟩ :=
    normalize a b R C lin hC (fun x => by rw [he]; simp)
  refine ⟨S,hS,?_⟩
  by_contra! hbad
  obtain ⟨B,limit⟩ := matched (n₀+1) (by omega)
  let t := B+1
  obtain ⟨n,T,D,hn,hD,hT,hs,hl,hm,hsize⟩ := copies t (by dsimp [t]; omega)
  have upper := limit n T D hD hT hs hl hm
  have violation : (C.size+1)+1 ≤ (incid R).card+S.card := by omega
  have scaled := Nat.mul_le_mul_left (2*t) violation
  rw [Nat.mul_add, Nat.mul_one] at scaled
  have gap : (D.size+1)+t ≤ (incid T).card+n := by omega
  have lower := Nat.mul_le_mul_left (n₀+1) gap
  have distribute : (n₀+1)*t = t*n₀+t := by ring
  rw [Nat.mul_add, distribute] at lower
  dsimp [t] at *
  omega
