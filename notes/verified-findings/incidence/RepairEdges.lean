import GateSize

namespace IncidenceRepair
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.Helpers
open Bridge3491

def edgeCircuit {n : ℕ} (p : Fin n × Fin n) : Circuit :=
  ⟨[⟨.and, [p.1.val, p.2.val]⟩], n⟩

theorem edgeLegal {n : ℕ} (p : Fin n × Fin n) : IsAO2 n (edgeCircuit p) := by
  change Good n ([] ++ [⟨.and, [p.1.val, p.2.val]⟩])
  apply snocGood (by simp [Good,IsAO2,AndOrOnly,ReadsBack]) (by simp [AO])
  simp

theorem edgeEval {n : ℕ} (p : Fin n × Fin n) (x : Fin n → Bool) :
    circuitFun n (edgeCircuit p) x = (x p.1 && x p.2) := by
  change ((List.ofFn x) ++ [GateOp.and.eval ([p.1.val, p.2.val].map
    fun i => (List.ofFn x).getD i false)]).getD n false = _
  rw [getD_snoc_len _ _ _ _ (by simp)]
  simp [GateOp.eval, List.getD_eq_getElem?_getD]

/-- Restore the missing edge terms of an induced restriction in an arbitrary AO2 circuit. -/
theorem repair {n : ℕ} (C : Circuit) (hc : IsAO2 n C) (es : List (Fin n × Fin n)) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size + 2 * es.length ∧
      ∀ x, circuitFun n D x = (circuitFun n C x || es.any (fun p => x p.1 && x p.2)) := by
  induction es with
  | nil => exact ⟨C, hc, by simp, by simp⟩
  | cons p ps ih =>
    obtain ⟨B, hB, sB, eB⟩ := ih
    obtain ⟨D, hD, sD, eD⟩ := orTwo B (edgeCircuit p) hB (edgeLegal p)
    have sp : (edgeCircuit p).size = 1 := rfl
    refine ⟨D, hD, by simp only [List.length_cons]; omega, fun x => ?_⟩
    rw [eD, eB, edgeEval, List.any_cons]
    ac_rfl

/-- The exact circuit can be recovered at additive cost even for a constant-false restriction. -/
theorem repairRestriction {m n : ℕ} (C : Circuit) (hc : IsAO2 m C)
    (σ : Fin m → Bool ⊕ Fin n) (hzero : ∃ x, circuitFun m C (plug σ x) = false)
    (es : List (Fin n × Fin n)) (F : (Fin n → Bool) → Bool)
    (hcover : ∀ x, (circuitFun m C (plug σ x) || es.any (fun p => x p.1 && x p.2)) = F x) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size + 2 * es.length ∧
      ∀ x, circuitFun n D x = F x := by
  obtain ⟨B,hB,sB,eB⟩ := restrictOfFalse σ C hc hzero
  obtain ⟨D,hD,sD,eD⟩ := repair B hB es
  exact ⟨D,hD,by omega,fun x => by rw [eD,eB,hcover]⟩

#print axioms repairRestriction
end IncidenceRepair
