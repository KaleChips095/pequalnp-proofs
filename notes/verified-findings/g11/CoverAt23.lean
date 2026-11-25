import PEqualNP.Defs

namespace Private6796Cost23
open PEqualNP PEqualNP.CircuitLowerBounds
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
local instance gateKind (B : Circuit) (j : ℕ) : Decidable (ReadTwo.isAnd B j) := by
  unfold ReadTwo.isAnd
  infer_instance

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def P : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768]
def Q : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]

def Pass (budget : ℕ) (B : Circuit) (T : List (ℕ × ℕ)) : Prop :=
  let v := fun (r w : ℕ) => BlindGate.wireValue B 11 (fun i => r.testBit i.val) w
  TopForm.IsAO2 11 B ∧ T ≠ [] ∧ B.size + 2 * T.length ≤ budget ∧ 3 ≤ ReadTwo.nAnd B ∧
  (∀ e ∈ T, e.1 < 11 + B.size ∧ e.2 < 11 + B.size) ∧
  (∀ j < B.size, (P.any fun r => v r (11+j)) = true ∧ (Q.any fun r => v r (11+j)) = true) ∧
  (∀ j < B.size, ReadTwo.isAnd B j → ∃ e ∈ T, ∃ w ∈ [e.1,e.2],
    w = 11+j ∨ (11 ≤ w ∧ EdgeOwnership.InCone 11 B j (w-11))) ∧
  (∀ r ∈ P ++ Q, (T.any fun e => v r e.1 && v r e.2) = decide (r ∈ P))

instance (budget : ℕ) (B : Circuit) (T : List (ℕ × ℕ)) : Decidable (Pass budget B T) := by
  unfold Pass
  dsimp only
  infer_instance

def base : Circuit := ⟨[
  ⟨.or, [4, 5]⟩,
  ⟨.or, [4, 8]⟩,
  ⟨.or, [8, 10]⟩,
  ⟨.or, [9, 11]⟩,
  ⟨.and, [13, 14]⟩,
  ⟨.or, [1, 15]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.or, [6, 9]⟩,
  ⟨.or, [7, 10]⟩,
  ⟨.and, [18, 19]⟩,
  ⟨.or, [3, 20]⟩,
  ⟨.or, [5, 10]⟩,
  ⟨.and, [9, 11]⟩,
  ⟨.or, [2, 23]⟩,
  ⟨.or, [9, 10]⟩], 0⟩
def pairs : List (ℕ × ℕ) := [(12, 16), (17, 21), (22, 24), (0, 25)]
theorem physical : Pass 23 base pairs := by decide +kernel

theorem target_shape : (∃ B T, Pass 22 B T) ↔ (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (ℕ × ℕ)),   have x3 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)];   have x4 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)];   have x5 : ℕ → ℕ → Bool := fun (x5 x6 : ℕ) => PEqualNP.BlindGate.wireValue x1 (11 : ℕ) (fun (x7 : Fin (11 : ℕ)) => x5.testBit ↑x7) x6;   PEqualNP.TopForm.IsAO2 (11 : ℕ) x1 ∧ x2 ≠ [] ∧ x1.size + (2 : ℕ) * x2.length ≤ (22 : ℕ) ∧ (3 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x1 ∧ (∀ x6 ∈ x2, x6.1 < (11 : ℕ) + x1.size ∧ x6.2 < (11 : ℕ) + x1.size) ∧ (∀ x6 < x1.size, (x3.any fun (x8 : ℕ) => x5 x8 ((11 : ℕ) + x6)) = Bool.true ∧ (x4.any fun (x8 : ℕ) => x5 x8 ((11 : ℕ) + x6)) = Bool.true) ∧ (∀ x6 < x1.size, PEqualNP.ReadTwo.isAnd x1 x6 → ∃ x9 ∈ x2, ∃ x10 ∈ [x9.1, x9.2], x10 = (11 : ℕ) + x6 ∨ (11 : ℕ) ≤ x10 ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x1 x6 (x10 - (11 : ℕ))) ∧ ∀ x6 ∈ x3 ++ x4, (x2.any fun (x8 : ℕ × ℕ) => x5 x6 x8.1 && x5 x6 x8.2) = Decidable.decide (x6 ∈ x3)) := Iff.rfl
#print axioms physical
end Private6796Cost23
