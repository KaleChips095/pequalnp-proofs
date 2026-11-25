import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_11463

abbrev Shore := Fin 7 → Bool

def reps : List Nat := [127,244,480,720,1188,3008,16256]
def points (m : Nat) (k i : Fin 7) := m.testBit (i+k).val
def lines (m : Nat) (k i : Fin 7) := m.testBit (7+(i+k).val)

-- Lines that can be included when the selected points are `p`.
def addLines (p : Shore) (i : Fin 7) := !(p i || p (i+1) || p (i+3))
-- Points that can be included when the selected lines are `l`.
def addPoints (l : Shore) (i : Fin 7) := !(l i || l (i-1) || l (i-3))

-- No selected line is incident with a selected point.
def Independent (p l : Shore) := ∀ i, l i = true → addLines p i = true

-- Independent, with every absent point and every absent line blocked.
def Maximal (p l : Shore) := Independent p l ∧
  (∀ i, p i = false → addPoints l i = false) ∧
  (∀ i, l i = false → addLines p i = false)

-- Complete the point set by first adding every compatible line, then every
-- compatible point. Each of the resulting maximal sets is a representative rotation.
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem completion_orbit : ∀ (p : Shore), ∃ m ∈ reps, ∃ k : Fin 7,
    (∀ i, points m k i = addPoints (addLines p) i) ∧
    (∀ i, lines m k i = addLines p i) := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem completion_preserves_points : ∀ (p : Shore) i,
    p i = true → addPoints (addLines p) i = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem rotations_maximal : ∀ m ∈ reps, ∀ k : Fin 7,
    Maximal (points m k) (lines m k) := by
  unfold Maximal Independent
  decide +kernel

-- The public seven masks and their rotations classify *all* maximal independent sets.
theorem maximal_iff_orbit (p l : Shore) : Maximal p l ↔
    ∃ m ∈ reps, ∃ k : Fin 7, p = points m k ∧ l = lines m k := by
  constructor
  · rintro ⟨hind,hp,hl⟩
    have heq : l = addLines p := by
      funext i
      cases e : l i with
      | false => exact (hl i e).symm
      | true => exact (hind i e).symm
    have fixed : p = addPoints (addLines p) := by
      funext i
      cases e : p i with
      | false => exact heq ▸ (hp i e).symm
      | true => exact (completion_preserves_points p i e).symm
    obtain ⟨m,hm,k,h₁,h₂⟩ := completion_orbit p
    exact ⟨m,hm,k,fixed.trans (funext h₁).symm,heq.trans (funext h₂).symm⟩
  · rintro ⟨m,hm,k,rfl,rfl⟩
    exact rotations_maximal m hm k

-- Boolean pairs give literal keys for sets of the fourteen labelled vertices.
def orbitKeys (m : Nat) := (List.finRange 7).map fun k =>
    (List.ofFn (points m k), List.ofFn (lines m k))

theorem different_masks : (reps.flatMap orbitKeys).eraseDups.length = 37 := by decide +kernel

theorem orbit_lengths : (reps.map fun m => (orbitKeys m).eraseDups.length) =
    [1,7,7,7,7,7,1] := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem completion_maximal : ∀ (p : Shore), Maximal (addPoints (addLines p)) (addLines p) := by
  unfold Maximal Independent
  decide +kernel

end PEqualNP.Outside.L_meta_11463

theorem PEqualNP.Outside.L_meta_11463 : ∀ (x1 : Fin (7 : ℕ) → Bool), ∃ x2 ∈ [(127 : ℕ), (244 : ℕ), (480 : ℕ), (720 : ℕ), (1188 : ℕ), (3008 : ℕ), (16256 : ℕ)], ∃ (x3 : Fin (7 : ℕ)), (∀ (x4 : Fin (7 : ℕ)), x1 x4 = Bool.true → x2.testBit ↑(x4 + x3) = Bool.true) ∧ ∀ (x4 : Fin (7 : ℕ)), x1 x4 = Bool.false → x1 (x4 + (1 : Fin (7 : ℕ))) = Bool.false → x1 (x4 + (3 : Fin (7 : ℕ))) = Bool.false → x2.testBit ((7 : ℕ) + ↑(x4 + x3)) = Bool.true := by
  intro p
  obtain ⟨m,hm,k,hpoints,hlines⟩ :=
    (PEqualNP.Outside.L_meta_11463.maximal_iff_orbit _ _).mp
      (PEqualNP.Outside.L_meta_11463.completion_maximal p)
  refine ⟨m,hm,k,?_,?_⟩
  · intro i hi
    exact (congrFun hpoints i).symm.trans
      (PEqualNP.Outside.L_meta_11463.completion_preserves_points p i hi)
  · intro i h₀ h₁ h₃
    exact (congrFun hlines i).symm.trans
      (by simp [PEqualNP.Outside.L_meta_11463.addLines,h₀,h₁,h₃])
