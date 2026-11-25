import Mathlib
import PEqualNP.Defs.ReadTwo

namespace SymmetricAmplification
open PEqualNP.ReadTwo
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

def blockRel (t : ℕ) (T : Fin n → Fin n → Prop) (a b : Fin (t*n)) :=
  (finProdFinEquiv.symm a).1 = (finProdFinEquiv.symm b).1 ∧
  T (finProdFinEquiv.symm a).2 (finProdFinEquiv.symm b).2

@[simp] theorem blockRel_pair {t : ℕ} (T : Fin n → Fin n → Prop)
    (i j : Fin t) (x y : Fin n) :
    blockRel t T (finProdFinEquiv (i,x)) (finProdFinEquiv (j,y)) ↔ i=j ∧ T x y := by
  simp [blockRel]

theorem exists_edge_iff (t : ℕ) (T : Fin n → Fin n → Prop)
    (P L : Fin (t*n) → Prop) :
    (∃ a b, blockRel t T a b ∧ P a ∧ L b) ↔
    ∃ (i : Fin t) (x y : Fin n), T x y ∧ P (finProdFinEquiv (i,x)) ∧
      L (finProdFinEquiv (i,y)) := by
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    obtain ⟨⟨i,x⟩,rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨⟨j,y⟩,rfl⟩ := finProdFinEquiv.surjective b
    obtain ⟨rfl,h⟩ := (blockRel_pair T i j x y).mp hab
    exact ⟨_,_,_,h,ha,hb⟩
  · rintro ⟨i,x,y,h,hx,hy⟩
    exact ⟨_,_,(blockRel_pair T i i x y).mpr ⟨rfl,h⟩,hx,hy⟩

theorem block_lin (t : ℕ) {T : Fin n → Fin n → Prop} (h : Lin T) :
    Lin (blockRel t T) := by
  intro a b c d
  obtain ⟨⟨i,x⟩,rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨j,y⟩,rfl⟩ := finProdFinEquiv.surjective b
  obtain ⟨⟨k,z⟩,rfl⟩ := finProdFinEquiv.surjective c
  obtain ⟨⟨l,w⟩,rfl⟩ := finProdFinEquiv.surjective d
  simp only [blockRel_pair]
  unfold Lin at h
  grind

theorem block_symmetric (t : ℕ) {T : Fin n → Fin n → Prop}
    (h : ∀ a b, T a b ↔ T b a) : ∀ a b, blockRel t T a b ↔ blockRel t T b a := by
  intro a b
  exact and_congr eq_comm (h _ _)

def blockMate (t : ℕ) (m : Fin n → Fin n) (a : Fin (t*n)) : Fin (t*n) :=
  finProdFinEquiv ((finProdFinEquiv.symm a).1,m (finProdFinEquiv.symm a).2)

theorem block_perfect (t : ℕ) {m : Fin n → Fin n} {T : Fin n → Fin n → Prop}
    (inv : Function.Involutive m) (edge : ∀ a, T a (m a)) :
    Function.Involutive (blockMate t m) ∧ ∀ a, blockRel t T a (blockMate t m a) := by
  constructor <;> intro a <;> obtain ⟨⟨i,x⟩,rfl⟩ := finProdFinEquiv.surjective a <;>
    simp [blockMate, blockRel, inv x, edge]

abbrev Inc {A B : Type*} (R : A → B → Prop) := {e : A × B // R e.1 e.2}

private theorem cardInc {a b : ℕ} (R : Fin a → Fin b → Prop) :
    (incid R).card = Fintype.card (Inc R) := by
  classical
  exact (Fintype.card_ofFinset (p := {z | R z.1 z.2}) (incid R) (by simp [incid])).symm

def edgesEquiv (t : ℕ) (T : Fin n → Fin n → Prop) :
    Fin t × Inc T ≃ Inc (blockRel t T) where
  toFun
    | (i,⟨(x,y),h⟩) => ⟨(finProdFinEquiv (i,x),finProdFinEquiv (i,y)),
      (blockRel_pair T i i x y).mpr ⟨rfl,h⟩⟩
  invFun
    | ⟨(a,b),h⟩ => ((finProdFinEquiv.symm a).1,
      ⟨((finProdFinEquiv.symm a).2,(finProdFinEquiv.symm b).2),h.2⟩)
  left_inv := by rintro ⟨i,⟨⟨x,y⟩,h⟩⟩; simp
  right_inv := by
    rintro ⟨⟨a,b⟩,hab⟩
    obtain ⟨⟨i,x⟩,rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨⟨j,y⟩,rfl⟩ := finProdFinEquiv.surjective b
    obtain ⟨rfl,h⟩ := (blockRel_pair T i j x y).mp hab
    simp

theorem card_incid (t : ℕ) (T : Fin n → Fin n → Prop) :
    (incid (blockRel t T)).card = t * (incid T).card := by
  classical
  rw [cardInc, cardInc]
  simpa using (Fintype.card_congr (edgesEquiv t T)).symm

end SymmetricAmplification
