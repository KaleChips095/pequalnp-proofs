import Mathlib

namespace SymmetricIncidence

variable {P L : Type*}

def adj (R : P → L → Prop) : P ⊕ L → P ⊕ L → Prop
  | .inl p, .inr l => R p l
  | .inr l, .inl p => R p l
  | _, _ => False

def liftRel (R : P → L → Prop) (mate : P ⊕ L → P ⊕ L) (u v : P ⊕ L) :=
  adj R u v ∨ (u = v ∧ mate u = u)

def NoFour {A B : Type*} (R : A → B → Prop) :=
  ∀ a b c d, a ≠ b → c ≠ d → ¬ (R a c ∧ R a d ∧ R b c ∧ R b d)

theorem symmetric (R : P → L → Prop) (m : P ⊕ L → P ⊕ L) :
    ∀ u v, liftRel R m u v ↔ liftRel R m v u := by
  intro u v
  cases u <;> cases v <;> simp [liftRel, adj] <;> grind

theorem noFour (R : P → L → Prop) (m : P ⊕ L → P ⊕ L)
    (h : NoFour R)
    (indep : ∀ u v, m u = u → m v = v → ¬ adj R u v) :
    NoFour (liftRel R m) := by
  intro a b c d
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [liftRel, adj] <;> unfold NoFour at h <;> grind [adj]

theorem perfect (R : P → L → Prop) (m : P ⊕ L → P ⊕ L)
    (inv : Function.Involutive m) (edges : ∀ u, m u ≠ u → adj R u (m u)) :
    Function.Bijective m ∧ ∀ u, liftRel R m u (m u) := by
  refine ⟨inv.bijective, fun u => ?_⟩
  by_cases h : m u = u
  · exact Or.inr ⟨h.symm,h⟩
  · exact Or.inl (edges u h)

abbrev Inc {A B : Type*} (r : A → B → Prop) := {e : A × B // r e.1 e.2}
abbrev Fixed {A : Type*} (m : A → A) := {a // m a = a}

def incEquiv (R : P → L → Prop) (m : P ⊕ L → P ⊕ L) :
    Inc (liftRel R m) ≃ (Inc R ⊕ Inc R) ⊕ Fixed m where
  toFun
    | ⟨(.inl p, .inr l), h⟩ => .inl (.inl ⟨(p,l), by simpa [liftRel, adj] using h⟩)
    | ⟨(.inr l, .inl p), h⟩ => .inl (.inr ⟨(p,l), by simpa [liftRel, adj] using h⟩)
    | ⟨(.inl p, .inl _), h⟩ => .inr ⟨.inl p, h.resolve_left (by simp [adj]) |>.2⟩
    | ⟨(.inr l, .inr _), h⟩ => .inr ⟨.inr l, h.resolve_left (by simp [adj]) |>.2⟩
  invFun
    | .inl (.inl ⟨(p,l), h⟩) => ⟨(.inl p,.inr l), Or.inl h⟩
    | .inl (.inr ⟨(p,l), h⟩) => ⟨(.inr l,.inl p), Or.inl h⟩
    | .inr ⟨u,h⟩ => ⟨(u,u), Or.inr ⟨rfl,h⟩⟩
  left_inv := by
    rintro ⟨⟨u,v⟩, h⟩
    cases u <;> cases v <;> apply Subtype.ext <;> simp <;>
      first | exact Sum.inl.inj ((h.resolve_left (by simp [adj])).1)
            | exact Sum.inr.inj ((h.resolve_left (by simp [adj])).1)
  right_inv := by
    rintro ((⟨⟨p,l⟩,h⟩ | ⟨⟨p,l⟩,h⟩) | ⟨u,h⟩)
    · rfl
    · rfl
    · cases u <;> rfl

theorem edges_card (R : P → L → Prop) (m : P ⊕ L → P ⊕ L)
    [Fintype (Inc (liftRel R m))] [Fintype (Inc R)] [Fintype (Fixed m)] :
    Fintype.card (Inc (liftRel R m)) = 2 * Fintype.card (Inc R) + Fintype.card (Fixed m) := by
  simpa [two_mul] using Fintype.card_congr (incEquiv R m)

abbrev Matched (m : P ⊕ L → P ⊕ L) := {e : P × L // m (.inl e.1) = .inr e.2}

def endpoint (m : P ⊕ L → P ⊕ L) : (Matched m ⊕ Matched m) ⊕ Fixed m → P ⊕ L
  | .inl (.inl e) => .inl e.val.1
  | .inl (.inr e) => .inr e.val.2
  | .inr u => u.val

theorem endpoint_bijective (R : P → L → Prop) (m : P ⊕ L → P ⊕ L)
    (inv : Function.Involutive m) (edges : ∀ u, m u ≠ u → adj R u (m u)) :
    Function.Bijective (endpoint m) := by
  have hback : ∀ (p : P) (l : L), m (.inl p) = .inr l → m (.inr l) = .inl p := by
    intro p l h
    rw [← h, inv]
  constructor
  · rintro ((⟨⟨p,l⟩, hp⟩ | ⟨⟨p,l⟩, hp⟩) | ⟨u,hu⟩)
        ((⟨⟨q,t⟩, hq⟩ | ⟨⟨q,t⟩, hq⟩) | ⟨v,hv⟩) <;>
      simp_all [endpoint] <;> grind
  · intro u
    by_cases h : m u = u
    · exact ⟨.inr ⟨u,h⟩,rfl⟩
    have he := edges u h
    cases u with
    | inl p =>
      cases hm : m (.inl p) with
      | inl q => simp [hm, adj] at he
      | inr l => exact ⟨.inl (.inl ⟨(p,l),hm⟩),rfl⟩
    | inr l =>
      cases hm : m (.inr l) with
      | inr t => simp [hm, adj] at he
      | inl p =>
        have hp : m (.inl p) = .inr l := by rw [← hm, inv]
        exact ⟨.inl (.inr ⟨(p,l),hp⟩),rfl⟩

theorem shore_card (R : P → L → Prop) (m : P ⊕ L → P ⊕ L)
    (inv : Function.Involutive m) (edges : ∀ u, m u ≠ u → adj R u (m u))
    [Fintype (P ⊕ L)] [Fintype (Matched m)] [Fintype (Fixed m)] :
    Fintype.card (P ⊕ L) = 2 * Fintype.card (Matched m) + Fintype.card (Fixed m) := by
  simpa [two_mul] using (Fintype.card_congr
    (Equiv.ofBijective _ (endpoint_bijective R m inv edges))).symm

theorem degree_ge (R : P → L → Prop) (m : P ⊕ L → P ⊕ L) (u : P ⊕ L)
    [Fintype {v // adj R u v}] [Fintype {v // liftRel R m u v}] :
    Fintype.card {v // adj R u v} ≤ Fintype.card {v // liftRel R m u v} := by
  apply Fintype.card_le_of_injective (fun v => ⟨v.val, Or.inl v.property⟩)
  exact fun _ _ h => Subtype.ext (congrArg (fun (w : {v // liftRel R m u v}) => w.val) h)

end SymmetricIncidence
