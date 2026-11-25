import Mathlib

/-! Finite monotone formulas induce rectangular partitions of separating row pairs. -/
namespace FormulaRectPartition

inductive Formula (V : Type) where
  | var : V → Formula V
  | conj : Formula V → Formula V → Formula V
  | disj : Formula V → Formula V → Formula V

def Formula.eval (x : V → Bool) : Formula V → Bool
  | .var v => x v
  | .conj a b => a.eval x && b.eval x
  | .disj a b => a.eval x || b.eval x

def Formula.leaves : Formula V → ℕ
  | .var _ => 1
  | .conj a b | .disj a b => a.leaves + b.leaves

structure Rect (V P Q : Type) where
  var : V
  rows : Finset P
  cols : Finset Q
  deriving DecidableEq

variable {V P Q : Type} [DecidableEq V] [DecidableEq P] [DecidableEq Q]

def Hits (R : Rect V P Q) (p : P) (q : Q) := p ∈ R.rows ∧ q ∈ R.cols

structure Part (pos : P → V → Bool) (neg : Q → V → Bool) (s : Finset P) (t : Finset Q)
    (d : Finset (Rect V P Q)) : Prop where
  valid : ∀ R ∈ d, R.rows.Nonempty ∧ R.cols.Nonempty ∧ R.rows ⊆ s ∧ R.cols ⊆ t ∧
    (∀ p ∈ R.rows, pos p R.var = true) ∧ (∀ q ∈ R.cols, neg q R.var = false)
  cover : ∀ p ∈ s, ∀ q ∈ t, ∃! R, R ∈ d ∧ Hits R p q

variable {pos : P → V → Bool} {neg : Q → V → Bool}
variable {s s₁ s₂ : Finset P} {t t₁ t₂ : Finset Q} {d₁ d₂ : Finset (Rect V P Q)}

private theorem Part.glue
    (h₁ : Part pos neg s₁ t₁ d₁) (h₂ : Part pos neg s₂ t₂ d₂)
    (ss₁ : s₁ ⊆ s) (ss₂ : s₂ ⊆ s) (tt₁ : t₁ ⊆ t) (tt₂ : t₂ ⊆ t)
    (covers : ∀ p ∈ s, ∀ q ∈ t, (p ∈ s₁ ∧ q ∈ t₁) ∨ (p ∈ s₂ ∧ q ∈ t₂))
    (apart : ∀ p q, p ∈ s₁ → q ∈ t₁ → p ∈ s₂ → q ∈ t₂ → False) :
    Part pos neg s t (d₁ ∪ d₂) := by
  constructor
  · intro R hR
    rcases Finset.mem_union.mp hR with hR | hR
    · obtain ⟨a,b,c,d,e,f⟩ := h₁.valid R hR
      exact ⟨a,b,c.trans ss₁,d.trans tt₁,e,f⟩
    · obtain ⟨a,b,c,d,e,f⟩ := h₂.valid R hR
      exact ⟨a,b,c.trans ss₂,d.trans tt₂,e,f⟩
  · intro p hp q hq
    rcases covers p hp q hq with ⟨a,b⟩ | ⟨a,b⟩
    · obtain ⟨R,⟨mem,hit⟩,uniq⟩ := h₁.cover p a q b
      refine ⟨R,⟨Finset.mem_union_left _ mem,hit⟩,?_⟩
      rintro U ⟨m,h⟩
      rcases Finset.mem_union.mp m with m | m
      · exact uniq U ⟨m,h⟩
      · obtain ⟨_,_,hs,ht,_,_⟩ := h₂.valid U m
        exact (apart p q a b (hs h.1) (ht h.2)).elim
    · obtain ⟨R,⟨mem,hit⟩,uniq⟩ := h₂.cover p a q b
      refine ⟨R,⟨Finset.mem_union_right _ mem,hit⟩,?_⟩
      rintro U ⟨m,h⟩
      rcases Finset.mem_union.mp m with m | m
      · obtain ⟨_,_,hs,ht,_,_⟩ := h₁.valid U m
        exact (apart p q (hs h.1) (ht h.2) a b).elim
      · exact uniq U ⟨m,h⟩

/-- Rectangles with nonempty sides, one per active leaf at most. -/
theorem formula_partition (f : Formula V) (s : Finset P) (t : Finset Q)
    (hp : ∀ p ∈ s, f.eval (pos p) = true) (hq : ∀ q ∈ t, f.eval (neg q) = false) :
    ∃ d, Part pos neg s t d ∧ d.card ≤ f.leaves := by
  classical
  induction f generalizing s t with
  | var v =>
    by_cases hs : s.Nonempty
    · by_cases ht : t.Nonempty
      · let R : Rect V P Q := ⟨v,s,t⟩
        refine ⟨{R},⟨?_,?_⟩,by simp [Formula.leaves]⟩
        · intro U h
          have e := Finset.mem_singleton.mp h
          subst U
          exact ⟨hs,ht,(fun _ h => h),(fun _ h => h),hp,hq⟩
        · intro p a q b
          exact ⟨R,⟨Finset.mem_singleton_self R,a,b⟩,fun U h => Finset.mem_singleton.mp h.1⟩
      · refine ⟨∅,⟨by simp,?_⟩,by simp⟩
        intro p _ q h
        exact (ht ⟨q,h⟩).elim
    · refine ⟨∅,⟨by simp,?_⟩,by simp⟩
      intro p h
      exact (hs ⟨p,h⟩).elim
  | conj a b ia ib =>
    let t₁ := t.filter fun q => a.eval (neg q) = false
    let t₂ := t.filter fun q => a.eval (neg q) = true
    obtain ⟨d₁,h₁,n₁⟩ := ia s t₁ (fun p h => (Bool.and_eq_true_iff.mp (hp p h)).1)
      (fun _ h => (Finset.mem_filter.mp h).2)
    obtain ⟨d₂,h₂,n₂⟩ := ib s t₂ (fun p h => (Bool.and_eq_true_iff.mp (hp p h)).2) (by
      intro q h
      obtain ⟨hmem,ha⟩ := Finset.mem_filter.mp h
      simpa [Formula.eval,ha] using hq q hmem)
    refine ⟨d₁ ∪ d₂,h₁.glue h₂ (fun _ h => h) (fun _ h => h) (Finset.filter_subset _ _)
      (Finset.filter_subset _ _) ?_ ?_,(Finset.card_union_le _ _).trans (Nat.add_le_add n₁ n₂)⟩
    · intro p ps q qt
      cases h : a.eval (neg q) <;> simp [t₁,t₂,h,ps,qt]
    · intro p q _ h₁ _ h₂
      exact Bool.noConfusion ((Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2)
  | disj a b ia ib =>
    let s₁ := s.filter fun p => a.eval (pos p) = true
    let s₂ := s.filter fun p => a.eval (pos p) = false
    obtain ⟨d₁,h₁,n₁⟩ := ia s₁ t (fun _ h => (Finset.mem_filter.mp h).2)
      (fun q h => (Bool.or_eq_false_iff.mp (hq q h)).1)
    obtain ⟨d₂,h₂,n₂⟩ := ib s₂ t (by
      intro p h
      obtain ⟨hmem,ha⟩ := Finset.mem_filter.mp h
      simpa [Formula.eval,ha] using hp p hmem)
      (fun q h => (Bool.or_eq_false_iff.mp (hq q h)).2)
    refine ⟨d₁ ∪ d₂,h₁.glue h₂ (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (fun _ h => h) (fun _ h => h) ?_ ?_,(Finset.card_union_le _ _).trans (Nat.add_le_add n₁ n₂)⟩
    · intro p ps q qt
      cases h : a.eval (pos p) <;> simp [s₁,s₂,h,ps,qt]
    · intro p q h₁ _ h₂ _
      exact Bool.noConfusion ((Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2)


abbrev Key (V P : Type) := V × Finset P

def key (R : Rect V P Q) : Key V P := (R.var,R.rows)

def keys (d : Finset (Rect V P Q)) := d.image key

def columns (d : Finset (Rect V P Q)) (k : Key V P) : Finset Q :=
  (d.filter fun R => key R = k).biUnion Rect.cols

theorem mem_columns {d : Finset (Rect V P Q)} {k : Key V P} {q : Q} :
    q ∈ columns d k ↔ ∃ R ∈ d, key R = k ∧ q ∈ R.cols := by
  simp only [columns,Finset.mem_biUnion,Finset.mem_filter]
  aesop

/-- Conditions on the used rectangle types and their assigned columns.
    These are the semantic conditions in the finite rectangle-partition encoding. -/
structure Packed (pos : P → V → Bool) (neg : Q → V → Bool) (s : Finset P) (t : Finset Q)
    (K : Finset (Key V P)) (col : Key V P → Finset Q) : Prop where
  admissible : ∀ k ∈ K, k.2.Nonempty ∧ k.2 ⊆ s ∧ (∀ p ∈ k.2, pos p k.1 = true)
  assigned : ∀ k ∈ K, (col k).Nonempty ∧ col k ⊆ t ∧ (∀ q ∈ col k, neg q k.1 = false)
  unused : ∀ k ∉ K, col k = ∅
  exactlyOne : ∀ p ∈ s, ∀ q ∈ t, ∃! k, k ∈ K ∧ p ∈ k.2 ∧ q ∈ col k

theorem merge_partition {d : Finset (Rect V P Q)} (h : Part pos neg s t d) :
    Packed pos neg s t (keys d) (columns d) ∧ (keys d).card ≤ d.card := by
  refine ⟨⟨?_,?_,?_,?_⟩, Finset.card_image_le⟩
  · intro k hk
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨ne,_,inc,_,bits,_⟩ := h.valid R hR
    exact ⟨ne,inc,bits⟩
  · intro k hk
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨q,hq⟩ := (h.valid R hR).2.1
    refine ⟨⟨q,mem_columns.mpr ⟨R,hR,rfl,hq⟩⟩,?_,?_⟩
    · intro q hq
      obtain ⟨U,hU,_,hcol⟩ := mem_columns.mp hq
      exact (h.valid U hU).2.2.2.1 hcol
    · intro q hq
      obtain ⟨U,hU,eq,hcol⟩ := mem_columns.mp hq
      rw [← eq]
      exact (h.valid U hU).2.2.2.2.2 q hcol
  · intro k hk
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨R,hR,e,_⟩ := mem_columns.mp hq
    exact hk (Finset.mem_image.mpr ⟨R,hR,e⟩)
  · intro p hp q hq
    obtain ⟨R,⟨hR,pr,qr⟩,uniq⟩ := h.cover p hp q hq
    refine ⟨key R,⟨Finset.mem_image.mpr ⟨R,hR,rfl⟩,pr,mem_columns.mpr ⟨R,hR,rfl,qr⟩⟩,?_⟩
    rintro k ⟨_,pk,qk⟩
    obtain ⟨U,hU,rfl,qu⟩ := mem_columns.mp qk
    exact congrArg key (uniq U ⟨hU,pk,qu⟩)

/-- The number of selected (coordinate, exact positive subset) types is at most the raw leaf count. -/
theorem formula_packed (f : Formula V) (s : Finset P) (t : Finset Q)
    (hp : ∀ p ∈ s, f.eval (pos p) = true) (hq : ∀ q ∈ t, f.eval (neg q) = false) :
    ∃ K col, Packed pos neg s t K col ∧ K.card ≤ f.leaves := by
  obtain ⟨d,part,bound⟩ := formula_partition f s t hp hq
  obtain ⟨packed,small⟩ := merge_partition part
  exact ⟨_,_,packed,small.trans bound⟩

def Formula.gates : Formula V → ℕ
  | .var _ => 0
  | .conj a b | .disj a b => a.gates + b.gates + 1

omit [DecidableEq V] in
theorem Formula.leaves_eq_gates_add_one (f : Formula V) : f.leaves = f.gates + 1 := by
  induction f with
  | var _ => rfl
  | conj a b ha hb => simp only [leaves,gates,ha,hb]; omega
  | disj a b ha hb => simp only [leaves,gates,ha,hb]; omega

namespace G11

def positiveRows : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
def negativeRows : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]

def positive (i : Fin 16) (v : Fin 11) := (positiveRows.getD i.val 0).testBit v.val
def negative (j : Fin 24) (v : Fin 11) := (negativeRows.getD j.val 0).testBit v.val

/-- The semantic finite search. Types are exactly (raw coordinate, set of positive row indices). -/
def AtMost (limit : ℕ) : Prop :=
  ∃ K col, Packed positive negative Finset.univ Finset.univ K col ∧ K.card ≤ limit

theorem of_separating (f : Formula (Fin 11)) (hp : ∀ i, f.eval (positive i) = true)
    (hq : ∀ j, f.eval (negative j) = false) : AtMost f.leaves :=
  formula_packed f _ _ (fun i _ => hp i) (fun j _ => hq j)

theorem gate_lower (reject : ¬ AtMost 22) (f : Formula (Fin 11))
    (hp : ∀ i, f.eval (positive i) = true) (hq : ∀ j, f.eval (negative j) = false) :
    22 ≤ f.gates := by
  obtain ⟨K,col,h,small⟩ := of_separating f hp hq
  have hleaf := f.leaves_eq_gates_add_one
  by_contra! short
  exact reject ⟨K,col,h,by omega⟩

end G11

#print axioms G11.gate_lower
#print axioms formula_partition
#print axioms merge_partition
#print axioms formula_packed
end FormulaRectPartition
