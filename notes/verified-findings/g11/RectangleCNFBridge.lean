import FormulaRectPartition
import Std.Tactic.BVDecide.LRAT

/-! A semantic checker for the physical rectangle CNF and its totalizer auxiliary variables.
    Each satisfying partition extends to the assignment used by this checker. -/
namespace RectangleCNFBridge
open FormulaRectPartition
abbrev KType := Key (Fin 11) (Fin 16)
abbrev QType := Fin 24

inductive Atom where
  | used (k : KType)
  | member (k : KType) (q : QType)
  | counter (s : Finset KType) (i : Nat)
  | unused
  deriving DecidableEq

abbrev Lit := Atom × Bool
abbrev Count := Finset KType × Nat

def selectionCount (K S : Finset KType) := (S ∩ K).card

def arithmetic : Atom → Option Count
  | .used k => some ({k},1)
  | .counter s i => some (s,i)
  | _ => none

def val (K : Finset KType) (col : KType → Finset QType) : Atom → Bool
  | .used k => decide (k ∈ K)
  | .member k q => decide (q ∈ col k)
  | .counter s i => decide (i ≤ selectionCount K s)
  | .unused => false

def TrueClause (a : Atom → Bool) (row : List Lit) := ∃ l ∈ row, a l.1 = l.2

theorem arith_iff {K : Finset KType} {col : KType → Finset QType} {a : Atom} {c : Count}
    (h : arithmetic a = some c) :
    val K col a = true ↔ c.2 ≤ selectionCount K c.1 := by
  cases a with
  | used k =>
    simp only [arithmetic, Option.some.injEq] at h
    subst c
    by_cases hk : k ∈ K <;> simp [val,selectionCount,hk]
  | counter S i =>
    simp only [arithmetic,Option.some.injEq] at h
    subst c
    simp [val]
  | member => simp [arithmetic] at h
  | unused => simp [arithmetic] at h

theorem counts_mono {K s t : Finset KType} (h : s ⊆ t) : selectionCount K s ≤ selectionCount K t :=
  Finset.card_le_card (Finset.inter_subset_inter h (by rfl))

theorem counts_add {K s t u : Finset KType} (ds : Disjoint s t) (hs : s ⊆ u) (ht : t ⊆ u) :
    selectionCount K s + selectionCount K t ≤ selectionCount K u := by
  have dis : Disjoint (s ∩ K) (t ∩ K) :=
    ds.mono Finset.inter_subset_left Finset.inter_subset_left
  rw [selectionCount,selectionCount,← Finset.card_union_of_disjoint dis]
  apply Finset.card_le_card
  intro x hx
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨a,b⟩ := Finset.mem_inter.mp h
    exact Finset.mem_inter.mpr ⟨hs a,b⟩
  · obtain ⟨a,b⟩ := Finset.mem_inter.mp h
    exact Finset.mem_inter.mpr ⟨ht a,b⟩

def possible (v : Fin 11) := (Finset.univ : Finset (Fin 16)).filter fun p => G11.positive p v = true

/-- Only subsets of the incident positive rows are enumerated. -/
def rowKeys (p : Fin 16) (q : QType) : List KType :=
  (List.finRange 11).flatMap fun v =>
    if G11.negative q v = false then
      (((((possible v).sort).sublists.map List.toFinset).filter fun s => p ∈ s)).map fun s => (v,s)
    else []

theorem catalogued {K col} (h : Packed G11.positive G11.negative Finset.univ Finset.univ K col)
    {p : Fin 16} {q : QType} {k : KType} (hk : k ∈ K) (hp : p ∈ k.2) (hq : q ∈ col k) :
    k ∈ rowKeys p q := by
  obtain ⟨_,_,hx⟩ := h.admissible k hk
  obtain ⟨_,_,hy⟩ := h.assigned k hk
  obtain ⟨v,s⟩ := k
  apply List.mem_flatMap.mpr
  refine ⟨v,List.mem_finRange _,?_⟩
  have sub : s ⊆ possible v := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx i hi⟩
  let ls := (possible v).sort.filter fun i => i ∈ s
  have he : ls.toFinset = s := by
    ext i
    simp [ls, and_iff_right_of_imp (fun h => sub h)]
  simp only [hy q hq,ite_true,List.mem_map,List.mem_filter,decide_eq_true_eq]
  refine ⟨s,⟨⟨ls,?_,he⟩,hp⟩,rfl⟩
  exact List.mem_sublists.mpr List.filter_sublist

inductive Rule where
  | link | occupied | apart | carry | bound
  | cell (p : Fin 16) (q : QType)
  deriving Repr, DecidableEq

def check (cap : Nat) : Rule → List Lit → Bool
  | .link, [(.member k _,false),(.used l,true)] => decide (k = l)
  | .occupied, (.used k,false) :: rest =>
    (List.finRange 24).all fun q => G11.negative q k.1 || rest.contains (.member k q,true)
  | .cell p q, row => (rowKeys p q).all fun k => row.contains (.member k q,true)
  | .apart, [(.member k q,false),(.member l r,false)] =>
    decide (k ≠ l ∧ q = r ∧ (k.2 ∩ l.2).Nonempty)
  | .carry, [(x,false),(z,true)] =>
    match arithmetic x, arithmetic z with
    | some a, some c => decide (a.1 ⊆ c.1 ∧ c.2 ≤ a.2)
    | _,_ => false
  | .carry, [(x,false),(y,false),(z,true)] =>
    match arithmetic x, arithmetic y, arithmetic z with
    | some a, some b, some c =>
      decide (a.1 ⊆ c.1 ∧ b.1 ⊆ c.1 ∧ Disjoint a.1 b.1 ∧ c.2 ≤ a.2+b.2)
    | _,_,_ => false
  | .bound, [(x,false)] =>
    match arithmetic x with
    | some a => decide (cap < a.2)
    | _ => false
  | _,_ => false

theorem check_sound {K col cap} (good : Packed G11.positive G11.negative Finset.univ Finset.univ K col)
    (small : K.card ≤ cap) (r : Rule) (c : List Lit) (ok : check cap r c = true) :
    TrueClause (val K col) c := by
  have used_of {k : KType} {q : QType} (hq : q ∈ col k) : k ∈ K := by
    by_contra hn
    simp [good.unused k hn] at hq
  fun_cases check cap r c <;> simp_all only [check,Bool.false_eq_true,decide_eq_true_eq]
  case case1 k q l =>
    by_cases used : l ∈ K
    · exact ⟨(.used l,true),by simp,by simp [val,used]⟩
    · exact ⟨(.member l q,false),by simp,by simp [val,good.unused l used]⟩
  case case2 k rest =>
    by_cases hk : k ∈ K
    · obtain ⟨⟨q,hq⟩,_,bits⟩ := good.assigned k hk
      have hit := List.all_eq_true.mp ok q (List.mem_finRange _)
      simp only [bits q hq,Bool.false_or,List.contains_iff_mem] at hit
      exact ⟨_,List.mem_cons_of_mem _ hit,by simpa [val] using hq⟩
    · exact ⟨(.used k,false),by simp,by simp [val,hk]⟩
  case case3 p q =>
    obtain ⟨k,⟨hk,hp,hq⟩,_⟩ := good.exactlyOne p (Finset.mem_univ _) q (Finset.mem_univ _)
    have hit := List.all_eq_true.mp ok k (catalogued good hk hp hq)
    exact ⟨_,List.contains_iff_mem.mp hit,by simpa [val] using hq⟩
  case case4 k q l r =>
    obtain ⟨hne,_,p,hp⟩ := ok
    obtain ⟨hk,hl⟩ := Finset.mem_inter.mp hp
    by_cases p₁ : r ∈ col k
    · have p₂ : r ∉ col l := by
        intro hlq
        obtain ⟨U,_,u⟩ := good.exactlyOne p (Finset.mem_univ _) r (Finset.mem_univ _)
        exact hne ((u k ⟨used_of p₁,hk,p₁⟩).trans (u l ⟨used_of hlq,hl,hlq⟩).symm)
      exact ⟨(.member l r,false),by simp,by simp [val,p₂]⟩
    · exact ⟨(.member k r,false),by simp,by simp [val,p₁]⟩
  case case5 x z a d hz hx =>
    by_cases vx : val K col x = true
    · refine ⟨(z,true),by simp,(arith_iff hz).mpr ?_⟩
      exact ok.2.trans (((arith_iff hx).mp vx).trans (counts_mono ok.1))
    · exact ⟨(x,false),by simp,Bool.eq_false_iff.mpr vx⟩
  case case7 x y z a b d hz hy hx =>
    by_cases vx : val K col x = true
    · by_cases vy : val K col y = true
      · refine ⟨(z,true),by simp,(arith_iff hz).mpr ?_⟩
        exact ok.2.2.2.trans ((Nat.add_le_add ((arith_iff hx).mp vx) ((arith_iff hy).mp vy)).trans
          (counts_add ok.2.2.1 ok.1 ok.2.1))
      · exact ⟨(y,false),by simp,Bool.eq_false_iff.mpr vy⟩
    · exact ⟨(x,false),by simp,Bool.eq_false_iff.mpr vx⟩
  case case9 x a hx =>
    refine ⟨(x,false),by simp,Bool.eq_false_iff.mpr ?_⟩
    intro vx
    have lo := (arith_iff hx).mp vx
    have hi : selectionCount K a.1 ≤ cap :=
      (Finset.card_le_card Finset.inter_subset_right).trans small
    omega

open Std.Sat Std.Tactic.BVDecide

def annotated (decode : Nat → Atom) (c : CNF.Clause Nat) : List Lit :=
  c.literals.map fun l => (decode l.1,l.2)

/-- The verifier checks every literal against the actual physical CNF passed to LRAT. -/
def validates (cap : Nat) (decode : Nat → Atom) (rule : Nat → Rule) (f : CNF Nat) : Bool :=
  (List.finRange f.clauses.size).all fun i => check cap (rule i) (annotated decode f.clauses[i])

theorem packed_sat {cap : Nat} (d : Nat → Atom) (rule : Nat → Rule) (f : CNF Nat)
    (checked : validates cap d rule f = true) (part : G11.AtMost cap) :
    ∃ a, f.eval a = true := by
  obtain ⟨K,col,packed,small⟩ := part
  refine ⟨fun n => val K col (d n),?_⟩
  apply Array.all_eq_true_iff_forall_mem.mpr
  intro c hc
  obtain ⟨i,hi,rfl⟩ := Array.getElem_of_mem hc
  have ok := List.all_eq_true.mp checked (⟨i,hi⟩ : Fin _) (List.mem_finRange _)
  obtain ⟨lit,mem,truth⟩ := check_sound packed small _ _ ok
  obtain ⟨raw,hraw,eq⟩ := List.mem_map.mp mem
  subst lit
  exact List.any_eq_true.mpr ⟨raw,hraw,by simpa using truth⟩

theorem certified_lower (d : Nat → Atom) (r : Nat → Rule) (f : CNF Nat) (proof : Array LRAT.IntAction)
    (bridge : validates 22 d r f = true) (lrat : LRAT.check proof f = true) : ¬ G11.AtMost 22 := by
  intro part
  obtain ⟨a,h⟩ := packed_sat d r f bridge part
  exact CNF.unsat_iff_not_sat.mp (LRAT.check_sound proof f lrat) a h

#print axioms check_sound
#print axioms packed_sat
#print axioms certified_lower
end RectangleCNFBridge
