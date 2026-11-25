import FormulaRectPartition
import PEqualNP.Outside.L_meta_3140

/-! A read-once residual circuit above one exposed shared wire. -/
namespace SingleSharedFormula
open FormulaRectPartition

structure Instruction where
  isAnd : Bool
  left : ℕ
  right : ℕ

def children (step : ℕ → Instruction) (w : ℕ) := [(step w).left,(step w).right]

def contacts (nodes : List ℕ) (step : ℕ → Instruction) (out : ℕ) :=
  out :: nodes.flatMap (children step)

def combine (op : Bool) (a b : Formula V) : Formula V := if op then .conj a b else .disj a b

def tree (raw : ℕ → V) (nodes : List ℕ) (step : ℕ → Instruction) (w : ℕ) : Formula V :=
  if _h : w ∈ nodes ∧ (step w).left < w ∧ (step w).right < w then
    combine (step w).isAnd (tree raw nodes step (step w).left) (tree raw nodes step (step w).right)
  else .var (raw w)
termination_by w

private theorem sum_contacts (nodes xs : List ℕ) (W : ℕ → ℕ)
    (outside : ∀ w, w ∉ nodes → W w = 0)
    (linear : (xs.filter fun w => w ∈ nodes).Nodup) :
    (xs.map W).sum ≤ (nodes.map W).sum := by
  let ys := xs.filter fun w => w ∈ nodes
  have sub : ys ⊆ nodes := fun _ h => of_decide_eq_true (List.mem_filter.mp h).2
  obtain ⟨zs,hz,hs⟩ := List.subperm_of_subset linear sub
  have le := (hs.map W).sum_le_sum (fun _ _ => Nat.zero_le _)
  rw [(hz.map W).sum_eq] at le
  have skip (as : List ℕ) : ((as.filter fun w => decide (w ∈ nodes)).map W).sum = (as.map W).sum := by
    induction as with
    | nil => rfl
    | cons w ws ih => by_cases h : w ∈ nodes <;> simp [h,ih,outside]
  simpa only [ys,skip] using le

/-- Count each physical contact, including the final output read. A residual gate can occur
    in at most one of these slots. Boundary wires have zero formula-gate cost. -/
theorem tree_cost (raw : ℕ → V) (nodes : List ℕ) (step : ℕ → Instruction) (out : ℕ)
    (earlier : ∀ w ∈ nodes, (step w).left < w ∧ (step w).right < w)
    (linear : ((contacts nodes step out).filter fun w => w ∈ nodes).Nodup) :
    (tree raw nodes step out).gates ≤ nodes.length := by
  let W := fun w => (tree raw nodes step w).gates
  have zero (w : ℕ) (hw : w ∉ nodes) : W w = 0 := by
    change (tree raw nodes step w).gates = 0
    rw [tree,dite_eq_right (by simp [hw])]
    rfl
  have expand (w : ℕ) (hw : w ∈ nodes) :
      W w = W (step w).left + W (step w).right + 1 := by
    rw [show W w = (tree raw nodes step w).gates from rfl,tree, dite_eq_left ⟨hw,earlier w hw⟩]
    cases h : (step w).isAnd <;> simp [combine,Formula.gates,W]
  have cancel (xs : List ℕ) (sub : xs ⊆ nodes) :
      (xs.map W).sum = ((xs.flatMap (children step)).map W).sum + xs.length := by
    induction xs with
    | nil => rfl
    | cons a as ih =>
      have ha := expand a (sub (by simp))
      have h := ih (fun x hx => sub (by simp [hx]))
      simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.map_append,List.sum_append,
        List.length_cons,children,List.map_nil,List.sum_nil,Nat.add_zero]
      omega
  have le := sum_contacts nodes (contacts nodes step out) W zero linear
  rw [cancel nodes (fun _ h => h)] at le
  change W out + ((nodes.flatMap (children step)).map W).sum ≤ _ at le
  change W out ≤ _
  omega

def applyOp (op a b : Bool) := if op then a && b else a || b

theorem tree_semantics (raw : ℕ → V) (nodes : List ℕ) (step : ℕ → Instruction) (out : ℕ)
    (earlier : ∀ w ∈ nodes, (step w).left < w ∧ (step w).right < w)
    (x : V → Bool) (signal : ℕ → Bool)
    (boundary : ∀ w ∈ contacts nodes step out, w ∉ nodes → x (raw w) = signal w)
    (inside : ∀ w ∈ nodes, signal w = applyOp (step w).isAnd (signal (step w).left) (signal (step w).right)) :
    (tree raw nodes step out).eval x = signal out := by
  have eval (w : ℕ) : w ∈ contacts nodes step out → (tree raw nodes step w).eval x = signal w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro used
      by_cases h : w ∈ nodes
      · rw [tree,dite_eq_left ⟨h,earlier w h⟩,inside w h]
        have children_in (v : ℕ) (hv : v ∈ children step w) : v ∈ contacts nodes step out :=
          List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨w,h,hv⟩)
        have a := ih _ (earlier w h).1 (children_in _ (by simp [children]))
        have b := ih _ (earlier w h).2 (children_in _ (by simp [children]))
        cases hop : (step w).isAnd <;> simp [combine,applyOp,Formula.eval,a,b]
      · rw [tree,dite_eq_right (by simp [h])]
        exact boundary w used h
  exact eval out (by simp [contacts])

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3140

def physical (n : ℕ) (C : Circuit) (w : ℕ) : Instruction :=
  let g := gateAt C (w-n)
  ⟨g.op.eval [],g.inputs.getD 0 0,g.inputs.getD 1 0⟩

def residual (n : ℕ) (C : Circuit) (prep : Finset (Fin C.size)) : List ℕ :=
  ((Finset.univ \ prep).sort).map fun i => n+i.val

def atom (n w : ℕ) : Fin n ⊕ Unit := if h : w<n then .inl ⟨w,h⟩ else .inr ()

def extended (C : Circuit) {n : ℕ} (h : ℕ) (x : Fin n → Bool) : Fin n ⊕ Unit → Bool :=
  Sum.elim x (fun _ => value C x h)

theorem physical_gate (n : ℕ) (C : Circuit) (ao : TopForm.IsAO2 n C) (j : Fin C.size) :
    let g := physical n C (n+j.val)
    (g.left < n+j.val ∧ g.right < n+j.val) ∧
    ∀ x : Fin n → Bool, value C x (n+j.val) = applyOp g.isAnd (value C x g.left) (value C x g.right) := by
  let g := gateAt C j.val
  have hg : g ∈ C.gates := by rw [show g = C.gates[j.val] from gateActual ..]; exact List.getElem_mem _
  obtain ⟨a,b,ab⟩ := List.length_eq_two.mp (ao.2.2 g hg)
  have earlier (w : ℕ) (hw : w ∈ [a,b]) : w < n+j.val :=
    ao.2.1 j.val j.isLt w (by simpa [← ab,g] using hw)
  dsimp only [physical]
  simp only [Nat.add_sub_cancel_left]
  change ((g.inputs.getD 0 0 < n+j.val) ∧ (g.inputs.getD 1 0 < n+j.val)) ∧ _
  constructor
  · simpa [ab] using And.intro (earlier a (by simp)) (earlier b (by simp))
  · intro x
    have rel := realGate C ao.2.1 x j.val j.isLt
    change value C x (n+j.val) = g.op.eval (g.inputs.map _) at rel
    rcases ao.1 g hg with op | op <;>
      simpa [g,ab,op,GateOp.eval,applyOp] using rel

def sharesOnly (n : ℕ) (C : Circuit) (z : ℕ) (nodes : List ℕ) : Prop :=
  (∀ w ∈ contacts nodes (physical n C) C.output, w ∉ nodes → w<n ∨ w=z) ∧
  ((contacts nodes (physical n C) C.output).filter fun w => w ∈ nodes).Nodup

/-- All observed residual boundary contacts are raw inputs or the one named wire.
    Nonraw residual contacts, including the output read, have multiplicity at most one. -/
theorem physical_residual {n : ℕ} (C : Circuit) (ao : TopForm.IsAO2 n C)
    (prep : Finset (Fin C.size)) (z : Fin C.size) (cut : sharesOnly n C (n+z.val) (residual n C prep)) :
    ∃ f : Formula (Fin n ⊕ Unit), f.gates + prep.card ≤ C.size ∧
      ∀ x : Fin n → Bool, f.eval (extended C (n+z.val) x) = C.eval (List.ofFn x) := by
  let nodes := residual n C prep
  let step := physical n C
  have source (w : ℕ) (hw : w ∈ nodes) : ∃ j : Fin C.size, n+j.val = w := by
    obtain ⟨j,_,e⟩ := List.mem_map.mp hw
    exact ⟨j,e⟩
  have back (w : ℕ) (hw : w ∈ nodes) : (step w).left < w ∧ (step w).right < w := by
    obtain ⟨j,rfl⟩ := source w hw
    exact (physical_gate n C ao j).1
  have sz : nodes.length + prep.card = C.size := by
    simpa [nodes,residual] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ prep)
  refine ⟨tree (atom n) nodes step C.output,?_,?_⟩
  · have hc := tree_cost (atom n) nodes step C.output back cut.2
    omega
  · intro x
    apply tree_semantics (atom n) nodes step C.output back _ (value C x)
    · intro w used hw
      rcases cut.1 w used hw with b | rfl
      · simpa [extended,atom,b] using (input_value C x ⟨w,b⟩).symm
      · simp [extended,atom]
    · intro w hw
      obtain ⟨j,rfl⟩ := source w hw
      exact (physical_gate n C ao j).2 x

/-- A general sample table on either side of the monotone search. The augmented label is
    the physical signal of the named wire, so every cell and bound refer to this circuit. -/
theorem physical_packed {P Q : Type} [DecidableEq P] [DecidableEq Q] {n : ℕ}
    (C : Circuit) (ao : TopForm.IsAO2 n C) (prep : Finset (Fin C.size)) (z : Fin C.size)
    (cut : sharesOnly n C (n+z.val) (residual n C prep))
    (pos : P → Fin n → Bool) (neg : Q → Fin n → Bool) (s : Finset P) (t : Finset Q)
    (hp : ∀ p ∈ s, C.eval (List.ofFn (pos p)) = true)
    (hq : ∀ q ∈ t, C.eval (List.ofFn (neg q)) = false) :
    ∃ K col, Packed (fun p => extended C (n+z.val) (pos p))
      (fun q => extended C (n+z.val) (neg q)) s t K col ∧ K.card + prep.card ≤ C.size+1 := by
  obtain ⟨f,small,rep⟩ := physical_residual C ao prep z cut
  have p' (p) (h : p ∈ s) := (rep (pos p)).trans (hp p h)
  have q' (q) (h : q ∈ t) := (rep (neg q)).trans (hq q h)
  obtain ⟨K,col,h,bound⟩ := formula_packed f s t p' q'
  have leaves := f.leaves_eq_gates_add_one
  exact ⟨K,col,h,by omega⟩

/-- Under a size-21 budget the remaining raw-plus-one-signal rectangle budget is 22−t. -/
theorem g11 (C : Circuit) (ao : TopForm.IsAO2 11 C) (prep : Finset (Fin C.size)) (z : Fin C.size)
    (cut : sharesOnly 11 C (11+z.val) (residual 11 C prep)) (size : C.size ≤ 21)
    (hp : ∀ p, C.eval (List.ofFn (G11.positive p)) = true)
    (hq : ∀ q, C.eval (List.ofFn (G11.negative q)) = false) :
    ∃ K col, Packed (fun p => extended C (11+z.val) (G11.positive p))
      (fun q => extended C (11+z.val) (G11.negative q)) Finset.univ Finset.univ K col ∧
      K.card ≤ 22-prep.card := by
  obtain ⟨K,col,h,small⟩ := physical_packed C ao prep z cut _ _ Finset.univ Finset.univ
    (fun p _ => hp p) (fun q _ => hq q)
  exact ⟨K,col,h,by omega⟩

#print axioms tree_cost
#print axioms physical_residual
#print axioms physical_packed
#print axioms g11
end SingleSharedFormula
