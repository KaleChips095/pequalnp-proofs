import PEqualNP.MetaComplexity.Helpers.Elim
import PEqualNP.Defs.TopForm

namespace Bridge3491
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def Good (n : ℕ) (gs : List Gate) := IsAO2 n ⟨gs,0⟩
def AO (g : Gate) := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

theorem snocGood {n : ℕ} {L : List Gate} {g : Gate} (h : Good n L) (a : AO g)
    (b : ∀ j ∈ g.inputs, j < n + L.length) : Good n (L ++ [g]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · exact h.1 _ hu
    · simpa using (List.mem_singleton.1 hu ▸ a.1 : u.op = .and ∨ u.op = .or)
  · intro j hj i hi
    change j < (L ++ [g]).length at hj
    change i ∈ ((L ++ [g]).getD j _).inputs at hi
    by_cases hj' : j < L.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact h.2.1 j hj' i hi
    · have : j = L.length := by simp at hj; omega
      subst j
      simp at hi
      exact b i hi
  · intro u hu
    rcases List.mem_append.1 hu with hu | hu
    · exact h.2.2 _ hu
    · simpa [List.mem_singleton.1 hu] using a.2

theorem stepGood {n : ℕ} {acc : List Stat × List Gate} {g : Gate} (h : Good n acc.2)
    (ha : AO g) (hv : ∀ i, (acc.1.getD i (.const false)).Valid (n+acc.2.length)) :
    Good n (elimStep n acc g).2 := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := ha
  change ins.length = 2 at hl
  obtain ⟨a,b,rfl⟩ : ∃ a b, ins = [a,b] := by
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> simp_all
  have va := hv a
  have vb := hv b
  change op = _ ∨ op = _ at hop
  rcases hop with rfl | rfl <;>
    cases ea : acc.1.getD a (.const false) <;> cases eb : acc.1.getD b (.const false) <;>
    simp only [elimStep, simplify, List.map_cons, List.map_nil, ea, eb, simpAnd, simpOr, Option.toList_none, Option.toList_some, List.append_nil] <;>
    first | exact h | (apply snocGood h (by simp [AO]); simp only [ea, Stat.Valid] at va; simp only [eb, Stat.Valid] at vb; simpa using And.intro va vb)

theorem elimGood (n : ℕ) (gs : List Gate) (ha : ∀ g ∈ gs, AO g)
    (y w : List Bool) (hy : y.length = n) (acc : List Stat × List Gate)
    (h : Good n acc.2) (hinv : Inv n y w acc) : Good n (elim n gs acc).2 := by
  induction gs generalizing w acc with
  | nil => exact h
  | cons g gs ih =>
    have ag := ha g List.mem_cons_self
    have ok : Ok g := ⟨ag.1.imp_right Or.inl, by have := ag.2; omega⟩
    apply ih (fun u hu => ha u (List.mem_cons_of_mem _ hu))
      (wiresFrom [g] w) (elimStep n acc g)
      (stepGood h ag (fun i => (hinv.2 i).1))
    exact inv_elim n y hy [g] w acc (by simpa using ok) hinv


theorem elim_prefix (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    ∃ rest, (elim n gs acc).2 = acc.2 ++ rest := by
  induction gs generalizing acc with
  | nil => exact ⟨[], by simp [elim]⟩
  | cons g gs ih =>
    obtain ⟨r,hr⟩ := ih (elimStep n acc g)
    exact ⟨_ ++ r, hr.trans (List.append_assoc ..)⟩

def plug {n m : ℕ} (σ : Fin m → Bool ⊕ Fin n) (x : Fin n → Bool) (i : Fin m) : Bool :=
  (σ i).elim id x

def status {n : ℕ} : Bool ⊕ Fin n → Stat
  | .inl b => .const b
  | .inr i => .wire i

theorem initialInv {n m : ℕ} (σ : Fin m → Bool ⊕ Fin n) (x : Fin n → Bool) (L : List Gate) :
    Inv n (List.ofFn x) (List.ofFn (plug σ x)) (List.ofFn (status ∘ σ), L) := by
  refine ⟨by simp, ?_⟩
  intro i
  by_cases hi : i < m
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte,
      Option.getD_some, Function.comp_apply]
    cases hs : σ ⟨i,hi⟩ with
    | inl b => simp [status, Stat.Valid, Stat.val, plug, hs]
    | inr j =>
      simp only [status, Stat.Valid, Stat.val, plug, hs, Sum.elim_inr]
      exact ⟨by omega, by rw [getD_wiresFrom _ _ _ (by simp)]; simp⟩
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    exact ⟨trivial,rfl⟩

/-- Append a specialized copy behind an arbitrary existing circuit. -/
theorem appendPlug {n m : ℕ} (σ : Fin m → Bool ⊕ Fin n) (C : Circuit) (hc : IsAO2 m C)
    (L : List Gate) (hL : Good n L)
    (hnc : ∃ x y, circuitFun m C (plug σ x) ≠ circuitFun m C (plug σ y)) :
    ∃ (rest : List Gate) (j : ℕ), Good n (L ++ rest) ∧ rest.length ≤ C.size ∧
      j < n + (L ++ rest).length ∧
      ∀ x, circuitFun n ⟨L ++ rest,j⟩ x = circuitFun m C (plug σ x) := by
  let a := (List.ofFn (status ∘ σ), L)
  let e := elim n C.gates a
  have hao : ∀ g ∈ C.gates, AO g := fun g h => ⟨hc.1 g h, hc.2.2 g h⟩
  have hok : ∀ g ∈ C.gates, Ok g := fun g h =>
    ⟨(hao g h).1.imp_right Or.inl, Nat.le_of_eq (hao g h).2⟩
  have inv (x : Fin n → Bool) :=
    inv_elim n (List.ofFn x) (by simp) C.gates _ a hok (initialInv σ x L)
  have ev (x : Fin n → Bool) :
      (e.1.getD C.output (.const false)).val (wiresFrom e.2 (List.ofFn x)) =
        circuitFun m C (plug σ x) := ((inv x).2 C.output).2
  obtain ⟨x,y,hxy⟩ := hnc
  have hv : (e.1.getD C.output (.const false)).Valid (n+e.2.length) := ((inv x).2 C.output).1
  cases hs : e.1.getD C.output (.const false) with
  | const b => exact False.elim (hxy (by rw [← ev x, ← ev y, hs]; rfl))
  | wire j =>
    obtain ⟨r,hr⟩ := elim_prefix n C.gates a
    change e.2 = L ++ r at hr
    have hl := elim_len n C.gates a
    change e.2.length ≤ L.length + C.gates.length at hl
    rw [hr,List.length_append] at hl
    refine ⟨r,j,?_,by change r.length ≤ C.gates.length; omega,?_,?_⟩
    · rw [← hr]
      exact elimGood n C.gates hao _ _ (by simp) a hL (initialInv σ x L)
    · rw [hs] at hv
      exact hr ▸ hv
    · intro z
      have hz := ev z
      rw [hs] at hz
      exact hr ▸ hz

theorem restrictAO {n m : ℕ} (σ : Fin m → Bool ⊕ Fin n) (C : Circuit) (hc : IsAO2 m C)
    (hnc : ∃ x y, circuitFun m C (plug σ x) ≠ circuitFun m C (plug σ y)) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ ∀ x, circuitFun n D x = circuitFun m C (plug σ x) := by
  obtain ⟨r,j,h,hl,_,e⟩ := appendPlug σ C hc [] (by
    simp [Good,IsAO2,AndOrOnly,ReadsBack]) hnc
  exact ⟨⟨r,j⟩,by change Good n r; simpa using h,hl,by simpa using e⟩


/-- Joining arbitrary circuits is allowed even when a designated output is out of range. -/
theorem orTwo {n : ℕ} (A B : Circuit) (ha : IsAO2 n A) (hb : IsAO2 n B) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ A.size + B.size + 1 ∧
      ∀ x, circuitFun n D x = (circuitFun n A x || circuitFun n B x) := by
  classical
  let z : Fin n → Bool := fun _ => false
  by_cases hca : ∃ x y, circuitFun n A x ≠ circuitFun n A y
  · by_cases hcb : ∃ x y, circuitFun n B x ≠ circuitFun n B y
    · have hao : A.output < n + A.gates.length := by
        by_contra! hn
        obtain ⟨x,y,h⟩ := hca
        apply h
        change (wiresFrom _ _).getD _ false = (wiresFrom _ _).getD _ false
        rw [List.getD_eq_default _ _ (by simpa [length_wiresFrom] using hn),
            List.getD_eq_default _ _ (by simpa [length_wiresFrom] using hn)]
      obtain ⟨r,j,hr,hlen,hj,ev⟩ := appendPlug (n:=n) Sum.inr B hb A.gates ha hcb
      let L := A.gates ++ r
      let g : Gate := ⟨.or,[A.output,j]⟩
      refine ⟨⟨L ++ [g],n+L.length⟩,?_,?_,?_⟩
      · change Good n (L ++ [g])
        apply snocGood hr (by simp [AO,g])
        have hao' : A.output < n + L.length := by simp [L]; omega
        simpa [g,L] using And.intro hao' hj
      · change (L ++ [g]).length ≤ A.gates.length + B.gates.length + 1
        change r.length ≤ B.gates.length at hlen
        simp [L]; omega
      · intro x
        let w := wiresFrom L (List.ofFn x)
        have hw : w.length = n+L.length := by simp [w,length_wiresFrom]
        have eA : w.getD A.output false = circuitFun n A x := by
          dsimp [w,L]
          rw [wiresFrom_append,getD_wiresFrom _ _ _ (by simpa [length_wiresFrom] using hao)]
          rfl
        have eB : w.getD j false = circuitFun n B x := ev x
        change (wiresFrom (L ++ [g]) _).getD (n+L.length) false = _
        rw [wiresFrom_append]
        change (w ++ [GateOp.or.eval ([A.output,j].map fun i => w.getD i false)]).getD _ _ = _
        rw [getD_snoc_len _ _ _ _ hw]
        simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil, Bool.or_false]
        rw [eA,eB]; rfl
    · push Not at hcb
      cases hv : circuitFun n B z with
      | false => exact ⟨A,ha,by omega,fun x => by simp [hcb x z,hv]⟩
      | true => exact ⟨B,hb,by omega,fun x => by simp [hcb x z,hv]⟩
  · push Not at hca
    cases hv : circuitFun n A z with
    | false => exact ⟨B,hb,by omega,fun x => by simp [hca x z,hv]⟩
    | true => exact ⟨A,ha,by omega,fun x => by simp [hca x z,hv]⟩

theorem orThree {n : ℕ} (A B C : Circuit) (ha : IsAO2 n A) (hb : IsAO2 n B)
    (hc : IsAO2 n C) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ A.size + B.size + C.size + 2 ∧
      ∀ x, circuitFun n D x = (circuitFun n A x || circuitFun n B x || circuitFun n C x) := by
  obtain ⟨AB,hab,sab,eab⟩ := orTwo A B ha hb
  obtain ⟨D,hd,sd,ed⟩ := orTwo AB C hab hc
  exact ⟨D,hd,by omega,fun x => by rw [ed,eab]⟩

/-- A false restricted input suffices, including an identically false restriction. -/
theorem restrictOfFalse {n m : ℕ} (σ : Fin m → Bool ⊕ Fin n) (C : Circuit) (hc : IsAO2 m C)
    (hzero : ∃ x, circuitFun m C (plug σ x) = false) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ ∀ x, circuitFun n D x = circuitFun m C (plug σ x) := by
  classical
  by_cases hnc : ∃ x y, circuitFun m C (plug σ x) ≠ circuitFun m C (plug σ y)
  · exact restrictAO σ C hc hnc
  · push Not at hnc
    obtain ⟨z,hz⟩ := hzero
    refine ⟨⟨[],n⟩,by simp [IsAO2,AndOrOnly,ReadsBack],Nat.zero_le _,?_⟩
    intro x
    rw [hnc x z, hz]
    change (List.ofFn x).getD n false = false
    exact List.getD_eq_default _ _ (by simp)

theorem threeSpecializations {n m : ℕ} (C : Circuit) (hc : IsAO2 m C)
    (σ : Fin 3 → Fin m → Bool ⊕ Fin n)
    (hfalse : ∀ i, ∃ x, circuitFun m C (plug (σ i) x) = false) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ 3*C.size+2 ∧
      ∀ x, circuitFun n D x =
        (circuitFun m C (plug (σ 0) x) || circuitFun m C (plug (σ 1) x) ||
          circuitFun m C (plug (σ 2) x)) := by
  obtain ⟨A,ha,sa,ea⟩ := restrictOfFalse (σ 0) C hc (hfalse 0)
  obtain ⟨B,hb,sb,eb⟩ := restrictOfFalse (σ 1) C hc (hfalse 1)
  obtain ⟨T,ht,st,et⟩ := restrictOfFalse (σ 2) C hc (hfalse 2)
  obtain ⟨D,hd,sd,ed⟩ := orThree A B T ha hb ht
  exact ⟨D,hd,by omega,fun x => by rw [ed,ea,eb,et]⟩

#print axioms restrictAO
#print axioms orThree
#print axioms threeSpecializations
end Bridge3491
