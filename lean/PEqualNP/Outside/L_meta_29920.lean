import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29920_aux

open PEqualNP.CircuitLowerBounds

-- Backward support adapted from the L-meta-2375 Petersen partial bounds.
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, step, Nat.add_right_comm, Nat.add_assoc]

private lemma snoc_read (w : List Bool) (b : Bool) (p : ℕ) :
    (w ++ [b]).getD p false =
      if p = w.length then b else w.getD p false := by
  by_cases hp : p = w.length
  · subst p
    rw [List.getD_append_right _ _ _ _ le_rfl]
    simp
  · rw [ite_eq_right hp]
    by_cases hl : p < w.length
    · exact List.getD_append _ _ _ _ hl
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]

private lemma support (gs : List Gate) (n : ℕ) (pins : Finset ℕ)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ T : Finset ℕ, T.card ≤ pins.card + gs.length ∧
      ∀ a b : List Bool, a.length = n → b.length = n →
        (∀ i ∈ T, a.getD i false = b.getD i false) →
        ∀ i ∈ pins, (gs.foldl step a).getD i false = (gs.foldl step b).getD i false := by
  induction gs using List.reverseRecOn generalizing pins with
  | nil =>
    exact ⟨pins, by simp, fun _ _ _ _ h => h⟩
  | append_singleton gs g ih =>
    let p := n + gs.length
    let needed := if p ∈ pins then pins.erase p ∪ g.inputs.toFinset else pins
    obtain ⟨T, hT, hagree⟩ := ih needed (fun g' hg' => hfan g' (by simp [hg']))
    have hneed : needed.card ≤ pins.card + 1 := by
      by_cases hp : p ∈ pins
      · simp only [needed, ite_eq_left hp]
        have h₁ := Finset.card_union_le (pins.erase p) g.inputs.toFinset
        have h₂ := Finset.card_erase_add_one hp
        have h₃ := List.toFinset_card_le g.inputs
        have h₄ := hfan g (by simp)
        omega
      · simp [needed, hp]
    refine ⟨T, by simp; omega, ?_⟩
    intro a b ha hb hinput i hi
    have heval := hagree a b ha hb hinput
    have hla : (gs.foldl step a).length = p := by rw [fold_length, ha]
    have hlb : (gs.foldl step b).length = p := by rw [fold_length, hb]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, step, snoc_read, hla, hlb]
    by_cases h : i = p
    · subst i
      simp only [ite_true, eq_self]
      congr 1
      apply List.map_congr_left
      intro j hj
      exact heval j (by simp [needed, hi, hj])
    · rw [ite_eq_right h, ite_eq_right h]
      exact heval i (by by_cases hp : p ∈ pins <;> simp [needed, hp, hi, h])

private def row (v : Bool) (m : Fin 64) (i : Fin 7) : Bool :=
  if i.val = 0 then v else m.val.testBit (i.val - 1)

private def ring (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

private def w (m : Fin 64) := List.ofFn (row false m)
private def good (m : Fin 64) := ring (row true m)
private def label (m : Fin 64) := ring (row false m)
private def essentialRows (i : Fin 6) : Fin 64 × Fin 64 :=
  [(35,34),(3,1),(38,34),(25,17),(48,32),(49,17)].getD i.val (0,0)

-- The essential-input cut follows the separation argument in L-meta-14580.
set_option maxRecDepth 4096 in
private lemma essential_test : ∀ i : Fin 6,
    let x := (essentialRows i).1
    let y := (essentialRows i).2
    good x = true ∧ good y = true ∧ label x = true ∧ label y = false ∧
      ∀ p : Fin 7, p.val ≠ i.val + 1 → row false x p = row false y p := by
  decide +kernel

private def mergeRows (o : Bool) (i j : Fin 6) : Fin 64 × Fin 64 :=
  (if o then
    [(3,1),(12,9),(12,5),(24,9),(3,34),(3,5),(3,9),(3,17),(3,33),
      (13,5),(48,36),(6,34),(13,21),(12,36),(24,40)]
   else
    [(6,5),(12,9),(12,5),(24,9),(3,34),(3,1),(3,1),(3,1),(3,1),
      (25,17),(13,9),(6,34),(13,5),(12,36),(24,40)]).getD
    (i.val * (11 - i.val) / 2 + (j.val - i.val - 1)) (0,0)

private def comb (o a b : Bool) : Bool := if o then a || b else a && b

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private lemma merge_test : ∀ (o : Bool) (i j : Fin 6), i.val < j.val →
    let x := (mergeRows o i j).1
    let y := (mergeRows o i j).2
    good x = true ∧ good y = true ∧ label x = true ∧ label y = false ∧
    comb o (x.val.testBit i.val) (x.val.testBit j.val) =
      comb o (y.val.testBit i.val) (y.val.testBit j.val) ∧
    ∀ p : Fin 7, p.val ≠ i.val + 1 → p.val ≠ j.val + 1 →
      row false x p = row false y p := by
  decide +kernel

private lemma read_w (m : Fin 64) (p : ℕ) :
    (w m).getD p false = if h : p < 7 then row false m ⟨p,h⟩ else false := by
  by_cases h : p < 7
  · simp only [w, h, dite_true, List.getD_eq_getElem?_getD, List.getElem?_ofFn, Option.getD_some]
  · rw [List.getD_eq_default _ _ (by simpa [w] using Nat.le_of_not_lt h), dite_eq_right h]

private lemma miss (T : Finset ℕ) (h : T.card < 6) :
    ∃ i : Fin 6, i.val + 1 ∉ T := by
  by_contra! hc
  let e : Fin 6 ↪ ℕ := ⟨fun i => i.val + 1, fun a b h => Fin.ext (by change a.val + 1 = b.val + 1 at h; omega)⟩
  have hh : (Finset.univ.map e : Finset ℕ) ⊆ T := by
    intro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hz
    exact hc i
  have := Finset.card_le_card hh
  simp at this
  omega

private lemma agree_essential (i : Fin 6) (p : ℕ) (hp : p ≠ i.val + 1) :
    (w (essentialRows i).1).getD p false = (w (essentialRows i).2).getD p false := by
  simp only [read_w]
  split
  · exact (essential_test i).2.2.2.2 _ hp
  · rfl

private lemma agree_merge (o : Bool) (i j : Fin 6) (hij : i.val < j.val)
    (p : ℕ) (hi : p ≠ i.val + 1) (hj : p ≠ j.val + 1) :
    (w (mergeRows o i j).1).getD p false = (w (mergeRows o i j).2).getD p false := by
  simp only [read_w]
  split
  · exact (merge_test o i j hij).2.2.2.2.2 _ hi hj
  · rfl

private lemma two_inputs {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l)
    (hne : a ≠ b) (hl : l.length ≤ 2) : l = [a,b] ∨ l = [b,a] := by
  rcases l with _ | ⟨p, _ | ⟨q, _ | ⟨r,t⟩⟩⟩
  · simp at ha
  · simp_all
  · simp at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
  · simp at hl

private def separates (f : Fin 64 → Bool) := ∀ m, good m = true → f m = label m

private lemma first_obstruction (g : Gate) (T : Finset ℕ) (hc : T.card ≤ 5)
    (hlen : g.inputs.length ≤ 2)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (f : Fin 64 → Bool) (hf : separates f)
    (hs : ∀ x y, (∀ p ∈ T, (step (w x) g).getD p false =
      (step (w y) g).getD p false) → f x = f y) : False := by
  have one (i : Fin 6) (hi : i.val + 1 ∉ T)
      (hg : 7 ∈ T → g.op.eval (g.inputs.map fun p => (w (essentialRows i).1).getD p false) =
        g.op.eval (g.inputs.map fun p => (w (essentialRows i).2).getD p false)) : False := by
    obtain ⟨hx,hy,hpos,hneg,_⟩ := essential_test i
    have he := hs (essentialRows i).1 (essentialRows i).2 (by
      intro p hp
      simp only [step, snoc_read, w, List.length_ofFn]
      split
      · rename_i h
        subst p
        exact hg hp
      · exact agree_essential i p (by rintro rfl; contradiction))
    rw [hf _ hx, hf _ hy, hpos, hneg] at he
    contradiction
  by_cases hv : 7 ∈ T
  · obtain ⟨a,b,hab,ha,hb⟩ : ∃ a b : Fin 6, a.val < b.val ∧
        a.val + 1 ∉ T ∧ b.val + 1 ∉ T := by
      obtain ⟨i,hi⟩ := miss (T.erase 7) (by
        have := Finset.card_erase_add_one hv
        omega)
      have hi' : i.val + 1 ∉ T := by
        intro h
        exact hi (Finset.mem_erase.mpr ⟨by have := i.isLt; omega, h⟩)
      obtain ⟨j,hj⟩ := miss (insert (i.val + 1) (T.erase 7)) (by
        rw [Finset.card_insert_of_notMem hi]
        have := Finset.card_erase_add_one hv
        omega)
      have hj' : j.val + 1 ∉ T := by
        intro h
        exact hj (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨by have := j.isLt; omega,h⟩))
      have hne : j.val ≠ i.val := by
        intro he
        apply hj
        rw [he]
        exact Finset.mem_insert_self _ _
      by_cases h : i.val < j.val
      · exact ⟨i,j,h,hi',hj'⟩
      · exact ⟨j,i,by omega,hj',hi'⟩
    have absent (i : Fin 6) (hi : i.val + 1 ∉ T) (hm : i.val + 1 ∉ g.inputs) : False := by
      apply one i hi
      intro _
      congr 1
      apply List.map_congr_left
      intro p hp
      exact agree_essential i p (by rintro rfl; contradiction)
    by_cases hma : a.val + 1 ∈ g.inputs
    · by_cases hmb : b.val + 1 ∈ g.inputs
      · have lists := two_inputs hma hmb (by omega) hlen
        have merged (o : Bool) (ho : g.op = if o then .or else .and) : False := by
          obtain ⟨hx,hy,hpos,hneg,hcomb,_⟩ := merge_test o a b hab
          have ar (m : Fin 64) : (w m).getD (a.val+1) false = m.val.testBit a.val := by
            have h : a.val + 1 < 7 := by have := a.isLt; omega
            rw [read_w, dite_eq_left h]
            simp [row]
          have br (m : Fin 64) : (w m).getD (b.val+1) false = m.val.testBit b.val := by
            have h : b.val + 1 < 7 := by have := b.isLt; omega
            rw [read_w, dite_eq_left h]
            simp [row]
          have he := hs (mergeRows o a b).1 (mergeRows o a b).2 (by
            intro p hp
            simp only [step, snoc_read, w, List.length_ofFn]
            split
            · change g.op.eval (g.inputs.map fun p => (w (mergeRows o a b).1).getD p false) =
                  g.op.eval (g.inputs.map fun p => (w (mergeRows o a b).2).getD p false)
              rcases lists with hl | hl <;> cases o <;>
                simpa only [hl, ho, List.map_cons, List.map_nil, Bool.false_eq_true,
                  ite_false, ite_true, GateOp.eval, List.all_cons, List.all_nil,
                  List.any_cons, List.any_nil, id, Bool.true_and, Bool.false_or,
                  ar, br, comb, Bool.and_comm, Bool.or_comm] using hcomb
            · exact agree_merge o a b hab p (by rintro rfl; contradiction)
                (by rintro rfl; contradiction))
          rw [hf _ hx, hf _ hy, hpos, hneg] at he
          contradiction
        rcases hop with h | h | h
        · exact merged false h
        · exact merged true h
        · rcases lists with hl | hl
          · apply one b hb
            intro _
            simp only [h,hl,List.map_cons,List.map_nil,GateOp.eval,List.headD_cons]
            rw [agree_essential b _ (by omega)]
          · apply one a ha
            intro _
            simp only [h,hl,List.map_cons,List.map_nil,GateOp.eval,List.headD_cons]
            rw [agree_essential a _ (by omega)]
      · exact absent b hb hmb
    · exact absent a ha hma
  · obtain ⟨i,hi⟩ := miss T (by omega)
    exact one i hi (fun h => (hv h).elim)

private lemma prefix_obstruction (g : Gate) (gs : List Gate) (hl : gs.length = 4)
    (hlen : g.inputs.length ≤ 2)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hfan : ∀ a ∈ gs, a.inputs.length ≤ 2)
    (hf : separates fun m => (gs.foldl step (step (w m) g)).getD 11 false) : False := by
  obtain ⟨T,hT,hagree⟩ := support gs 8 {11} hfan
  apply first_obstruction g T (by simpa [hl] using hT) hlen hop _ hf
  intro x y he
  apply hagree _ _ _ _ he 11 (by simp)
  all_goals simp [step, w]

private lemma independence (gs : List Gate) (h : ∀ g ∈ gs, 0 ∉ g.inputs)
    (a b : List Bool) (ha : a.length = b.length)
    (he : ∀ p, p ≠ 0 → a.getD p false = b.getD p false) :
    ∀ p, p ≠ 0 → (gs.foldl step a).getD p false = (gs.foldl step b).getD p false := by
  induction gs generalizing a b with
  | nil => exact he
  | cons g gs ih =>
    apply ih (fun q hq => h q (by simp [hq]))
    · simp [step, ha]
    · intro p hp
      simp only [step, snoc_read, ha]
      split
      · congr 1
        apply List.map_congr_left
        intro j hj
        exact he j (by rintro rfl; exact h g (by simp) hj)
      · exact he p hp


private lemma row_read (v : Bool) (m : Fin 64) (p : ℕ) :
    (List.ofFn (row v m)).getD p false =
      if h : p < 7 then row v m ⟨p,h⟩ else false := by
  by_cases h : p < 7
  · simp only [h, dite_true, List.getD_eq_getElem?_getD, List.getElem?_ofFn, Option.getD_some]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt h), dite_eq_right h]

private lemma stable_prefix (gs : List Gate) (a : List Bool) (p : ℕ)
    (h : p < a.length) : (gs.foldl step a).getD p false = a.getD p false := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl step (step a g)).getD p false = _
    rw [ih _ (by simp [step]; omega)]
    rw [step, snoc_read, ite_eq_right (by omega)]

end PEqualNP.Outside.L_meta_29920_aux

open PEqualNP.Outside.L_meta_29920_aux
open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_29920 : ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 11 ∈ (C.gates.get i).inputs ∧ 11 ≠ 0 ∧ 11 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 11 false = true) := by
  classical
  intro ⟨⟨gs,out⟩,i,k,hi,hfan,hlen,hev,h0,honly,hor,hand,hik,h15,h11,_,_,_⟩
  change gs.length = 10 at hlen
  have hk : k.val = 9 := by
    have hkl : k.val < gs.length := k.isLt
    omega
  let g8 := gs.get i
  let g9 := gs.get k
  let pre := gs.take 8
  have hpre : pre.length = 8 := by simp [pre, hlen]
  have hsplit : gs = pre ++ [g8,g9] := by
    apply List.ext_getElem
    · simp [hlen,hpre]
    · intro p hp hq
      by_cases h : p < 8
      · rw [List.getElem_append_left (by omega)]
        simp [pre]
      · have h' : p = 8 ∨ p = 9 := by omega
        rcases h' with rfl | rfl
        · rw [List.getElem_append_right (show pre.length ≤ 8 by omega)]
          simp only [hpre, Nat.sub_self, List.getElem_cons_zero, g8, List.get_eq_getElem]
          congr 1
          exact hi.symm
        · rw [List.getElem_append_right (show pre.length ≤ 9 by omega)]
          simp only [hpre, show 9 - 8 = 1 by decide, List.getElem_cons_succ,
            List.getElem_cons_zero, g9, List.get_eq_getElem]
          congr 1
          exact hk.symm
  have nzero : ∀ g ∈ pre, 0 ∉ g.inputs := by
    intro g hg h
    obtain ⟨p,hp,rfl⟩ := List.mem_iff_getElem.mp hg
    have hlt : p < gs.length := by omega
    have he : pre[p] = gs[p] := by simp [pre]
    rw [he] at h
    have hn := honly ⟨p,hlt⟩ h
    have eh : p = i.val := congrArg Fin.val hn
    omega
  have hg8 : g8.inputs = [0,11] ∨ g8.inputs = [11,0] :=
    two_inputs h0 h11 (by decide) (hfan _ (List.get_mem _ _)).2
  have h9zero : 0 ∉ g9.inputs := by
    intro h
    have := congrArg Fin.val (honly k h)
    omega
  let U (v : Bool) (m : Fin 64) := pre.foldl step (List.ofFn (row v m))
  have lu (v : Bool) (m : Fin 64) : (U v m).length = 15 := by
    simp [U, fold_length, hpre]
  have same (m : Fin 64) (p : ℕ) (hp : p ≠ 0) :
      (U true m).getD p false = (U false m).getD p false := by
    apply independence pre nzero _ _ (by simp) _ p hp
    intro q hq
    simp only [row_read]
    split <;> simp [row,hq]
  have zero (v : Bool) (m : Fin 64) : (U v m).getD 0 false = v := by
    rw [stable_prefix _ _ _ (by simp)]
    rw [row_read, dite_eq_left (by decide)]
    rfl
  let V (v : Bool) (m : Fin 64) := step (U v m) g8
  have readV (v : Bool) (m : Fin 64) (p : ℕ) :
      (V v m).getD p false =
        if p = 15 then v || (U false m).getD 11 false else (U v m).getD p false := by
    simp only [V, step, snoc_read, lu]
    split
    · have eq11 : (U v m).getD 11 false = (U false m).getD 11 false := by
        cases v
        · rfl
        · exact same m 11 (by decide)
      change g8.op = .or at hor
      rw [hor]
      rcases hg8 with h | h <;>
        simp only [h, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
          List.any_nil, id, Bool.false_or, Bool.or_false, zero, eq11, Bool.or_comm]
    · rfl
  have target (v : Bool) (m : Fin 64) :
      (step (V v m) g9).getD out false = ring (row v m) := by
    have hh := hev (row v m)
    change (gs.foldl step (List.ofFn (row v m))).getD out false = ring (row v m) at hh
    rwa [hsplit, List.foldl_append] at hh
  have hout : out = 16 := by
    by_contra hn
    have lv (v : Bool) (m : Fin 64) : (V v m).length = 16 := by
      simp only [V, step, List.length_append, List.length_singleton, lu]
    have hv (v : Bool) (m : Fin 64) : (V v m).getD out false = ring (row v m) := by
      have ht := target v m
      rw [step, snoc_read, lv, ite_eq_right hn] at ht
      exact ht
    have hbad : (V true 0).getD out false = false := (hv true 0).trans (by decide)
    have h15' : out ≠ 15 := by
      intro he
      rw [he, readV] at hbad
      simp at hbad
    have h0' : out ≠ 0 := by
      intro he
      rw [he, readV] at hbad
      simp only [show ¬ (0 : ℕ) = 15 by decide, ite_false, zero] at hbad
      contradiction
    have he : (V true 1).getD out false = (V false 1).getD out false := by
      rw [readV, readV, ite_eq_right h15', ite_eq_right h15', same 1 out h0']
    exact (by decide : ring (row true 1) ≠ ring (row false 1))
      ((hv true 1).symm.trans (he.trans (hv false 1)))
  have final (v : Bool) (m : Fin 64) :
      g9.op.eval (g9.inputs.map fun p => (V v m).getD p false) = ring (row v m) := by
    have ht := target v m
    have lv : (V v m).length = 16 := by
      simp only [V, step, List.length_append, List.length_singleton, lu]
    rwa [step, snoc_read, lv, hout, ite_eq_left rfl] at ht
  have sep : separates (fun m => (U false m).getD 11 false) := by
    intro m hm
    have ht := final true m
    have hf := final false m
    change g9.op = .and at hand
    rw [hand, GateOp.eval] at ht hf
    rw [List.all_map] at ht hf
    change (g9.inputs.all fun p => (V true m).getD p false) = good m at ht
    change (g9.inputs.all fun p => (V false m).getD p false) = label m at hf
    have ht' := List.all_eq_true.mp (ht.trans hm)
    have hread : 15 ∈ g9.inputs := by
      change 7 + i.val ∈ g9.inputs at h15
      rw [hi] at h15
      exact h15
    change (U false m).getD 11 false = label m
    rw [← hf]
    cases hb : (U false m).getD 11 false
    · symm
      apply Bool.eq_false_iff.mpr
      intro hall
      have hfalse := List.all_eq_true.mp hall 15 hread
      rw [readV, ite_eq_left rfl, hb] at hfalse
      contradiction
    · symm
      apply List.all_eq_true.mpr
      intro p hp
      by_cases he : p = 15
      · rw [he, readV, ite_eq_left rfl, hb]; rfl
      · have hn : p ≠ 0 := by rintro rfl; exact h9zero hp
        have ht'' := ht' p hp
        rw [readV, ite_eq_right he, same m p hn] at ht''
        rwa [readV, ite_eq_right he]
  cases hp : pre with
  | nil => simp [hp] at hpre
  | cons g rest =>
    let sub := rest.take 4
    have hsub : sub.length = 4 := by simp [sub]; simp [hp] at hpre; omega
    have hs : pre = (g :: sub) ++ rest.drop 4 := by simp [hp,sub]
    have hg : g ∈ gs := by rw [hsplit,hp]; simp
    obtain ⟨hop,hl⟩ := hfan g hg
    apply prefix_obstruction g sub hsub hl (by simpa using hop)
    · intro q hq
      apply (hfan q _).2
      rw [hsplit,hs]
      simp [hq]
    · intro m hm
      have h := sep m hm
      change (pre.foldl step (w m)).getD 11 false = _ at h
      rw [hs,List.foldl_append,List.foldl_cons,stable_prefix] at h
      · exact h
      · simp [fold_length, step, hsub, w]
