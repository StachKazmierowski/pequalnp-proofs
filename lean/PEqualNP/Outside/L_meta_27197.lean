import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_27197_aux
-- Two-probe interface and restriction compiler adapted from L-meta-27764,
-- which credits the interface from L-meta-27253.
open PEqualNP.CircuitLowerBounds
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def permanent (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def fixed : List Gate := [⟨.and,[0,4]⟩,⟨.and,[1,5]⟩]
def shape (g : Gate) : Prop :=
  (g.op = .not ∧ ∃ a, g.inputs = [a]) ∨
  ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, a < b ∧ g.inputs = [a,b])

def assign (m : ℕ) (i : Fin 9) : Bool := m.testBit i.val

def value (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

lemma input_read (x : Fin 9 → Bool) {i : ℕ} (hi : i < 9) :
    (List.ofFn x).getD i false = x ⟨i,hi⟩ := by
  have h : i < (List.ofFn x).length := by simpa only [List.length_ofFn] using hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  simp only [Option.getD_some, List.getElem_ofFn]

lemma fixed_eval (x : Fin 9 → Bool) :
    fixed.foldl step (List.ofFn x) =
      List.ofFn x ++ [x 0 && x 4] ++ [x 1 && x 5] := by
  simp [fixed, step, GateOp.eval]

section Row

def pin (i : ℕ) : Bool := decide (i = 3 ∨ i = 4 ∨ i = 5)

def touches (g : Gate) : Bool := g.inputs.any (pin )

def probe (s : Fin 10) (x : Fin 9 → Bool) : Bool :=
  let a := x (Fin.ofNat 9 3)
  let b := x (Fin.ofNat 9 4)
  let c := x (Fin.ofNat 9 5)
  ([false, a, b, c, a && b, a || b,
    a && c, a || c, b && c, b || c] : List Bool).getD s.val false

def collision (s t : Fin 10) : ℕ × ℕ :=
  ([(84, 68), (84, 68), (140, 132), (84, 68), (84, 68), (84, 76), (84, 68), (84, 68), (84, 68), (84, 100), (84, 68), (84, 68), (161, 129), (84, 68), (84, 68), (92, 76), (84, 68), (84, 68), (84, 68), (84, 100), (140, 132), (161, 129), (140, 132), (140, 132), (140, 132), (156, 148), (140, 132), (140, 164), (140, 132), (140, 132), (84, 68), (84, 68), (140, 132), (84, 68), (84, 68), (84, 76), (84, 68), (84, 68), (84, 68), (116, 100), (84, 68), (84, 68), (140, 132), (84, 68), (84, 68), (84, 76), (84, 68), (84, 68), (84, 68), (84, 100), (84, 76), (92, 76), (156, 148), (84, 76), (84, 76), (84, 76), (84, 76), (92, 76), (84, 76), (84, 108), (84, 68), (84, 68), (140, 132), (84, 68), (84, 68), (84, 76), (84, 68), (84, 68), (84, 68), (84, 100), (84, 68), (84, 68), (140, 164), (84, 68), (84, 68), (92, 76), (84, 68), (84, 68), (84, 68), (92, 100), (84, 68), (84, 68), (140, 132), (84, 68), (84, 68), (84, 76), (84, 68), (84, 68), (84, 68), (84, 100), (84, 100), (84, 100), (140, 132), (116, 100), (84, 100), (84, 108), (84, 100), (92, 100), (84, 100), (84, 100)] : List (ℕ × ℕ)).getD
    (10 * s.val + t.val) (0, 0)

lemma probes_collide : ∀ s t : Fin 10,
    let x := assign (collision s t).1
    let y := assign (collision s t).2
    (∀ i : Fin 9, (pin ) i.val = false → x i = y i) ∧
    (x 0 && x 4) = (y 0 && y 4) ∧ (x 1 && x 5) = (y 1 && y 5) ∧
    probe s x = probe s y ∧ probe t x = probe t y ∧ permanent x ≠ permanent y := by
  decide +kernel

def reads (x y : Fin 9 → Bool) (w v : List Bool) : Prop :=
  ∀ i : ℕ, if (pin ) i then w.getD i false = x (Fin.ofNat 9 i) ∧
    v.getD i false = y (Fin.ofNat 9 i) else w.getD i false = v.getD i false

lemma relevant_pin {i : ℕ} (h : (pin ) i = true) : i = 3 ∨ i = 4 ∨ i = 5 := by
  simpa [pin] using h

lemma keep_pin {i : ℕ} (h : (pin ) i = true) : i < 9 := by
  rcases relevant_pin h with rfl | rfl | rfl <;> omega

lemma read_pin {x y w v} (h : (reads ) x y w v) {i} (hi : (pin ) i = true) :
    w.getD i false = x (Fin.ofNat 9 i) ∧ v.getD i false = y (Fin.ofNat 9 i) := by
  simpa [hi] using h i

lemma read_other {x y w v} (h : (reads ) x y w v) {i} (hi : (pin ) i = false) :
    w.getD i false = v.getD i false := by simpa [hi] using h i

lemma probe_single {i : ℕ} (hi : (pin ) i = true) :
    ∃ s : Fin 10, ∀ x, probe s x = x (Fin.ofNat 9 i) := by
  rcases relevant_pin hi with rfl | rfl | rfl
  · exact ⟨1, fun _ => rfl⟩
  · exact ⟨2, fun _ => rfl⟩
  · exact ⟨3, fun _ => rfl⟩

lemma probe_pair {a b : ℕ} (ha : (pin ) a = true) (hb : (pin ) b = true) (hab : a < b)
    (o : Bool) : ∃ s : Fin 10, ∀ x, probe s x =
      (if o then x (Fin.ofNat 9 a) || x (Fin.ofNat 9 b)
        else x (Fin.ofNat 9 a) && x (Fin.ofNat 9 b)) := by
  rcases relevant_pin ha with rfl | rfl | rfl <;>
    rcases relevant_pin hb with rfl | rfl | rfl <;> try omega
  · cases o
    · exact ⟨4, fun _ => rfl⟩
    · exact ⟨5, fun _ => rfl⟩
  · cases o
    · exact ⟨6, fun _ => rfl⟩
    · exact ⟨7, fun _ => rfl⟩
  · cases o
    · exact ⟨8, fun _ => rfl⟩
    · exact ⟨9, fun _ => rfl⟩

def good (s : Fin 10) (g : Gate) : Prop :=
  ∀ {x y w v}, (reads ) x y w v → probe s x = probe s y → value w g = value v g

lemma has_probe (g : Gate) (hg : shape g) : ∃ s, good s g := by
  obtain ⟨op,is⟩ := g
  rcases hg with ⟨ho,a,hi⟩ | ⟨ho,a,b,hab,hi⟩
  · change op = .not at ho
    change is = [a] at hi
    subst op
    subst is
    cases ha : (pin ) a
    · exact ⟨0, fun h _ => by simp only [value, List.map_cons, List.map_nil, read_other h ha]⟩
    · obtain ⟨s, hs⟩ := probe_single ha
      refine ⟨s, ?_⟩
      intro x y w v h e
      rw [hs, hs] at e
      obtain ⟨hw,hv⟩ := read_pin h ha
      simp only [value, List.map_cons, List.map_nil, hw, hv, e]
  · change is = [a,b] at hi
    subst is
    change op = .and ∨ op = .or at ho
    rcases ho with rfl | rfl <;> cases ha : (pin ) a <;> cases hb : (pin ) b
    all_goals first
      | have ha0 : (pin ) a = false := ha
        have hb0 : (pin ) b = false := hb
        exact ⟨0, fun h _ => by simp only [value, List.map_cons, List.map_nil, read_other h ha0, read_other h hb0]⟩
      | have hb0 : (pin ) b = false := hb
        obtain ⟨s, hs⟩ := probe_single ha
        refine ⟨s, ?_⟩
        intro x y w v h e
        rw [hs, hs] at e
        obtain ⟨hw,hv⟩ := read_pin h ha
        simp only [value, List.map_cons, List.map_nil, hw, hv, e, read_other h hb0]
      | have ha0 : (pin ) a = false := ha
        obtain ⟨s, hs⟩ := probe_single hb
        refine ⟨s, ?_⟩
        intro x y w v h e
        rw [hs, hs] at e
        obtain ⟨hw,hv⟩ := read_pin h hb
        simp only [value, List.map_cons, List.map_nil, hw, hv, e, read_other h ha0]
      | skip
    · obtain ⟨s, hs⟩ := probe_pair ha hb hab false
      refine ⟨s, ?_⟩
      intro x y w v h e
      rw [hs, hs] at e
      obtain ⟨hw,hv⟩ := read_pin h ha
      obtain ⟨hw',hv'⟩ := read_pin h hb
      simpa only [value, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.and_true, Bool.or_false, Bool.false_eq_true, ite_true, ite_false, id_eq, hw, hv, hw', hv'] using e
    · obtain ⟨s, hs⟩ := probe_pair ha hb hab true
      refine ⟨s, ?_⟩
      intro x y w v h e
      rw [hs, hs] at e
      obtain ⟨hw,hv⟩ := read_pin h ha
      obtain ⟨hw',hv'⟩ := read_pin h hb
      simpa only [value, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.and_true, Bool.or_false, Bool.false_eq_true, ite_true, ite_false, id_eq, hw, hv, hw', hv'] using e

lemma reads_push {x y w v} (h : (reads ) x y w v) (hl : w.length = v.length)
    (hn : 9 ≤ w.length) (b : Bool) : (reads ) x y (w ++ [b]) (v ++ [b]) := by
  intro i
  by_cases hi : i < w.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega)]
    exact h i
  · have ho : (pin ) i = false := by
      cases hp : (pin ) i
      · rfl
      · have := keep_pin hp
        omega
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hl]
    simp [ho]

lemma eval_agree {x y : Fin 9 → Bool} (gs : List Gate) (w v : List Bool)
    (h : (reads ) x y w v) (hl : w.length = v.length) (hn : 9 ≤ w.length)
    (hp' : ∀ g ∈ gs.filter (touches ), ∀ {w' v'}, (reads ) x y w' v' → value w' g = value v' g)
    {o : ℕ} (ho : (pin ) o = false) :
    (gs.foldl step w).getD o false = (gs.foldl step v).getD o false := by
  induction gs generalizing w v with
  | nil => exact read_other h ho
  | cons g gs ih =>
    have e : value w g = value v g := by
      cases ht : (touches ) g
      · unfold value
        congr 1
        apply List.map_congr_left
        intro i hi
        have hh : (pin ) i = false := by
          cases he : (pin ) i
          · rfl
          · have : (touches ) g = true := List.any_eq_true.mpr ⟨i,hi,he⟩
            simp [ht] at this
        exact read_other h hh
      · exact hp' g (by simp [ht]) h
    have ht (g' : Gate) (hg' : g' ∈ gs.filter (touches )) : g' ∈ (g :: gs).filter (touches ) := by
      simp only [List.mem_filter] at *
      exact ⟨List.mem_cons_of_mem _ hg'.1, hg'.2⟩
    rw [List.foldl_cons, List.foldl_cons]
    change (gs.foldl step (w ++ [value w g])).getD o false =
      (gs.foldl step (v ++ [value v g])).getD o false
    rw [e]
    apply ih _ _ (reads_push h hl hn _) (by simp [hl]) (by simp; omega)
    · exact fun g' hg' => hp' g' (ht g' hg')

lemma input_reads {x y : Fin 9 → Bool}
    (h : ∀ i : Fin 9, (pin ) i.val = false → x i = y i) :
    (reads ) x y (List.ofFn x) (List.ofFn y) := by
  intro i
  cases hp : (pin ) i
  · simp only [hp, Bool.false_eq_true, ite_false]
    by_cases hi : i < 9
    · simpa only [input_read _ hi] using h ⟨i,hi⟩ hp
    · simp [List.getD_eq_default, List.length_ofFn, Nat.le_of_not_gt hi]
  · simp only [hp, ite_true]
    have hi := keep_pin hp
    have e : (⟨i,hi⟩ : Fin 9) = Fin.ofNat 9 i := by
      apply Fin.ext
      exact (Nat.mod_eq_of_lt hi).symm
    rw [input_read _ hi, input_read _ hi, e]
    exact ⟨rfl,rfl⟩

lemma three_touches (gs : List Gate) (o : ℕ) (ho : (pin ) o = false)
    (hs : ∀ g ∈ gs, shape g)
    (he : ∀ x, ((fixed ++ gs).foldl step (List.ofFn x)).getD o false = permanent x) :
    3 ≤ (gs.filter (touches )).length := by
  by_contra! short
  generalize eq : gs.filter (touches ) = ts at short
  have incl : ∀ g ∈ ts, shape g := by
    intro g hg
    exact hs g (List.mem_filter.mp (eq ▸ hg)).1
  have two : ∃ s t : Fin 10, ∀ g ∈ ts, good s g ∨ good t g := by
    rcases ts with _ | ⟨a, _ | ⟨b, _ | ⟨c,cs⟩⟩⟩
    · exact ⟨0, 0, by simp⟩
    · obtain ⟨s,hs⟩ := has_probe a (incl a (by simp))
      exact ⟨s, s, by simp [hs]⟩
    · obtain ⟨s,hs⟩ := has_probe a (incl a (by simp))
      obtain ⟨t,ht⟩ := has_probe b (incl b (by simp))
      refine ⟨s,t,?_⟩
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact .inl hs
      · exact .inr ht
    · simp only [List.length_cons] at short; omega
  obtain ⟨s,t,hcover⟩ := two
  let x := assign (collision s t).1
  let y := assign (collision s t).2
  obtain ⟨hxy,h1,h2,hs',ht',hne⟩ := probes_collide s t
  change ∀ i : Fin 9, (pin ) i.val = false → x i = y i at hxy
  change (x 0 && x 4) = (y 0 && y 4) at h1
  change (x 1 && x 5) = (y 1 && y 5) at h2
  have hr := input_reads hxy
  have hr1 := reads_push hr (by simp) (by simp) (x 0 && x 4)
  have hr2 := reads_push hr1 (by simp) (by simp) (x 1 && x 5)
  have hr3 : (reads ) x y (fixed.foldl step (List.ofFn x)) (fixed.foldl step (List.ofFn y)) := by
    rw [fixed_eval, fixed_eval, ← h2, ← h1]
    exact hr2
  have out := eval_agree gs _ _ hr3
    (by rw [fixed_eval, fixed_eval]; simp) (by rw [fixed_eval]; simp) (by
      intro g hg w v r
      rcases hcover g (eq ▸ hg) with h | h
      · exact h r hs'
      · exact h r ht') ho
  apply hne
  rw [← he x, ← he y, List.foldl_append, List.foldl_append]
  exact out


end Row

-- The signed live-wire search follows L-meta-8463 and L-meta-1449, Apache-2.0.
-- Adjacent assignments on opposite sides of the six-cycle are sampled.

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- The upper and lower halves represent opposite target labels on 48 pairs of assignments.
abbrev W := BitVec 96
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 48 := ((x >>> 48) ^^^ x).setWidth 48
def cuts (ws : List W) : BitVec 48 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 48) ++ (0 : BitVec 48)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 48) (w : W) : Prop :=
  w.getLsbD (48+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 48) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 48+i.val < 96 := by omega
  have hi' : i.val < 96 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 48) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 48)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 96 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 96)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 96) (z : W) : Bool := z[k.val]
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 96) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 96) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#96)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

section Restricted

def fixedOnes (w : List W) : Prop :=
  11 ≤ w.length ∧ ∀ i, pin i = true → w.getD i 0 = ~~~0

lemma fixedOnes_append {w : List W} (h : fixedOnes w) (z : W) :
    fixedOnes (w ++ [z]) := by
  refine ⟨by have := h.1; simp; omega, ?_⟩
  intro i hi
  have hh : i < w.length := by
    have hn := h.1
    have := keep_pin hi
    omega
  rw [List.getD_append _ _ _ _ hh]
  exact h.2 i hi

def charged (g : Gate) : Bool := !(g.inputs.any (pin)) && isBinary g

lemma free_gate (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (hp : fixedOnes w) (g : Gate) (hg : shape g) (hc : (charged ) g = false) :
    holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  rcases hg with ⟨hop,a,ha⟩ | ⟨hop,a,b,_,hab⟩
  · change op = .not at hop
    change args = [a] at ha
    subst op args
    simpa [action] using holds_not (available_read hw a)
  · change op = .and ∨ op = .or at hop
    change args = [a,b] at hab
    subst args
    rcases hop with rfl | rfl
    all_goals
      have ht : pin a = true ∨ pin b = true := by
        cases ha : pin a <;> cases hb : pin b <;> simp_all [charged, isBinary]
      rcases ht with ht | ht
    · change holds av (w.getD a 0 &&& (w.getD b 0 &&& ~~~0))
      rw [hp.2 _ ht]
      change holds av (BitVec.allOnes 96 &&& (w.getD b 0 &&& BitVec.allOnes 96))
      simpa only [BitVec.and_allOnes, BitVec.allOnes_and] using available_read hw b
    · change holds av (w.getD a 0 &&& (w.getD b 0 &&& ~~~0))
      rw [hp.2 _ ht]
      change holds av (w.getD a 0 &&& (BitVec.allOnes 96 &&& BitVec.allOnes 96))
      simpa only [BitVec.and_allOnes] using available_read hw a
    · change holds av (w.getD a 0 ||| (w.getD b 0 ||| 0))
      rw [hp.2 _ ht]
      exact .inr (.inl BitVec.allOnes_or)
    · change holds av (w.getD a 0 ||| (w.getD b 0 ||| 0))
      rw [hp.2 _ ht]
      change holds av (w.getD a 0 ||| (BitVec.allOnes 96 ||| 0#96))
      rw [BitVec.or_zero]
      exact .inr (.inl BitVec.or_allOnes)

lemma shape_legal {g : Gate} (h : shape g) : legal g := by
  rcases h with ⟨ho,a,hi⟩ | ⟨ho,a,b,_,hi⟩
  · simp [legal, ho, hi]
  · exact ⟨ho.imp_right Or.inl, by simp [hi]⟩
set_option maxRecDepth 4000 in
theorem compileRestricted (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, shape g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (hp : fixedOnes w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t ((gs.filter (charged )).length) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (shape_legal (hg g (by simp)))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) (fixedOnes_append hp z) nextEval
    have stepClass := gate_reach w av hw g (shape_legal (hg g (by simp)))
    cases neg : (charged ) g
    · simpa [neg] using cont av hw (free_gate w av hw hp g (hg g (by simp)) neg)
    · have hb : isBinary g = true := by rw [charged, Bool.and_eq_true] at neg; exact neg.2
      simp only [hb,ite_true] at stepClass
      have len : ((g::gs).filter (charged )).length = (gs.filter (charged )).length+1 := by simp [neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩



end Restricted

def inputs : List W := [79220957706355459891957597152, 79214952074864716155432500255, 662959320660763614380063, 399725472523725770294240, 194988035240134804765696, 233985642288176581050368]
def samplePairs : List (ℕ × ℕ) := [(6, 3), (6, 12), (6, 21), (6, 42), (6, 48), (9, 3), (9, 12), (9, 21), (9, 42), (9, 48), (18, 3), (18, 12), (18, 21), (18, 42), (18, 48), (24, 3), (24, 12), (24, 21), (24, 42), (24, 48), (33, 3), (33, 12), (33, 21), (33, 42), (33, 48), (36, 3), (36, 12), (36, 21), (36, 42), (36, 48), (9, 8), (6, 4), (6, 2), (9, 1), (18, 2), (33, 1), (6, 3), (6, 3), (6, 3), (6, 3), (6, 3), (6, 3), (6, 3), (6, 3), (6, 3), (6, 3), (6, 3), (6, 3)]

def projected : List W :=
    [inputs.getD 0 0, inputs.getD 2 0, inputs.getD 4 0, ~~~0, ~~~0, ~~~0,
      inputs.getD 1 0, inputs.getD 3 0, inputs.getD 5 0, inputs.getD 0 0, inputs.getD 2 0]

def sample (k : Fin 96) : Fin 9 → Bool := assign
  (56 + ([0,6,1,7,2,8] : List ℕ).zipIdx.foldl
    (fun acc (i,j) => acc + if (if k.val < 48 then (samplePairs.getD (k.val % 48) (0,0)).1
      else (samplePairs.getD (k.val % 48) (0,0)).2).testBit j then 2^i else 0) 0)

lemma projected_fixed : fixedOnes projected := by
  refine ⟨by decide, ?_⟩
  intro i hi
  rcases relevant_pin hi with rfl | rfl | rfl <;> rfl

lemma projected_holds : ∀ u ∈ projected, holds inputs.toFinset u := by
  intro u hu
  simp only [projected, Bool.false_eq_true, ite_false, ite_true, List.mem_cons,
    List.not_mem_nil, or_false] at hu <;>
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact .inr (.inl rfl)
    | exact .inr (.inr ⟨_, by decide, .inl rfl⟩)

lemma projected_samples : ∀ k : Fin 96,
    fixed.foldl step (List.ofFn (sample k)) = (projected).map (bit k) := by
  decide +kernel

lemma projected_target :
    ∀ k : Fin 96, permanent (sample k) = bit k (~~~goal) := by
  decide +kernel

lemma build_more {g : W} {av : Finset W} {k l : ℕ}
    (h : k ≤ l) (run : build basicOps g k av) : build basicOps g l av := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => exact run
  | succ d ih => exact Or.inl ih

lemma count_charged (gs : List Gate) :
    (gs.filter charged).length + (gs.filter touches).length ≤ gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hc : charged g = (!touches g && isBinary g) := rfl
    cases ht : touches g <;> cases hb : isBinary g <;>
      simp [List.filter_cons, hc, ht, hb] <;> omega

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
lemma signed_check : search 6 inputs = false := by decide +kernel

lemma excludeTail (gs : List Gate) (o : ℕ) (ho : 9 ≤ o)
    (hsize : gs.length ≤ 9) (hs : ∀ g ∈ gs, shape g)
    (he : ∀ x, ((fixed ++ gs).foldl step (List.ofFn x)).getD o false = permanent x) :
    False := by
  have hp : pin o = false := by
    cases hh : pin o
    · rfl
    · have := keep_pin hh
      omega
  have ht := three_touches gs o hp hs he
  have hc := count_charged gs
  obtain ⟨t, ht', hbuild⟩ := compileRestricted gs o hs projected inputs.toFinset
    projected_holds projected_fixed (by
      intro k
      have h := he (sample k)
      rw [List.foldl_append, projected_samples, projected_target] at h
      exact h)
  have run := build_more (l := 6) (by omega) hbuild
  have h := search_complete ht' 6 inputs (by decide) run
  rw [signed_check] at h
  contradiction

lemma prefix_decompose (gs : List Gate)
    (h₀ : gs.head? = some ⟨.and, [0,4]⟩)
    (h₁ : gs.tail.head? = some ⟨.and, [1,5]⟩) :
    ∃ tail, gs = fixed ++ tail := by
  rcases gs with _ | ⟨a,_ | ⟨b,tail⟩⟩
  · simp at h₀
  · simp at h₁
  · simp at h₀ h₁
    exact ⟨tail, by rw [h₀,h₁]; rfl⟩

end PEqualNP.Outside.L_meta_27197_aux

open PEqualNP.Outside.L_meta_27197_aux

theorem PEqualNP.Outside.L_meta_27197 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 5]⟩) := by
  rintro ⟨C, _, hsize, he, ho, hs, _, _, h₀, h₁⟩
  obtain ⟨gs, hg⟩ := prefix_decompose C.gates h₀ h₁
  have hlen : C.gates.length = gs.length + 2 := by simp [hg,fixed]
  change C.gates.length ≤ 11 at hsize
  change C.output + 1 = 9 + C.gates.length at ho
  apply excludeTail gs C.output (by omega) (by omega)
  · intro g hm
    have hm' : g ∈ C.gates := by rw [hg]; exact List.mem_append_right _ hm
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hm'
    rcases hs j with ⟨hop,a,_,ha⟩ | ⟨hop,a,b,hab,_,hargs⟩
    · exact .inl ⟨hop,a,ha⟩
    · exact .inr ⟨hop,a,b,hab,hargs⟩
  · intro x
    rw [← hg]
    exact he x
