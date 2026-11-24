import PEqualNP.Defs
import Mathlib

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

open PEqualNP.EdgeOwnership in
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

open PEqualNP.EdgeOwnership in
lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  apply hF
  apply hbel
  rw [val_and (n := n) (by simp) ha hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
  · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

open PEqualNP.EdgeOwnership in
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

open PEqualNP.EdgeOwnership

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

lemma pairInput_comm {n : ℕ} (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w
  simp only [pairInput, or_comm]

lemma sub_zero2 : (1 : Fin 2) - 0 = 1 := by decide

lemma sub_one2 : (1 : Fin 2) - 1 = 0 := by decide

abbrev G11 : SimpleGraph (Fin 11) :=
  edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
    (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

lemma noFourCycle_G11 : NoFourCycle G11 := by
  dsimp [G11]; decide +kernel

lemma tau_G11 (K : Finset (Fin 11)) (hK : G11.IsVertexCover (↑K : Set (Fin 11))) : 7 ≤ K.card := by
  classical
  let w (i : Fin 11) : ℕ := if i ∈ K then 1 else 0
  have ew (u v : Fin 11) (he : G11.Adj u v) : 1 ≤ w u + w v := by
    rcases hK he with hu | hv
    · change u ∈ K at hu; simp [w, hu]
    · change v ∈ K at hv; simp [w, hv]
  have e0 := ew 1 4 (by decide +kernel)
  have e1 := ew 4 8 (by decide +kernel)
  have e2 := ew 8 1 (by decide +kernel)
  have e3 := ew 3 6 (by decide +kernel)
  have e4 := ew 6 7 (by decide +kernel)
  have e5 := ew 7 3 (by decide +kernel)
  have e6 := ew 0 9 (by decide +kernel)
  have e7 := ew 9 5 (by decide +kernel)
  have e8 := ew 5 2 (by decide +kernel)
  have e9 := ew 2 10 (by decide +kernel)
  have e10 := ew 10 0 (by decide +kernel)
  have hw : ∑ i, w i = K.card := by simp [w]
  rw [Fin.sum_univ_succ] at hw
  simp [Fin.sum_univ_succ] at hw
  omega

lemma inCone_lt (n : ℕ) (C : Circuit) (i j : ℕ) (h : InCone n C i j) :
    i < j ∧ j < C.gates.length := by
  induction j using Nat.strong_induction_on generalizing i with
  | _ j ih =>
    rw [inCone_iff] at h
    rcases h with ⟨hj, k, hkj, _, rfl | hik⟩
    · exact ⟨hkj, hj⟩
    · exact ⟨(ih k hkj i hik).1.trans hkj, hj⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (i j k : ℕ)
    (hij : InCone n C i j) (hjk : InCone n C j k) : InCone n C i k := by
  induction k using Nat.strong_induction_on generalizing i j with
  | _ k ih =>
    rw [inCone_iff] at hjk
    rcases hjk with ⟨hk, m, hmk, hm, rfl | hjm⟩
    · rw [inCone_iff]; exact ⟨hk, j, hmk, hm, Or.inr hij⟩
    · rw [inCone_iff]; exact ⟨hk, m, hmk, hm, Or.inr (ih m hmk i j hij hjm)⟩

lemma opnd_mem_inputs {C : Circuit} {a : ℕ} (b : Fin 2)
    (hlen : (gateAt C a).inputs.length = 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  unfold opnd
  obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp hlen
  fin_cases b <;> simp [hxy]

lemma opnd_lt {n : ℕ} {C : Circuit} (hrb : ReadsBack n C) {a : ℕ}
    (ha : a < C.gates.length) (b : Fin 2) (hlen : (gateAt C a).inputs.length = 2) :
    opnd C a b < n + a := by
  have hm := opnd_mem_inputs b hlen
  have hg := gateAt_mem ha
  have hrb' := hrb a ha (opnd C a b) hm
  simpa [gateAt_eq ha] using hrb'

lemma orReaches_inCone {n : ℕ} {C : Circuit} (hao : IsAO2 n C) {a h : ℕ}
    (ha : a < C.gates.length) (b : Fin 2)
    (hor : OrReaches n C (opnd C a b) h) : InCone n C h a := by
  have hlen : (gateAt C a).inputs.length = 2 := hao.2.2 _ (gateAt_mem ha)
  exact operand_cone ha (opnd_mem_inputs b hlen) (opnd_lt hao.2.1 ha b hlen) (orReaches_reach h _ hor).1

lemma eval_wire_no_and {n : ℕ} {C : Circuit} (hao : IsAO2 n C) (w : ℕ)
    (hno : ∀ h, (gateAt C h).op = GateOp.and → ¬ OrReaches n C w h) (x : Fin n → Bool) :
    val C (List.ofFn x) w = true ↔ ∃ u ∈ orIn n C w, x u = true := by
  constructor
  · intro hv
    obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn x) (by simp) w hv
    rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
    · refine ⟨⟨w', hlt⟩, reach_mem_orIn _ hr, ?_⟩
      rw [← val_ofFn C x ⟨w', hlt⟩]
      exact hv'
    · exfalso
      have hor : OrReaches n C w h := reach_orReaches hr h rfl hh
      have hand : (gateAt C h).op = GateOp.and := by
        rcases hao.1 _ (gateAt_mem hh) with ha | ho
        · exact ha
        · exact absurd ho hop
      exact hno h hand hor
  · rintro ⟨u, hu, hxu⟩
    exact reach_var_val x w u (mem_orIn_reach u hu) hxu

lemma orStep_not_and {n : ℕ} {C : Circuit} {h w : ℕ}
    (hand : (gateAt C h).op = GateOp.and) (hr : Relation.ReflTransGen (OrStep n C) (n + h) w) :
    w = n + h := by
  rcases Relation.ReflTransGen.cases_head hr with rfl | ⟨_, hstep, _⟩
  · rfl
  · obtain ⟨k, _, heq, hop, _⟩ := hstep
    have hk : k = h := by omega
    subst hk
    rw [hand] at hop
    cases hop

lemma orIn_and_empty {n : ℕ} {C : Circuit} {h : ℕ} (hand : (gateAt C h).op = GateOp.and) :
    orIn n C (n + h) = ∅ := by
  ext u
  simp only [Finset.notMem_empty, iff_false]
  intro hu
  have hr := mem_orIn_reach u hu
  have heq := orStep_not_and hand hr
  have : (u : ℕ) < n := u.isLt
  omega

lemma no_and_in_junk_cone {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (x4 x5 : ℕ) (htop : TopForm G C) (hj : junk G C = {x4, x5})
    (h45 : ¬ InCone n C x4 x5) (h54 : ¬ InCone n C x5 x4)
    {h : ℕ} (hh : h = x4 ∨ h = x5) {g : ℕ} (hg : g < C.gates.length)
    (hand : (gateAt C g).op = GateOp.and) : ¬ InCone n C g h := by
  intro hin
  have hh_mem : h ∈ junk G C := by rw [hj]; rcases hh with rfl | rfl <;> simp
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hh_mem
  have hlt := hh_mem.1
  have hhand : (gateAt C h).op = GateOp.and := hh_mem.2.1
  by_cases hbel : BelowF G C g
  · exact htop g hg h hlt hand hbel hhand hin
  · have hdirty : IsDirtyAnd n G C g := by
      refine ⟨hand, hg, ?_⟩
      unfold BelowF at hbel
      push Not at hbel
      obtain ⟨x, hx1, hx2⟩ := hbel
      exact ⟨x, hx1, Bool.eq_false_iff.mpr hx2⟩
    have hg_mem : g ∈ junk G C := by
      simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]
      exact ⟨hg, hdirty⟩
    rw [hj, Finset.mem_insert, Finset.mem_singleton] at hg_mem
    have hne : g ≠ h := (inCone_lt n C g h hin).1.ne
    rcases hh with rfl | rfl <;> rcases hg_mem with rfl | rfl
    · exact hne rfl
    · exact h54 hin
    · exact h45 hin
    · exact hne rfl

lemma junk_eval_eq {n : ℕ} {C : Circuit} (hao : IsAO2 n C) {h : ℕ}
    (hh : h < C.gates.length) (hand : (gateAt C h).op = GateOp.and)
    (hno : ∀ g, g < C.gates.length → (gateAt C g).op = GateOp.and → ¬ InCone n C g h)
    (x : Fin n → Bool) :
    gateVal n C h x = true ↔
      (∃ u ∈ side C h 0, x u = true) ∧ (∃ v ∈ side C h 1, x v = true) := by
  have hlen : (gateAt C h).inputs.length = 2 := hao.2.2 _ (gateAt_mem hh)
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen
  have hp0 : opnd C h 0 = p := by simp [opnd, hpq]
  have hq1 : opnd C h 1 = q := by simp [opnd, hpq]
  have hp_lt : p < n + h := hp0 ▸ opnd_lt hao.2.1 hh 0 hlen
  have hq_lt : q < n + h := hq1 ▸ opnd_lt hao.2.1 hh 1 hlen
  have hno_w (b : Fin 2) : ∀ g, (gateAt C g).op = GateOp.and → ¬ OrReaches n C (opnd C h b) g := by
    intro g hg hor
    have hg_lt : g < C.gates.length := (orReaches_reach g _ hor).2
    exact hno g hg_lt hg (orReaches_inCone hao hh b hor)
  rw [gateVal_eq_val, val_and (n := n) (by simp) hh hand, hpq]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro H
    have H0 := (H p (Or.inl rfl)).2
    have H1 := (H q (Or.inr rfl)).2
    rw [← hp0, eval_wire_no_and hao _ (hno_w 0) x] at H0
    rw [← hq1, eval_wire_no_and hao _ (hno_w 1) x] at H1
    exact ⟨H0, H1⟩
  · rintro ⟨H0, H1⟩ i hi
    rcases hi with rfl | rfl
    · refine ⟨hp_lt, ?_⟩
      rw [← hp0, eval_wire_no_and hao _ (hno_w 0) x]
      exact H0
    · refine ⟨hq_lt, ?_⟩
      rw [← hq1, eval_wire_no_and hao _ (hno_w 1) x]
      exact H1

lemma orIn_lam_not_Ustar {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit)
    (hStars : ∀ a ∈ tops G C,
      (∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v) ∧
      ((side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1))
    {g : ℕ} (hg : g ∈ lam G C) :
    ∃ c : Fin n, ∀ v ∈ orIn n C (n + g), G.Adj c v ∧ s(c, v) ∉ Ustar G C := by
  simp only [lam, Finset.mem_filter] at hg
  obtain ⟨_, _, _, a, ha, b, hcard, hor⟩ := hg
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
  refine ⟨c, fun v hv => ?_⟩
  have hvc : c ∈ side (n := n) C a (1 - b) := by rw [hc]; exact Finset.mem_singleton_self c
  have hrg := (orReaches_reach g _ hor).1
  have hrv := mem_orIn_reach v hv
  have hva : v ∈ side (n := n) C a b := reach_mem_orIn v (hrg.trans hrv)
  have hadj : G.Adj c v := by
    have hs := (hStars a ha).1
    fin_cases b
    · exact (hs v hva c hvc).symm
    · exact hs c hvc v hva
  have hstar : s(c, v) ∈ starEdges G C := by
    simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
    refine ⟨a, ha, ?_⟩
    fin_cases b
    · refine ⟨(v, c), ⟨hva, hvc⟩, Sym2.eq_swap⟩
    · refine ⟨(c, v), ⟨hvc, hva⟩, rfl⟩
  refine ⟨hadj, fun hU => ?_⟩
  simp only [Ustar, Finset.mem_sdiff] at hU
  exact hU.2 hstar

lemma orTrace_R_or_V {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) {a h : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hh : h ∈ junk G C) (hor : OrReaches n C (opnd C a b) h) :
    a ∈ centreless G C ∨
      ∃ m ∈ orN G C \ lam G C,
        OrReaches n C (opnd C a b) m ∧ OrReaches n C (n + m) h ∧
        (opnd C m 0 = n + h ∨ opnd C m 1 = n + h) := by
  have hh' := hh
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hh'
  have hh_lt := hh'.1
  have hh_and : (gateAt C h).op = GateOp.and := hh'.2.1
  obtain ⟨xd, hxd1, hxd2⟩ := hh'.2.2.2
  have hnw : n ≤ opnd C a b := hor.1
  obtain ⟨k0, hk0⟩ : ∃ k0, opnd C a b = n + k0 := ⟨opnd C a b - n, by omega⟩
  by_cases heq : k0 = h
  · left
    simp only [centreless, Finset.mem_filter]
    refine ⟨ha, ?_⟩
    have hempty : side (n := n) C a b = ∅ := by
      unfold side
      rw [hk0, heq]
      exact orIn_and_empty hh_and
    fin_cases b
    · exact Or.inl hempty
    · exact Or.inr hempty
  · right
    have dirty_reach : ∀ k, OrReaches n C (n + k) h → ¬ BelowF G C k := by
      intro k hk hbel
      have hr := (orReaches_reach h (n + k) hk).1
      have hval : gateVal n C k xd = true := by
        rw [gateVal_eq_val]
        apply orStep_up (n := n) (by simp) hr
        rw [← gateVal_eq_val]
        exact hxd1
      have := hbel xd hval
      rw [this] at hxd2
      cases hxd2
    have k0_lt : k0 < C.gates.length := ((orReaches_iff n C k0 h).mp (hk0 ▸ hor)).1
    have k0_orN : k0 ∈ orN G C := by
      obtain ⟨hk0_lt, hk0_cases⟩ := (orReaches_iff n C k0 h).mp (hk0 ▸ hor)
      rcases hk0_cases with rfl | ⟨hk0_or, _⟩
      · exact absurd rfl heq
      · simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
        exact ⟨hk0_lt, hk0_or, dirty_reach k0 (hk0 ▸ hor)⟩
    let S : Finset ℕ := (orN G C).filter fun m =>
      OrReaches n C (opnd C a b) m ∧ OrReaches n C (n + m) h
    have hS : S.Nonempty := ⟨k0, Finset.mem_filter.mpr ⟨k0_orN,
      hk0 ▸ reach_orReaches Relation.ReflTransGen.refl k0 rfl k0_lt, hk0 ▸ hor⟩⟩
    obtain ⟨m, hmS, hm_min⟩ := Finset.exists_min_image S id hS
    simp only [S, Finset.mem_filter] at hmS
    obtain ⟨hm_orN, hm_reach1, hm_reach2⟩ := hmS
    have hm_orN' := hm_orN
    simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at hm_orN'
    obtain ⟨hm_lt, hm_or, _⟩ := hm_orN'
    obtain ⟨_, hm_cases⟩ := (orReaches_iff n C m h).mp hm_reach2
    rcases hm_cases with rfl | ⟨_, i, hi_mem, hi_lt, hi_reach⟩
    · rw [hm_or] at hh_and; cases hh_and
    · have hi_nw : n ≤ i := hi_reach.1
      obtain ⟨m', hm'⟩ : ∃ m', i = n + m' := ⟨i - n, by omega⟩
      have hm'_eq_h : m' = h := by
        by_contra hne
        obtain ⟨hm'_lt, hm'_cases⟩ := (orReaches_iff n C m' h).mp (hm' ▸ hi_reach)
        rcases hm'_cases with rfl | ⟨hm'_or, _⟩
        · exact hne rfl
        · have hm'_orN : m' ∈ orN G C := by
            simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
            exact ⟨hm'_lt, hm'_or, dirty_reach m' (hm' ▸ hi_reach)⟩
          have hm'_reach1 : OrReaches n C (opnd C a b) m' := by
            have hr1 := (orReaches_reach m _ hm_reach1).1
            have hstep : OrStep n C (n + m) (n + m') :=
              ⟨m, hm_lt, rfl, hm_or, hm' ▸ hi_mem, hm' ▸ hi_lt⟩
            exact reach_orReaches (hr1.tail hstep) m' rfl hm'_lt
          have hm'_S : m' ∈ S := Finset.mem_filter.mpr ⟨hm'_orN, hm'_reach1, hm' ▸ hi_reach⟩
          have hle := hm_min m' hm'_S
          dsimp [id] at hle
          omega
      have hi_eq : i = n + h := by omega
      have hlen : (gateAt C m).inputs.length = 2 := hao.2.2 _ (gateAt_mem hm_lt)
      obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen
      have hop_eq : opnd C m 0 = n + h ∨ opnd C m 1 = n + h := by
        rw [hpq] at hi_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi_mem
        rcases hi_mem with rfl | rfl
        · left; simp [opnd, hpq, hi_eq]
        · right; simp [opnd, hpq, hi_eq]
      have hm_not_lam : m ∉ lam G C := by
        intro hlam
        simp only [lam, Finset.mem_filter] at hlam
        obtain ⟨_, h0, h1, _⟩ := hlam
        rcases hop_eq with h0eq | h1eq
        · rw [h0eq, orIn_and_empty hh_and] at h0
          exact Finset.not_nonempty_empty h0
        · rw [h1eq, orIn_and_empty hh_and] at h1
          exact Finset.not_nonempty_empty h1
      exact ⟨m, Finset.mem_sdiff.mpr ⟨hm_orN, hm_not_lam⟩, hm_reach1, hm_reach2, hop_eq⟩

lemma orIn_mono_orStep {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    orIn n C w' ⊆ orIn n C w := by
  intro u hu
  exact reach_mem_orIn u (h.trans (mem_orIn_reach u hu))

lemma or_tree_R_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C)
    (hnoEdge : ∀ u : Fin n, graphFun G ∅ (pairInput u u) = false)
    (w : ℕ) (hno : ∀ g, (gateAt C g).op = GateOp.and → ¬ OrReaches n C w g)
    (W : Finset (Fin n)) (hW : W ⊆ orIn n C w)
    (hlam : ∀ g ∈ lam G C, OrReaches n C w g → (orIn n C (n + g) ∩ W).card ≤ 1) :
    W.card ≤ 1 + ((orN G C \ lam G C).filter fun g =>
      OrReaches n C w g ∧ 2 ≤ (orIn n C (n + g) ∩ W).card).card := by
  induction w using Nat.strong_induction_on generalizing W with
  | _ w ih =>
    by_cases hW1 : W.card ≤ 1
    · omega
    · have hW2 : 2 ≤ W.card := by omega
      have hWne : W.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨u0, hu0⟩ := hWne
      have hu0_orIn := hW hu0
      have hnw : n ≤ w := by
        by_contra hlt
        have hlt' : w < n := by omega
        have hsub : orIn n C w ⊆ {⟨w, hlt'⟩} := by
          intro v hv
          have hr := mem_orIn_reach v hv
          rcases Relation.ReflTransGen.cases_head hr with hv_eq | ⟨_, hstep, _⟩
          · rw [Finset.mem_singleton]; ext; exact hv_eq.symm
          · obtain ⟨k, _, heq, _⟩ := hstep; omega
        have hle := Finset.card_le_card (hW.trans hsub)
        simp at hle
        omega
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk_orIn : (orIn n C (n + k)).Nonempty := ⟨u0, hu0_orIn⟩
      have hk_lt : k < C.gates.length := by
        rcases (by simpa [orIn] using hu0_orIn) with h | ⟨m, hm, hr, _⟩
        · have : (u0 : ℕ) < n := u0.isLt; omega
        · exact ((orReaches_iff n C k m).mp hr).1
      have hk_or : (gateAt C k).op = GateOp.or := by
        rcases hao.1 _ (gateAt_mem hk_lt) with hand | hor
        · exfalso
          have := hno k hand ((orReaches_iff n C k k).mpr ⟨hk_lt, Or.inl rfl⟩)
          exact this
        · exact hor
      have hk_not_bel : ¬ BelowF G C k := by
        intro hbel
        have hval : gateVal n C k (pairInput u0 u0) = true := by
          rw [gateVal_eq_val]
          exact reach_var_val _ _ u0 (mem_orIn_reach u0 hu0_orIn) (pairInput_left u0 u0)
        have := hbel (pairInput u0 u0) hval
        rw [hnoEdge u0] at this
        cases this
      have hk_orN : k ∈ orN G C := by
        simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
        exact ⟨hk_lt, hk_or, hk_not_bel⟩
      have hk_reach : OrReaches n C (n + k) k := (orReaches_iff n C k k).mpr ⟨hk_lt, Or.inl rfl⟩
      have hk_not_lam : k ∉ lam G C := by
        intro hkl
        have := hlam k hkl hk_reach
        have hinter : orIn n C (n + k) ∩ W = W := Finset.inter_eq_right.mpr hW
        rw [hinter] at this
        omega
      have hk_R : k ∈ (orN G C \ lam G C).filter fun g =>
          OrReaches n C (n + k) g ∧ 2 ≤ (orIn n C (n + g) ∩ W).card := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hk_orN, hk_not_lam⟩, hk_reach, ?_⟩
        rw [Finset.inter_eq_right.mpr hW]
        exact hW2
      let p := opnd C k 0
      let q := opnd C k 1
      have hlen : (gateAt C k).inputs.length = 2 := hao.2.2 _ (gateAt_mem hk_lt)
      have hp_lt : p < n + k := opnd_lt hao.2.1 hk_lt 0 hlen
      have hq_lt : q < n + k := opnd_lt hao.2.1 hk_lt 1 hlen
      have hp_mem : p ∈ (gateAt C k).inputs := opnd_mem_inputs 0 hlen
      have hq_mem : q ∈ (gateAt C k).inputs := opnd_mem_inputs 1 hlen
      have hp_step : OrStep n C (n + k) p := ⟨k, hk_lt, rfl, hk_or, hp_mem, hp_lt⟩
      have hq_step : OrStep n C (n + k) q := ⟨k, hk_lt, rfl, hk_or, hq_mem, hq_lt⟩
      have hp_sub : orIn n C p ⊆ orIn n C (n + k) :=
        orIn_mono_orStep (Relation.ReflTransGen.single hp_step)
      have hq_sub : orIn n C q ⊆ orIn n C (n + k) :=
        orIn_mono_orStep (Relation.ReflTransGen.single hq_step)
      have hsplit : orIn n C (n + k) ⊆ orIn n C p ∪ orIn n C q := by
        intro u hu
        have hr := mem_orIn_reach u hu
        rcases Relation.ReflTransGen.cases_head hr with heq | ⟨c, hstep, hrest⟩
        · omega
        · obtain ⟨k', _, heq', _, hcmem, _⟩ := hstep
          have hk' : k' = k := by omega
          subst hk'
          obtain ⟨x, y, hxy⟩ := List.length_eq_two.mp hlen
          rw [hxy] at hcmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hcmem
          rcases hcmem with rfl | rfl
          · have : p = c := by simp [p, opnd, hxy]
            rw [← this] at hrest
            exact Finset.mem_union_left _ (reach_mem_orIn u hrest)
          · have : q = c := by simp [q, opnd, hxy]
            rw [← this] at hrest
            exact Finset.mem_union_right _ (reach_mem_orIn u hrest)
      let W0 := W ∩ orIn n C p
      let W1 := W \ W0
      have hW0_sub : W0 ⊆ orIn n C p := Finset.inter_subset_right
      have hW1_sub : W1 ⊆ orIn n C q := by
        intro u hu
        simp only [W1, W0, Finset.mem_sdiff, Finset.mem_inter] at hu
        rcases Finset.mem_union.mp (hsplit (hW hu.1)) with h1 | h2
        · exact absurd ⟨hu.1, h1⟩ hu.2
        · exact h2
      have reach_up (c : ℕ) (hc : OrStep n C (n + k) c) (g : ℕ) (hg : OrReaches n C c g) :
          OrReaches n C (n + k) g := by
        obtain ⟨hr, hg_lt⟩ := orReaches_reach g c hg
        exact reach_orReaches (Relation.ReflTransGen.head hc hr) g rfl hg_lt
      have hno_p : ∀ g, (gateAt C g).op = GateOp.and → ¬ OrReaches n C p g :=
        fun g hg hor => hno g hg (reach_up p hp_step g hor)
      have hno_q : ∀ g, (gateAt C g).op = GateOp.and → ¬ OrReaches n C q g :=
        fun g hg hor => hno g hg (reach_up q hq_step g hor)
      have hlam_p : ∀ g ∈ lam G C, OrReaches n C p g → (orIn n C (n + g) ∩ W0).card ≤ 1 := by
        intro g hgl hor
        have hsub : orIn n C (n + g) ∩ W0 ⊆ orIn n C (n + g) ∩ W :=
          Finset.inter_subset_inter_left Finset.inter_subset_left
        exact (Finset.card_le_card hsub).trans (hlam g hgl (reach_up p hp_step g hor))
      have hlam_q : ∀ g ∈ lam G C, OrReaches n C q g → (orIn n C (n + g) ∩ W1).card ≤ 1 := by
        intro g hgl hor
        have hsub : orIn n C (n + g) ∩ W1 ⊆ orIn n C (n + g) ∩ W :=
          Finset.inter_subset_inter_left Finset.sdiff_subset
        exact (Finset.card_le_card hsub).trans (hlam g hgl (reach_up q hq_step g hor))
      have ihp := ih p hp_lt hno_p W0 hW0_sub hlam_p
      have ihq := ih q hq_lt hno_q W1 hW1_sub hlam_q
      let Rall := (orN G C \ lam G C).filter fun g =>
        OrReaches n C (n + k) g ∧ 2 ≤ (orIn n C (n + g) ∩ W).card
      let Rp := (orN G C \ lam G C).filter fun g =>
        OrReaches n C p g ∧ 2 ≤ (orIn n C (n + g) ∩ W0).card
      let Rq := (orN G C \ lam G C).filter fun g =>
        OrReaches n C q g ∧ 2 ≤ (orIn n C (n + g) ∩ W1).card
      have hRp_sub : Rp ⊆ Rall := by
        intro g hg
        simp only [Rp, Rall, Finset.mem_filter] at hg ⊢
        refine ⟨hg.1, reach_up p hp_step g hg.2.1, ?_⟩
        have hsub2 : orIn n C (n + g) ∩ W0 ⊆ orIn n C (n + g) ∩ W :=
          Finset.inter_subset_inter_left Finset.inter_subset_left
        exact hg.2.2.trans (Finset.card_le_card hsub2)
      have hRq_sub : Rq ⊆ Rall := by
        intro g hg
        simp only [Rq, Rall, Finset.mem_filter] at hg ⊢
        refine ⟨hg.1, reach_up q hq_step g hg.2.1, ?_⟩
        have hsub2 : orIn n C (n + g) ∩ W1 ⊆ orIn n C (n + g) ∩ W :=
          Finset.inter_subset_inter_left Finset.sdiff_subset
        exact hg.2.2.trans (Finset.card_le_card hsub2)
      have hk_not_Rp : k ∉ Rp := by
        intro hmem
        simp only [Rp, Finset.mem_filter] at hmem
        have := orStep_le (orReaches_reach k p hmem.2.1).1
        omega
      have hk_not_Rq : k ∉ Rq := by
        intro hmem
        simp only [Rq, Finset.mem_filter] at hmem
        have := orStep_le (orReaches_reach k q hmem.2.1).1
        omega
      have hdisj_pq : Disjoint Rp Rq := by
        rw [Finset.disjoint_left]
        intro g hgp hgq
        simp only [Rp, Rq, Finset.mem_filter] at hgp hgq
        have hgp_sub : orIn n C (n + g) ⊆ orIn n C p :=
          orIn_mono_orStep (orReaches_reach g p hgp.2.1).1
        have hinter_empty : orIn n C (n + g) ∩ W1 = ∅ := by
          ext u
          simp only [Finset.mem_inter, W1, W0, Finset.mem_sdiff, Finset.notMem_empty, iff_false]
          rintro ⟨hu1, hu2, hu3⟩
          exact hu3 ⟨hu2, hgp_sub hu1⟩
        rw [hinter_empty] at hgq
        simp at hgq
      have hcard_union : (insert k (Rp ∪ Rq)).card ≤ Rall.card := by
        apply Finset.card_le_card
        intro g hg
        simp only [Finset.mem_insert, Finset.mem_union] at hg
        rcases hg with rfl | h1 | h2
        · exact hk_R
        · exact hRp_sub h1
        · exact hRq_sub h2
      rw [Finset.card_insert_of_notMem (by simp [hk_not_Rp, hk_not_Rq]),
        Finset.card_union_of_disjoint hdisj_pq] at hcard_union
      have hW_card : W.card = W0.card + W1.card := by
        have h1 : W1 = W \ orIn n C p := by
          ext u; simp [W1, W0]
        rw [h1]
        have h2 := Finset.card_sdiff_add_card_inter W (orIn n C p)
        dsimp [W0]
        omega
      change W0.card ≤ 1 + Rp.card at ihp
      change W1.card ≤ 1 + Rq.card at ihq
      change W.card ≤ 1 + Rall.card
      omega

lemma side_nonempty_of_eval {n : ℕ} {C : Circuit} (hao : IsAO2 n C) {h : ℕ}
    (hh : h < C.gates.length) (hand : (gateAt C h).op = GateOp.and)
    (hno : ∀ g, g < C.gates.length → (gateAt C g).op = GateOp.and → ¬ InCone n C g h)
    (x : Fin n → Bool) (hx : gateVal n C h x = true) :
    (side (n := n) C h 0).Nonempty ∧ (side (n := n) C h 1).Nonempty := by
  have hiff := (junk_eval_eq hao hh hand hno x).mp hx
  exact ⟨⟨hiff.1.choose, hiff.1.choose_spec.1⟩, ⟨hiff.2.choose, hiff.2.choose_spec.1⟩⟩

lemma junk_other_side_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hao : IsAO2 n C) (htop : TopForm G C)
    {x4 x5 h : ℕ} (hj : junk G C = {x4, x5}) (h45 : ¬ InCone n C x4 x5) (h54 : ¬ InCone n C x5 x4)
    (hh_eq : h = x4 ∨ h = x5)
    (hdisj_top : ∀ a ∈ tops G C, InCone n C x4 a → ¬ InCone n C x5 a)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hor : OrReaches n C (opnd C a b) h)
    (u v : Fin n) (hval_a : gateVal n C a (pairInput u v) = true) :
    ∃ w ∈ side (n := n) C a (1 - b), (w = u ∨ w = v) ∧
      ∀ z : Fin n, gateVal n C h (pairInput w z) = true → z ≠ w ∧ G.Adj w z := by
  have ha' := ha
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
  obtain ⟨ha_lt, ha_and, ha_bel⟩ := ha'
  have hh_mem : h ∈ junk G C := by rw [hj]; rcases hh_eq with rfl | rfl <;> simp
  have hh' := hh_mem
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hh'
  obtain ⟨hh_lt, hh_and, _, xd, hxd1, hxd2⟩ := hh'
  have hno_other : ∀ g, (gateAt C g).op = GateOp.and → ¬ OrReaches n C (opnd C a (1 - b)) g := by
    intro g hg hor_g
    have hg_lt := (orReaches_reach g _ hor_g).2
    by_cases hbel : BelowF G C g
    · exact htop g hg_lt a ha_lt hg hbel ha_and (orReaches_inCone hao ha_lt (1 - b) hor_g)
    · have hg_mem : g ∈ junk G C := by
        simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]
        refine ⟨hg_lt, hg, hg_lt, ?_⟩
        unfold BelowF at hbel; push Not at hbel
        obtain ⟨y, hy1, hy2⟩ := hbel
        exact ⟨y, hy1, Bool.eq_false_iff.mpr hy2⟩
      rw [hj, Finset.mem_insert, Finset.mem_singleton] at hg_mem
      by_cases hgh : g = h
      · subst hgh
        have hlen : (gateAt C a).inputs.length = 2 := hao.2.2 _ (gateAt_mem ha_lt)
        obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen
        have hval_xd : gateVal n C a xd = true := by
          rw [gateVal_eq_val, val_and (n := n) (by simp) ha_lt ha_and, hpq]
          intro i hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          have hor0 : OrReaches n C (opnd C a 0) g := by
            fin_cases b
            · exact hor
            · simpa using hor_g
          have hor1 : OrReaches n C (opnd C a 1) g := by
            fin_cases b
            · simpa using hor_g
            · exact hor
          rcases hi with rfl | rfl
          · refine ⟨by simpa [opnd, hpq] using opnd_lt hao.2.1 ha_lt 0 hlen, ?_⟩
            have hr := (orReaches_reach g _ hor0).1
            simp only [opnd, hpq] at hr
            exact orStep_up (n := n) (by simp) hr (by rw [← gateVal_eq_val]; exact hxd1)
          · refine ⟨by simpa [opnd, hpq] using opnd_lt hao.2.1 ha_lt 1 hlen, ?_⟩
            have hr := (orReaches_reach g _ hor1).1
            simp only [opnd, hpq] at hr
            exact orStep_up (n := n) (by simp) hr (by rw [← gateVal_eq_val]; exact hxd1)
        have := ha_bel xd hval_xd
        rw [this] at hxd2
        cases hxd2
      · have hc1 := orReaches_inCone hao ha_lt b hor
        have hc2 := orReaches_inCone hao ha_lt (1 - b) hor_g
        rcases hh_eq with rfl | rfl <;> rcases hg_mem with rfl | rfl
        · exact hgh rfl
        · exact hdisj_top a ha hc1 hc2
        · exact hdisj_top a ha hc2 hc1
        · exact hgh rfl
  have hlen : (gateAt C a).inputs.length = 2 := hao.2.2 _ (gateAt_mem ha_lt)
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hlen
  have hval_1b : val C (List.ofFn (pairInput u v)) (opnd C a (1 - b)) = true := by
    rw [gateVal_eq_val, val_and (n := n) (by simp) ha_lt ha_and, hpq] at hval_a
    fin_cases b
    · simpa [opnd, hpq] using (hval_a q (by simp)).2
    · simpa [opnd, hpq] using (hval_a p (by simp)).2
  rw [eval_wire_no_and hao _ hno_other (pairInput u v)] at hval_1b
  obtain ⟨w, hw_side, hw_pi⟩ := hval_1b
  refine ⟨w, hw_side, (pairInput_true u v w).mp hw_pi, fun z hz => ?_⟩
  have ha_wz : gateVal n C a (pairInput w z) = true := by
    rw [gateVal_eq_val, val_and (n := n) (by simp) ha_lt ha_and, hpq]
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    have h1 : val C (List.ofFn (pairInput w z)) (opnd C a (1 - b)) = true :=
      reach_var_val (pairInput w z) _ w (mem_orIn_reach w hw_side) (pairInput_left w z)
    have h2 : val C (List.ofFn (pairInput w z)) (opnd C a b) = true :=
      orStep_up (n := n) (by simp) (orReaches_reach h _ hor).1 (by rw [← gateVal_eq_val]; exact hz)
    rcases hi with rfl | rfl
    · refine ⟨by simpa [opnd, hpq] using opnd_lt hao.2.1 ha_lt 0 hlen, ?_⟩
      fin_cases b
      · simpa [opnd, hpq] using h2
      · simpa [opnd, hpq] using h1
    · refine ⟨by simpa [opnd, hpq] using opnd_lt hao.2.1 ha_lt 1 hlen, ?_⟩
      fin_cases b
      · simpa [opnd, hpq] using h1
      · simpa [opnd, hpq] using h2
  have hF := ha_bel (pairInput w z) ha_wz
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at hF
  obtain ⟨x', y', hadj, hmemx, hmemy⟩ := hF
  have hx' : x' = w ∨ x' = z := (pairInput_true w z x').mp hmemx
  have hy' : y' = w ∨ y' = z := (pairInput_true w z y').mp hmemy
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
  · exact absurd rfl (G.ne_of_adj hadj)
  · exact ⟨hadj.ne.symm, hadj⟩
  · exact ⟨hadj.ne, hadj.symm⟩
  · exact absurd rfl (G.ne_of_adj hadj)

lemma noFourCycle_common_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hnf : NoFourCycle G) {a b : Fin n} (hab : a ≠ b) (S : Finset (Fin n))
    (hS : ∀ v ∈ S, G.Adj a v ∧ G.Adj b v) : S.card ≤ 1 := by
  have hsub : S ⊆ Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w := by
    intro v hv; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS v hv⟩
  exact (Finset.card_le_card hsub).trans (hnf a b hab)

lemma side_lam_bound (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
    (hnf : NoFourCycle G) (C : Circuit)
    (hStars : ∀ a ∈ tops G C,
      (∀ u ∈ side (n := 11) C a 0, ∀ v ∈ side (n := 11) C a 1, G.Adj u v) ∧
      ((side (n := 11) C a 0).card ≤ 1 ∨ (side (n := 11) C a 1).card ≤ 1))
    (w : Fin 11) (W : Finset (Fin 11))
    (hW : ∀ v ∈ W, G.Adj w v ∧ s(w, v) ∈ Ustar G C)
    (g : ℕ) (hg : g ∈ lam G C) :
    (orIn 11 C (11 + g) ∩ W).card ≤ 1 := by
  obtain ⟨c, hc⟩ := orIn_lam_not_Ustar G C hStars hg
  by_cases hcw : c = w
  · subst hcw
    have hempty : orIn 11 C (11 + g) ∩ W = ∅ := by
      ext v
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
      rintro ⟨hv1, hv2⟩
      exact (hc v hv1).2 (hW v hv2).2
    rw [hempty]; simp
  · refine noFourCycle_common_le_one G hnf (Ne.symm hcw) _ ?_
    intro v hv
    simp only [Finset.mem_inter] at hv
    exact ⟨(hW v hv.2).1, (hc v hv.1).1⟩

lemma junk_cover_and_R_bound (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
    (hnf : NoFourCycle G) (C : Circuit) (hao : IsAO2 11 C) (htop : TopForm G C)
    (hStars : ∀ a ∈ tops G C,
      (∀ u ∈ side (n := 11) C a 0, ∀ v ∈ side (n := 11) C a 1, G.Adj u v) ∧
      ((side (n := 11) C a 0).card ≤ 1 ∨ (side (n := 11) C a 1).card ≤ 1))
    {x4 x5 h : ℕ} (hj : junk G C = {x4, x5}) (h45 : ¬ InCone 11 C x4 x5) (h54 : ¬ InCone 11 C x5 x4)
    (hh_eq : h = x4 ∨ h = x5)
    (hdisj_top : ∀ a ∈ tops G C, InCone 11 C x4 a → ¬ InCone 11 C x5 a)
    (Uh : Finset (Sym2 (Fin 11))) (hUh_sub : Uh ⊆ Ustar G C)
    (hUh_wit : ∀ u v : Fin 11, s(u, v) ∈ Uh →
      ∃ a ∈ tops G C, ∃ b : Fin 2,
        gateVal 11 C a (pairInput u v) = true ∧
        OrReaches 11 C (opnd C a b) h ∧
        gateVal 11 C h (pairInput u v) = true)
    (hUh_ne : Uh.Nonempty) :
    (∃ Xh : Finset (Fin 11), Xh.card ≤ 2 ∧
      (∀ u v : Fin 11, s(u, v) ∈ Uh → u ∈ Xh ∨ v ∈ Xh) ∧
      Uh.card ≤ 1 + ((orN G C \ lam G C).filter fun g =>
        g < h ∧ (OrReaches 11 C (opnd C h 0) g ∨ OrReaches 11 C (opnd C h 1) g)).card) ∨
    (∃ z : Fin 11, gateVal 11 C h (pairInput z z) = true) := by
  have hh_mem : h ∈ junk G C := by rw [hj]; rcases hh_eq with rfl | rfl <;> simp
  have hh' := hh_mem
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hh'
  obtain ⟨hh_lt, hh_and, _⟩ := hh'
  have hno_h : ∀ g, g < C.gates.length → (gateAt C g).op = GateOp.and → ¬ InCone 11 C g h :=
    fun g hg hand => no_and_in_junk_cone G C x4 x5 htop hj h45 h54 hh_eq hg hand
  have hno_op (b : Fin 2) : ∀ g, (gateAt C g).op = GateOp.and → ¬ OrReaches 11 C (opnd C h b) g := by
    intro g hg hor
    exact hno_h g (orReaches_reach g _ hor).2 hg (orReaches_inCone hao hh_lt b hor)
  have hnoEdge : ∀ u : Fin 11, graphFun G ∅ (pairInput u u) = false := by
    intro u
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_false_iff_not]
    rintro ⟨x', y', hadj, hx', hy'⟩
    have hx'' := (pairInput_true u u x').mp hx'
    have hy'' := (pairInput_true u u y').mp hy'
    rcases hx'' with rfl | rfl <;> rcases hy'' with rfl | rfl <;> exact G.ne_of_adj hadj rfl
  let S0 := side (n := 11) C h 0
  let S1 := side (n := 11) C h 1
  by_cases hinter_ne : (S0 ∩ S1).Nonempty
  · right
    obtain ⟨z, hz⟩ := hinter_ne
    rw [Finset.mem_inter] at hz
    refine ⟨z, ?_⟩
    rw [junk_eval_eq hao hh_lt hh_and hno_h]
    exact ⟨⟨z, hz.1, pairInput_left z z⟩, ⟨z, hz.2, pairInput_left z z⟩⟩
  left
  have hdisj_S : Disjoint S0 S1 := Finset.not_nonempty_iff_eq_empty.mp hinter_ne |> Finset.disjoint_iff_inter_eq_empty.mpr
  obtain ⟨e0, he0⟩ := hUh_ne
  have hne_sides : S0.Nonempty ∧ S1.Nonempty := by
    induction e0 using Sym2.ind with
    | _ u v =>
      obtain ⟨_, _, _, _, _, hval⟩ := hUh_wit u v he0
      exact side_nonempty_of_eval hao hh_lt hh_and hno_h (pairInput u v) hval
  let Rcone := (orN G C \ lam G C).filter fun g =>
    g < h ∧ (OrReaches 11 C (opnd C h 0) g ∨ OrReaches 11 C (opnd C h 1) g)
  have hR_sub (b : Fin 2) (W : Finset (Fin 11)) :
      ((orN G C \ lam G C).filter fun g =>
        OrReaches 11 C (opnd C h b) g ∧ 2 ≤ (orIn 11 C (11 + g) ∩ W).card) ⊆ Rcone := by
    intro g hg
    simp only [Finset.mem_filter, Rcone] at hg ⊢
    refine ⟨hg.1, (inCone_lt 11 C g h (orReaches_inCone hao hh_lt b hg.2.1)).1, ?_⟩
    fin_cases b
    · exact Or.inl hg.2.1
    · exact Or.inr hg.2.1
  have hstar_side (w : Fin 11) (W : Finset (Fin 11))
      (hW_sub : W ⊆ S0 ∨ W ⊆ S1)
      (hW_cov : ∀ e ∈ Uh, ∃ v ∈ W, e = s(w, v))
      (hW_edge : ∀ v ∈ W, G.Adj w v ∧ s(w, v) ∈ Ustar G C) :
      Uh.card ≤ 1 + Rcone.card := by
    have hUh_le : Uh.card ≤ W.card := by
      have hsub : Uh ⊆ W.image (fun v => s(w, v)) := by
        intro e he
        obtain ⟨v, hv, rfl⟩ := hW_cov e he
        exact Finset.mem_image_of_mem _ hv
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    rcases hW_sub with hW0 | hW1
    · have htree := or_tree_R_count G C hao hnoEdge (opnd C h 0) (hno_op 0) W hW0
        (fun g hg _ => side_lam_bound G hnf C hStars w W hW_edge g hg)
      have hrc := Finset.card_le_card (hR_sub 0 W)
      omega
    · have htree := or_tree_R_count G C hao hnoEdge (opnd C h 1) (hno_op 1) W hW1
        (fun g hg _ => side_lam_bound G hnf C hStars w W hW_edge g hg)
      have hrc := Finset.card_le_card (hR_sub 1 W)
      omega
  by_cases hS0 : S0.card ≤ 1
  · have hS0_eq : S0.card = 1 := by
      have := Finset.card_pos.mpr hne_sides.1; omega
    obtain ⟨w0, hw0⟩ := Finset.card_eq_one.mp hS0_eq
    have hw0S1 : w0 ∉ S1 := Finset.disjoint_left.mp hdisj_S (by show w0 ∈ S0; rw [hw0]; simp)
    refine ⟨{w0}, by simp, fun u v huv => ?_, ?_⟩
    · obtain ⟨_, _, _, _, _, hval⟩ := hUh_wit u v huv
      have hev := (junk_eval_eq hao hh_lt hh_and hno_h (pairInput u v)).mp hval
      obtain ⟨x, hx, hxpi⟩ := hev.1
      change x ∈ S0 at hx
      have hxw0 : x = w0 := by rw [hw0] at hx; exact Finset.mem_singleton.mp hx
      subst hxw0
      rcases (pairInput_true u v x).mp hxpi with rfl | rfl <;> simp
    · let W1 := S1.filter fun v => s(w0, v) ∈ Uh
      refine hstar_side w0 W1 (Or.inr (Finset.filter_subset _ _)) (fun e he => ?_) (fun v hv => ?_)
      · induction e using Sym2.ind with
        | _ u v =>
          obtain ⟨_, _, _, _, _, hval⟩ := hUh_wit u v he
          have hev := (junk_eval_eq hao hh_lt hh_and hno_h (pairInput u v)).mp hval
          obtain ⟨x, hx, hxpi⟩ := hev.1
          change x ∈ S0 at hx
          have hxw0 : x = w0 := by rw [hw0] at hx; exact Finset.mem_singleton.mp hx
          subst hxw0
          obtain ⟨y, hy, hypi⟩ := hev.2
          have hy_ne : y ≠ x := fun h => hw0S1 (h ▸ hy)
          rcases (pairInput_true u v x).mp hxpi with hxu | hxv <;>
            rcases (pairInput_true u v y).mp hypi with hyu | hyv
          · exact absurd (hyu.trans hxu.symm) hy_ne
          · rw [← hxu, ← hyv] at he ⊢; exact ⟨y, Finset.mem_filter.mpr ⟨hy, he⟩, rfl⟩
          · rw [← hxv, ← hyu] at he ⊢; exact ⟨y, Finset.mem_filter.mpr ⟨hy, by rw [Sym2.eq_swap]; exact he⟩, Sym2.eq_swap⟩
          · exact absurd (hyv.trans hxv.symm) hy_ne
      · simp only [W1, Finset.mem_filter] at hv
        have hU := hUh_sub hv.2
        exact ⟨SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1, hU⟩
  · by_cases hS1 : S1.card ≤ 1
    · have hS1_eq : S1.card = 1 := by
        have := Finset.card_pos.mpr hne_sides.2; omega
      obtain ⟨w1, hw1⟩ := Finset.card_eq_one.mp hS1_eq
      have hw1S0 : w1 ∉ S0 := Finset.disjoint_right.mp hdisj_S (by show w1 ∈ S1; rw [hw1]; simp)
      refine ⟨{w1}, by simp, fun u v huv => ?_, ?_⟩
      · obtain ⟨_, _, _, _, _, hval⟩ := hUh_wit u v huv
        have hev := (junk_eval_eq hao hh_lt hh_and hno_h (pairInput u v)).mp hval
        obtain ⟨y, hy, hypi⟩ := hev.2
        change y ∈ S1 at hy
        have hyw1 : y = w1 := by rw [hw1] at hy; exact Finset.mem_singleton.mp hy
        subst hyw1
        rcases (pairInput_true u v y).mp hypi with rfl | rfl <;> simp
      · let W0 := S0.filter fun u => s(w1, u) ∈ Uh
        refine hstar_side w1 W0 (Or.inl (Finset.filter_subset _ _)) (fun e he => ?_) (fun u hu => ?_)
        · induction e using Sym2.ind with
          | _ u v =>
            obtain ⟨_, _, _, _, _, hval⟩ := hUh_wit u v he
            have hev := (junk_eval_eq hao hh_lt hh_and hno_h (pairInput u v)).mp hval
            obtain ⟨y, hy, hypi⟩ := hev.2
            change y ∈ S1 at hy
            have hyw1 : y = w1 := by rw [hw1] at hy; exact Finset.mem_singleton.mp hy
            subst hyw1
            obtain ⟨x, hx, hxpi⟩ := hev.1
            have hx_ne : x ≠ y := fun h => hw1S0 (h ▸ hx)
            rcases (pairInput_true u v x).mp hxpi with hxu | hxv <;>
              rcases (pairInput_true u v y).mp hypi with hyu | hyv
            · exact absurd (hxu.trans hyu.symm) hx_ne
            · rw [← hxu, ← hyv] at he ⊢; exact ⟨x, Finset.mem_filter.mpr ⟨hx, by rw [Sym2.eq_swap]; exact he⟩, Sym2.eq_swap⟩
            · rw [← hxv, ← hyu] at he ⊢; exact ⟨x, Finset.mem_filter.mpr ⟨hx, he⟩, rfl⟩
            · exact absurd (hxv.trans hyv.symm) hx_ne
        · simp only [W0, Finset.mem_filter] at hu
          have hU := hUh_sub hu.2
          exact ⟨SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1, hU⟩
    · have hS0_2 : 2 ≤ S0.card := by omega
      have hS1_2 : 2 ≤ S1.card := by omega
      let X0 := S0.filter fun w => ∀ z ∈ S1, z ≠ w ∧ G.Adj w z
      let X1 := S1.filter fun w' => ∀ z ∈ S0, z ≠ w' ∧ G.Adj w' z
      have hX0_le : X0.card ≤ 1 := by
        by_contra hgt
        have : 2 ≤ X0.card := by omega
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < X0.card)
        simp only [X0, Finset.mem_filter] at ha hb
        have hle := noFourCycle_common_le_one G hnf hab S1 (fun z hz => ⟨(ha.2 z hz).2, (hb.2 z hz).2⟩)
        omega
      have hX1_le : X1.card ≤ 1 := by
        by_contra hgt
        have : 2 ≤ X1.card := by omega
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < X1.card)
        simp only [X1, Finset.mem_filter] at ha hb
        have hle := noFourCycle_common_le_one G hnf hab S0 (fun z hz => ⟨(ha.2 z hz).2, (hb.2 z hz).2⟩)
        omega
      have hcov : ∀ u v : Fin 11, s(u, v) ∈ Uh → u ∈ X0 ∪ X1 ∨ v ∈ X0 ∪ X1 := by
        intro u v huv
        obtain ⟨a, ha, b, hva, hor, hvh⟩ := hUh_wit u v huv
        obtain ⟨w, _, hw_uv, hadj_w⟩ := junk_other_side_adj G C hao htop hj h45 h54 hh_eq hdisj_top ha b hor u v hva
        have hev := (junk_eval_eq hao hh_lt hh_and hno_h (pairInput u v)).mp hvh
        obtain ⟨x, hx, hxpi⟩ := hev.1
        obtain ⟨y, hy, hypi⟩ := hev.2
        have hwS : w ∈ S0 ∨ w ∈ S1 := by
          by_contra hnot
          push Not at hnot
          rcases hw_uv with hwu | hwv
          · have hxu : x ≠ u := fun h => hnot.1 (hwu ▸ h ▸ hx)
            have hyu : y ≠ u := fun h => hnot.2 (hwu ▸ h ▸ hy)
            have hxv : x = v := ((pairInput_true u v x).mp hxpi).resolve_left hxu
            have hyv : y = v := ((pairInput_true u v y).mp hypi).resolve_left hyu
            exact Finset.disjoint_left.mp hdisj_S (hxv ▸ hx) (hyv ▸ hy)
          · have hxv : x ≠ v := fun h => hnot.1 (hwv ▸ h ▸ hx)
            have hyv : y ≠ v := fun h => hnot.2 (hwv ▸ h ▸ hy)
            have hxu : x = u := ((pairInput_true u v x).mp hxpi).resolve_right hxv
            have hyu : y = u := ((pairInput_true u v y).mp hypi).resolve_right hyv
            exact Finset.disjoint_left.mp hdisj_S (hxu ▸ hx) (hyu ▸ hy)
        have hw_mem : w ∈ X0 ∪ X1 := by
          rcases hwS with hw0 | hw1
          · apply Finset.mem_union_left
            refine Finset.mem_filter.mpr ⟨hw0, fun z hz => hadj_w z ?_⟩
            rw [junk_eval_eq hao hh_lt hh_and hno_h]
            exact ⟨⟨w, hw0, pairInput_left w z⟩, ⟨z, hz, pairInput_right w z⟩⟩
          · apply Finset.mem_union_right
            refine Finset.mem_filter.mpr ⟨hw1, fun z hz => hadj_w z ?_⟩
            rw [junk_eval_eq hao hh_lt hh_and hno_h]
            exact ⟨⟨z, hz, pairInput_right w z⟩, ⟨w, hw1, pairInput_left w z⟩⟩
        rcases hw_uv with hwu | hwv
        · exact Or.inl (hwu ▸ hw_mem)
        · exact Or.inr (hwv ▸ hw_mem)
      refine ⟨X0 ∪ X1, (Finset.card_union_le X0 X1).trans (by omega), hcov, ?_⟩
      by_cases hX0_ne : X0 = ∅
      · by_cases hX1_ne : X1 = ∅
        · have hUh_empty : Uh = ∅ := by
            ext e
            simp only [Finset.notMem_empty, iff_false]
            intro he
            induction e using Sym2.ind with
            | _ u v =>
              rcases hcov u v he with h1 | h2 <;> simp [hX0_ne, hX1_ne] at *
          rw [hUh_empty]; simp
        · obtain ⟨w', hw'⟩ := Finset.nonempty_iff_ne_empty.mpr hX1_ne
          have hX1_eq : X1 = {w'} := Finset.eq_singleton_iff_unique_mem.mpr
            ⟨hw', fun y hy => by
              by_contra hne
              have : 2 ≤ X1.card := Finset.one_lt_card.mpr ⟨y, hy, w', hw', hne⟩
              omega⟩
          let W0 := S0.filter fun u => s(w', u) ∈ Uh
          refine hstar_side w' W0 (Or.inl (Finset.filter_subset _ _)) (fun e he => ?_) (fun u hu => ?_)
          · induction e using Sym2.ind with
            | _ u v =>
              have hcov' := hcov u v he
              simp only [hX0_ne, hX1_eq, Finset.empty_union, Finset.mem_singleton] at hcov'
              obtain ⟨_, _, _, _, _, hval⟩ := hUh_wit u v he
              have hev := (junk_eval_eq hao hh_lt hh_and hno_h (pairInput u v)).mp hval
              obtain ⟨x, hx, hxpi⟩ := hev.1
              have hxpi' := (pairInput_true u v x).mp hxpi
              have hadj_edge := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hUh_sub he)).1
              have huv_ne := G.ne_of_adj hadj_edge
              rcases hcov' with hwu | hvu
              · rcases (pairInput_true u v x).mp hxpi with hxu | hxv
                · exfalso; exact ((Finset.mem_filter.mp hw').2 x hx).1 (hxu.trans hwu)
                · exact ⟨x, Finset.mem_filter.mpr ⟨hx, by rw [← hwu, hxv]; exact he⟩, by rw [hwu, ← hxv]⟩
              · rcases (pairInput_true u v x).mp hxpi with hxu | hxv
                · exact ⟨x, Finset.mem_filter.mpr ⟨hx, by rw [← hvu, hxu, Sym2.eq_swap]; exact he⟩, by rw [hvu, ← hxu, Sym2.eq_swap]⟩
                · exfalso; exact ((Finset.mem_filter.mp hw').2 x hx).1 (hxv.trans hvu)
          · simp only [W0, Finset.mem_filter] at hu
            have hU := hUh_sub hu.2
            exact ⟨SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1, hU⟩
      · by_cases hX1_ne : X1 = ∅
        · obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hX0_ne
          have hX0_eq : X0 = {w} := Finset.eq_singleton_iff_unique_mem.mpr
            ⟨hw, fun y hy => by
              by_contra hne
              have : 2 ≤ X0.card := Finset.one_lt_card.mpr ⟨y, hy, w, hw, hne⟩
              omega⟩
          let W1 := S1.filter fun v => s(w, v) ∈ Uh
          refine hstar_side w W1 (Or.inr (Finset.filter_subset _ _)) (fun e he => ?_) (fun v hv => ?_)
          · induction e using Sym2.ind with
            | _ u v =>
              have hcov' := hcov u v he
              simp only [hX1_ne, hX0_eq, Finset.union_empty, Finset.mem_singleton] at hcov'
              obtain ⟨_, _, _, _, _, hval⟩ := hUh_wit u v he
              have hev := (junk_eval_eq hao hh_lt hh_and hno_h (pairInput u v)).mp hval
              obtain ⟨y, hy, hypi⟩ := hev.2
              have hypi' := (pairInput_true u v y).mp hypi
              have hadj_edge := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hUh_sub he)).1
              have huv_ne := G.ne_of_adj hadj_edge
              rcases hcov' with hwu | hvu
              · rcases (pairInput_true u v y).mp hypi with hyu | hyv
                · exfalso; exact ((Finset.mem_filter.mp hw).2 y hy).1 (hyu.trans hwu)
                · exact ⟨y, Finset.mem_filter.mpr ⟨hy, by rw [← hwu, hyv]; exact he⟩, by rw [hwu, ← hyv]⟩
              · rcases (pairInput_true u v y).mp hypi with hyu | hyv
                · exact ⟨y, Finset.mem_filter.mpr ⟨hy, by rw [← hvu, hyu, Sym2.eq_swap]; exact he⟩, by rw [hvu, ← hyu, Sym2.eq_swap]⟩
                · exfalso; exact ((Finset.mem_filter.mp hw).2 y hy).1 (hyv.trans hvu)
          · simp only [W1, Finset.mem_filter] at hv
            have hU := hUh_sub hv.2
            exact ⟨SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1, hU⟩
        · obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hX0_ne
          obtain ⟨w', hw'⟩ := Finset.nonempty_iff_ne_empty.mpr hX1_ne
          have hX0_eq : X0 = {w} := Finset.eq_singleton_iff_unique_mem.mpr
            ⟨hw, fun y hy => by
              by_contra hne
              have : 2 ≤ X0.card := Finset.one_lt_card.mpr ⟨y, hy, w, hw, hne⟩
              omega⟩
          have hX1_eq : X1 = {w'} := Finset.eq_singleton_iff_unique_mem.mpr
            ⟨hw', fun y hy => by
              by_contra hne
              have : 2 ≤ X1.card := Finset.one_lt_card.mpr ⟨y, hy, w', hw', hne⟩
              omega⟩
          have hw_S0 : w ∈ S0 := (Finset.mem_filter.mp hw).1
          have hw'_S1 : w' ∈ S1 := (Finset.mem_filter.mp hw').1
          have hww'_ne : w' ≠ w ∧ G.Adj w w' := (Finset.mem_filter.mp hw).2 w' hw'_S1
          let W1 := S1.filter fun v => s(w, v) ∈ Uh
          let W0 := S0.filter fun u => s(w', u) ∈ Uh
          have hW1_edge : ∀ v ∈ W1, G.Adj w v ∧ s(w, v) ∈ Ustar G C := by
            intro v hv
            simp only [W1, Finset.mem_filter] at hv
            have hU := hUh_sub hv.2
            exact ⟨SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1, hU⟩
          have hW0_edge : ∀ u ∈ W0, G.Adj w' u ∧ s(w', u) ∈ Ustar G C := by
            intro u hu
            simp only [W0, Finset.mem_filter] at hu
            have hU := hUh_sub hu.2
            exact ⟨SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1, hU⟩
          have hUh_sub_img : Uh ⊆ W1.image (fun v => s(w, v)) ∪ W0.image (fun u => s(w', u)) := by
            intro e he
            induction e using Sym2.ind with
            | _ u v =>
              have hcov' := hcov u v he
              simp only [hX0_eq, hX1_eq, Finset.mem_union, Finset.mem_singleton] at hcov'
              obtain ⟨_, _, _, _, _, hval⟩ := hUh_wit u v he
              have hev := (junk_eval_eq hao hh_lt hh_and hno_h (pairInput u v)).mp hval
              rcases hcov' with (rfl | rfl) | (rfl | rfl)
              · obtain ⟨y, hy, hypi⟩ := hev.2
                rcases (pairInput_true u v y).mp hypi with rfl | rfl
                · exfalso; exact ((Finset.mem_filter.mp hw).2 y hy).1 rfl
                · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hy, he⟩))
              · obtain ⟨x, hx, hxpi⟩ := hev.1
                rcases (pairInput_true u v x).mp hxpi with rfl | rfl
                · exfalso; exact ((Finset.mem_filter.mp hw').2 x hx).1 rfl
                · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx, he⟩))
              · obtain ⟨y, hy, hypi⟩ := hev.2
                rcases (pairInput_true u v y).mp hypi with rfl | rfl
                · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, by rw [Sym2.eq_swap]; exact he⟩, Sym2.eq_swap⟩)
                · exfalso; exact ((Finset.mem_filter.mp hw).2 y hy).1 rfl
              · obtain ⟨x, hx, hxpi⟩ := hev.1
                rcases (pairInput_true u v x).mp hxpi with rfl | rfl
                · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, by rw [Sym2.eq_swap]; exact he⟩, Sym2.eq_swap⟩)
                · exfalso; exact ((Finset.mem_filter.mp hw').2 x hx).1 rfl
          by_cases hww'U : s(w, w') ∈ Uh
          · have hUh_card_le : Uh.card + 1 ≤ W1.card + W0.card := by
              have hmem1 : s(w, w') ∈ W1.image (fun v => s(w, v)) :=
                Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw'_S1, hww'U⟩)
              have hmem0 : s(w, w') ∈ W0.image (fun u => s(w', u)) :=
                Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hw_S0, by rw [Sym2.eq_swap]; exact hww'U⟩, Sym2.eq_swap⟩
              have hinter : (W1.image (fun v => s(w, v)) ∩ W0.image (fun u => s(w', u))).Nonempty :=
                ⟨s(w, w'), Finset.mem_inter.mpr ⟨hmem1, hmem0⟩⟩
              have h1 := Finset.card_le_card hUh_sub_img
              have h2 := Finset.card_union_add_card_inter (W1.image (fun v => s(w, v))) (W0.image (fun u => s(w', u)))
              have h3 : 1 ≤ (W1.image (fun v => s(w, v)) ∩ W0.image (fun u => s(w', u))).card :=
                Finset.card_pos.mpr hinter
              have h4 : (W1.image (fun v => s(w, v))).card ≤ W1.card := Finset.card_image_le
              have h5 : (W0.image (fun u => s(w', u))).card ≤ W0.card := Finset.card_image_le
              omega
            have htree0 := or_tree_R_count G C hao hnoEdge (opnd C h 0) (hno_op 0) W0 (Finset.filter_subset _ _)
              (fun g hg _ => side_lam_bound G hnf C hStars w' W0 hW0_edge g hg)
            have htree1 := or_tree_R_count G C hao hnoEdge (opnd C h 1) (hno_op 1) W1 (Finset.filter_subset _ _)
              (fun g hg _ => side_lam_bound G hnf C hStars w W1 hW1_edge g hg)
            let R0 := (orN G C \ lam G C).filter fun g =>
              OrReaches 11 C (opnd C h 0) g ∧ 2 ≤ (orIn 11 C (11 + g) ∩ W0).card
            let R1 := (orN G C \ lam G C).filter fun g =>
              OrReaches 11 C (opnd C h 1) g ∧ 2 ≤ (orIn 11 C (11 + g) ∩ W1).card
            have hdisj_01 : Disjoint R0 R1 := by
              rw [Finset.disjoint_left]
              intro g hg0 hg1
              simp only [R0, R1, Finset.mem_filter] at hg0 hg1
              have hsub0 : orIn 11 C (11 + g) ⊆ S0 := fun z hz =>
                reach_mem_orIn z ((orReaches_reach g _ hg0.2.1).1.trans (mem_orIn_reach z hz))
              have hsub1 : orIn 11 C (11 + g) ⊆ S1 := fun z hz =>
                reach_mem_orIn z ((orReaches_reach g _ hg1.2.1).1.trans (mem_orIn_reach z hz))
              have hcommon : (orIn 11 C (11 + g)).card ≤ 1 :=
                noFourCycle_common_le_one G hnf hww'_ne.1.symm _ (fun z hz =>
                  ⟨(Finset.mem_filter.mp hw).2 z (hsub1 hz) |>.2, (Finset.mem_filter.mp hw').2 z (hsub0 hz) |>.2⟩)
              have hle0 : (orIn 11 C (11 + g) ∩ W0).card ≤ (orIn 11 C (11 + g)).card :=
                Finset.card_le_card Finset.inter_subset_left
              omega
            have hR_union : (R0 ∪ R1).card ≤ Rcone.card :=
              Finset.card_le_card (Finset.union_subset (hR_sub 0 W0) (hR_sub 1 W1))
            rw [Finset.card_union_of_disjoint hdisj_01] at hR_union
            change W0.card ≤ 1 + R0.card at htree0
            change W1.card ≤ 1 + R1.card at htree1
            change Uh.card ≤ 1 + Rcone.card
            omega
          · by_cases hW0_e : W0 = ∅
            · have hUh_le : Uh.card ≤ W1.card := by
                have hsub : Uh ⊆ W1.image (fun v => s(w, v)) := by
                  intro e he
                  have hm := hUh_sub_img he
                  simpa [hW0_e] using hm
                exact (Finset.card_le_card hsub).trans Finset.card_image_le
              have htree1 := or_tree_R_count G C hao hnoEdge (opnd C h 1) (hno_op 1) W1 (Finset.filter_subset _ _)
                (fun g hg _ => side_lam_bound G hnf C hStars w W1 hW1_edge g hg)
              have hrc := Finset.card_le_card (hR_sub 1 W1)
              change Uh.card ≤ 1 + Rcone.card
              omega
            · by_cases hW1_e : W1 = ∅
              · have hUh_le : Uh.card ≤ W0.card := by
                  have hsub : Uh ⊆ W0.image (fun u => s(w', u)) := by
                    intro e he
                    have hm := hUh_sub_img he
                    simpa [hW1_e] using hm
                  exact (Finset.card_le_card hsub).trans Finset.card_image_le
                have htree0 := or_tree_R_count G C hao hnoEdge (opnd C h 0) (hno_op 0) W0 (Finset.filter_subset _ _)
                  (fun g hg _ => side_lam_bound G hnf C hStars w' W0 hW0_edge g hg)
                have hrc := Finset.card_le_card (hR_sub 0 W0)
                change Uh.card ≤ 1 + Rcone.card
                omega
              · obtain ⟨u0, hu0⟩ := Finset.nonempty_iff_ne_empty.mpr hW0_e
                obtain ⟨v0, hv0⟩ := Finset.nonempty_iff_ne_empty.mpr hW1_e
                let W0' := insert w W0
                let W1' := insert w' W1
                have hw_not_W0 : w ∉ W0 := fun hmem => hww'U (by rw [Sym2.eq_swap]; exact (Finset.mem_filter.mp hmem).2)
                have hw'_not_W1 : w' ∉ W1 := fun hmem => hww'U (Finset.mem_filter.mp hmem).2
                have hW0'_sub : W0' ⊆ S0 := Finset.insert_subset_iff.mpr ⟨hw_S0, Finset.filter_subset _ _⟩
                have hW1'_sub : W1' ⊆ S1 := Finset.insert_subset_iff.mpr ⟨hw'_S1, Finset.filter_subset _ _⟩
                have hlam0' : ∀ g ∈ lam G C, OrReaches 11 C (opnd C h 0) g → (orIn 11 C (11 + g) ∩ W0').card ≤ 1 := by
                  intro g hg _
                  obtain ⟨c, hc⟩ := orIn_lam_not_Ustar G C hStars hg
                  by_cases hcw' : c = w'
                  · subst hcw'
                    have hsub_s : orIn 11 C (11 + g) ∩ W0' ⊆ {w} := by
                      intro z hz
                      simp only [Finset.mem_inter, W0', Finset.mem_insert, Finset.mem_singleton] at hz ⊢
                      rcases hz.2 with rfl | hz0
                      · rfl
                      · exact absurd (hW0_edge z hz0).2 (hc z hz.1).2
                    exact (Finset.card_le_card hsub_s).trans (by simp)
                  · refine noFourCycle_common_le_one G hnf (Ne.symm hcw') _ (fun z hz => ?_)
                    simp only [Finset.mem_inter, W0', Finset.mem_insert] at hz
                    refine ⟨?_, (hc z hz.1).1⟩
                    rcases hz.2 with rfl | hz0
                    · exact hww'_ne.2.symm
                    · exact (hW0_edge z hz0).1
                have hlam1' : ∀ g ∈ lam G C, OrReaches 11 C (opnd C h 1) g → (orIn 11 C (11 + g) ∩ W1').card ≤ 1 := by
                  intro g hg _
                  obtain ⟨c, hc⟩ := orIn_lam_not_Ustar G C hStars hg
                  by_cases hcw : c = w
                  · subst hcw
                    have hsub_s : orIn 11 C (11 + g) ∩ W1' ⊆ {w'} := by
                      intro z hz
                      simp only [Finset.mem_inter, W1', Finset.mem_insert, Finset.mem_singleton] at hz ⊢
                      rcases hz.2 with rfl | hz1
                      · rfl
                      · exact absurd (hW1_edge z hz1).2 (hc z hz.1).2
                    exact (Finset.card_le_card hsub_s).trans (by simp)
                  · refine noFourCycle_common_le_one G hnf (Ne.symm hcw) _ (fun z hz => ?_)
                    simp only [Finset.mem_inter, W1', Finset.mem_insert] at hz
                    refine ⟨?_, (hc z hz.1).1⟩
                    rcases hz.2 with rfl | hz1
                    · exact hww'_ne.2
                    · exact (hW1_edge z hz1).1
                have htree0 := or_tree_R_count G C hao hnoEdge (opnd C h 0) (hno_op 0) W0' hW0'_sub hlam0'
                have htree1 := or_tree_R_count G C hao hnoEdge (opnd C h 1) (hno_op 1) W1' hW1'_sub hlam1'
                let R0 := (orN G C \ lam G C).filter fun g =>
                  OrReaches 11 C (opnd C h 0) g ∧ 2 ≤ (orIn 11 C (11 + g) ∩ W0').card
                let R1 := (orN G C \ lam G C).filter fun g =>
                  OrReaches 11 C (opnd C h 1) g ∧ 2 ≤ (orIn 11 C (11 + g) ∩ W1').card
                have hdisj_01 : Disjoint R0 R1 := by
                  rw [Finset.disjoint_left]
                  intro g hg0 hg1
                  simp only [R0, R1, Finset.mem_filter] at hg0 hg1
                  have hsub0 : orIn 11 C (11 + g) ⊆ S0 := fun z hz =>
                    reach_mem_orIn z ((orReaches_reach g _ hg0.2.1).1.trans (mem_orIn_reach z hz))
                  have hsub1 : orIn 11 C (11 + g) ⊆ S1 := fun z hz =>
                    reach_mem_orIn z ((orReaches_reach g _ hg1.2.1).1.trans (mem_orIn_reach z hz))
                  have hcommon : (orIn 11 C (11 + g)).card ≤ 1 :=
                    noFourCycle_common_le_one G hnf hww'_ne.1.symm _ (fun z hz =>
                      ⟨(Finset.mem_filter.mp hw).2 z (hsub1 hz) |>.2, (Finset.mem_filter.mp hw').2 z (hsub0 hz) |>.2⟩)
                  have hle0 : (orIn 11 C (11 + g) ∩ W0').card ≤ (orIn 11 C (11 + g)).card :=
                    Finset.card_le_card Finset.inter_subset_left
                  omega
                have hR_union : (R0 ∪ R1).card ≤ Rcone.card :=
                  Finset.card_le_card (Finset.union_subset (hR_sub 0 W0') (hR_sub 1 W1'))
                rw [Finset.card_union_of_disjoint hdisj_01] at hR_union
                have hUh_card_le : Uh.card ≤ W1.card + W0.card :=
                  (Finset.card_le_card hUh_sub_img).trans ((Finset.card_union_le _ _).trans
                    (Nat.add_le_add Finset.card_image_le Finset.card_image_le))
                have hc0 : W0'.card = W0.card + 1 := Finset.card_insert_of_notMem hw_not_W0
                have hc1 : W1'.card = W1.card + 1 := Finset.card_insert_of_notMem hw'_not_W1
                change W0'.card ≤ 1 + R0.card at htree0
                change W1'.card ≤ 1 + R1.card at htree1
                change Uh.card ≤ 1 + Rcone.card
                omega




theorem PEqualNP.Outside.R_meta_2264_1 :
    (∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [DecidableRel x1.Adj]
        (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
      x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →
      PEqualNP.TopForm.IsLeastAO x1 x3 →
      PEqualNP.TopForm.TopForm x1 x3 →
      x3.size ≤ (21 : ℕ) →
      x4 < x5 →
      PEqualNP.TopForm.junk x1 x3 = {x4, x5} →
      ¬ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →
      ¬ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x5 x4 →
      ∀ h : ℕ, h = x4 ∨ h = x5 →
      ¬ ∃ z : Fin (11 : ℕ), PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 h (PEqualNP.EdgeOwnership.pairInput z z) = Bool.true) →
    (∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [DecidableRel x1.Adj]
        (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
      x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →
      PEqualNP.TopForm.IsLeastAO x1 x3 →
      PEqualNP.TopForm.TopForm x1 x3 →
      x3.size ≤ (21 : ℕ) →
      (∀ x13 ∈ PEqualNP.TopForm.tops x1 x3,
        have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;
        (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧
        ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →
      (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ PEqualNP.TopForm.Ustar x1 x3 →
        ∃ x17 ∈ PEqualNP.TopForm.tops x1 x3, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ),
          (x19 = x4 ∨ x19 = x5) ∧
          PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧
          PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧
          PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) →
      (17 : ℕ) + (PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + (PEqualNP.TopForm.Ustar x1 x3).card →
      (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑(PEqualNP.TopForm.Ustar x1 x3)) x16 → x16.card ≤ (PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card) →
      x4 < x5 →
      PEqualNP.TopForm.junk x1 x3 = {x4, x5} →
      ¬ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →
      ¬ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x5 x4 →
      (∀ x21 ∈ PEqualNP.TopForm.tops x1 x3, PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x21 → ¬ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x5 x21) →
      (∃ u1 v1 : Fin (11 : ℕ), s(u1, v1) ∈ PEqualNP.TopForm.Ustar x1 x3 ∧
        ∃ a ∈ PEqualNP.TopForm.tops x1 x3, ∃ b : Fin (2 : ℕ),
          PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 a (PEqualNP.EdgeOwnership.pairInput u1 v1) = Bool.true ∧
          PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 a b) x4 ∧
          PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x4 (PEqualNP.EdgeOwnership.pairInput u1 v1) = Bool.true) →
      (∃ u2 v2 : Fin (11 : ℕ), s(u2, v2) ∈ PEqualNP.TopForm.Ustar x1 x3 ∧
        ¬ (∃ a ∈ PEqualNP.TopForm.tops x1 x3, ∃ b : Fin (2 : ℕ),
          PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 a (PEqualNP.EdgeOwnership.pairInput u2 v2) = Bool.true ∧
          PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 a b) x4 ∧
          PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x4 (PEqualNP.EdgeOwnership.pairInput u2 v2) = Bool.true)) →
      False) →
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∀ x21 ∈ x9, x12 x4 x21 → ¬x12 x5 x21) → (22 : ℕ) ≤ x3.size := by
  intro hNoDiag hTwoJunk G _ C x4 x5 hG hLeast hTop
  dsimp only
  intro hStars hOff hCount hCoverBound hlt hj h45 h54 hdisj_top
  have hnf : NoFourCycle G := by
    intro a b hab
    have h1 := noFourCycle_G11 a b hab
    simpa [hG] using h1
  have htau : ∀ K : Finset (Fin 11), G.IsVertexCover (↑K : Set (Fin 11)) → 7 ≤ K.card := by
    intro K hK; rw [hG] at hK; exact tau_G11 K hK
  by_contra hShort
  have hSize : C.size ≤ 21 := by omega
  have hao : IsAO2 11 C := hLeast.1
  let T := tops G C
  let V := centreless G C
  let U := Ustar G C
  let R := orN G C \ lam G C
  change 17 + (T \ V).card + 2 * V.card + R.card ≤ C.size + U.card at hCount
  have hBudget : (T \ V).card + 2 * V.card + R.card ≤ 4 + U.card := by omega
  classical
  let H := G.deleteEdges (↑U : Set (Sym2 (Fin 11)))
  let P (m : ℕ) := ∃ K : Finset (Fin 11), H.IsVertexCover (↑K : Set (Fin 11)) ∧ K.card = m
  have hex : ∃ m, P m := ⟨11, Finset.univ, by simp [SimpleGraph.IsVertexCover], by simp⟩
  obtain ⟨K, hKcov, hKcard⟩ := Nat.find_spec hex
  have hKMin : IsMinCover H K := ⟨hKcov, fun A hA => by rw [hKcard]; exact Nat.find_min' hex ⟨A, hA, rfl⟩⟩
  have hKT : K.card ≤ (T \ V).card := hCoverBound K hKMin
  have hcover_lift : ∀ X : Finset (Fin 11),
      (∀ u v : Fin 11, s(u, v) ∈ U → u ∈ X ∨ v ∈ X) → 7 ≤ K.card + X.card := by
    intro X hX
    have hfull : G.IsVertexCover (↑(K ∪ X) : Set (Fin 11)) := by
      intro u v hadj
      by_cases hU : s(u, v) ∈ U
      · exact (hX u v hU).imp (Finset.mem_union_right _) (Finset.mem_union_right _)
      · have he : H.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hU⟩
        exact (hKMin.1 he).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
    exact (htau (K ∪ X) hfull).trans (Finset.card_union_le K X)
  by_cases hU_empty : U = ∅
  · have h7 := hcover_lift ∅ (by simp [hU_empty])
    simp [hU_empty] at h7 hBudget
    omega
  · let U4 := U.filter fun e => ∃ u v : Fin 11, e = s(u, v) ∧
      ∃ a ∈ T, ∃ b : Fin 2, gateVal 11 C a (pairInput u v) = true ∧
        OrReaches 11 C (opnd C a b) x4 ∧ gateVal 11 C x4 (pairInput u v) = true
    let U5 := U \ U4
    have hU_eq : U = U4 ∪ U5 := (Finset.union_sdiff_of_subset (Finset.filter_subset _ _)).symm
    have hU_disj : Disjoint U4 U5 := Finset.disjoint_sdiff
    have hU_card : U.card = U4.card + U5.card := by
      rw [hU_eq, Finset.card_union_of_disjoint hU_disj]
    have hU4_wit : ∀ u v : Fin 11, s(u, v) ∈ U4 → ∃ a ∈ T, ∃ b : Fin 2,
        gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) x4 ∧
        gateVal 11 C x4 (pairInput u v) = true := by
      intro u v huv
      simp only [U4, Finset.mem_filter] at huv
      obtain ⟨_, u', v', heq, a, ha, b, h1, h2, h3⟩ := huv
      rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a, ha, b, h1, h2, h3⟩
      · rw [pairInput_comm] at h1 h3
        exact ⟨a, ha, b, h1, h2, h3⟩
    have hU5_wit : ∀ u v : Fin 11, s(u, v) ∈ U5 → ∃ a ∈ T, ∃ b : Fin 2,
        gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) x5 ∧
        gateVal 11 C x5 (pairInput u v) = true := by
      intro u v huv
      simp only [U5, U4, Finset.mem_sdiff, Finset.mem_filter] at huv
      obtain ⟨hU, hnot⟩ := huv
      obtain ⟨a, ha, b, h, hh, h1, h2, h3⟩ := hOff u v hU
      rcases hh with rfl | rfl
      · exfalso; exact hnot ⟨hU, u, v, rfl, a, ha, b, h1, h2, h3⟩
      · exact ⟨a, ha, b, h1, h2, h3⟩
    have hTrace_cost (h : ℕ) (hh : h = x4 ∨ h = x5) (Uh : Finset (Sym2 (Fin 11)))
        (hUh_wit : ∀ u v : Fin 11, s(u, v) ∈ Uh → ∃ a ∈ T, ∃ b : Fin 2,
          gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) h ∧
          gateVal 11 C h (pairInput u v) = true)
        (hUh_ne : Uh.Nonempty) :
        1 ≤ 2 * (V.filter fun a => InCone 11 C h a).card +
          (R.filter fun m => h < m ∧ (∃ a ∈ T, ∃ b : Fin 2, OrReaches 11 C (opnd C a b) m) ∧
            OrReaches 11 C (11 + m) h).card := by
      obtain ⟨e0, he0⟩ := hUh_ne
      induction e0 using Sym2.ind with
      | _ u v =>
        obtain ⟨a, ha, b, _, hor, _⟩ := hUh_wit u v he0
        have hh_mem : h ∈ junk G C := by rw [hj]; rcases hh with rfl | rfl <;> simp
        rcases orTrace_R_or_V G C hao ha b hh_mem hor with haV | ⟨m, hmR, hm1, hm2, hmop⟩
        · have ha_lt : a < C.gates.length := by
            simp only [T, tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha; exact ha.1
          have ha_mem : a ∈ V.filter fun a => InCone 11 C h a :=
            Finset.mem_filter.mpr ⟨haV, orReaches_inCone hao ha_lt b hor⟩
          have hpos : 0 < (V.filter fun a => InCone 11 C h a).card := Finset.card_pos.mpr ⟨a, ha_mem⟩
          omega
        · have hm_lt : h < m := by
            rcases hmop with hop | hop
            · have := opnd_lt hao.2.1 (by simp only [orN, gatesWhere, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hmR; exact hmR.1.1) 0 (hao.2.2 _ (gateAt_mem (by simp only [orN, gatesWhere, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hmR; exact hmR.1.1)))
              omega
            · have := opnd_lt hao.2.1 (by simp only [orN, gatesWhere, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hmR; exact hmR.1.1) 1 (hao.2.2 _ (gateAt_mem (by simp only [orN, gatesWhere, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hmR; exact hmR.1.1)))
              omega
          have hm_mem : m ∈ R.filter fun m => h < m ∧ (∃ a ∈ T, ∃ b : Fin 2, OrReaches 11 C (opnd C a b) m) ∧
              OrReaches 11 C (11 + m) h :=
            Finset.mem_filter.mpr ⟨hmR, hm_lt, ⟨a, ha, b, hm1⟩, hm2⟩
          have hpos := Finset.card_pos.mpr ⟨m, hm_mem⟩
          omega
    have hsingle (h : ℕ) (hh : h = x4 ∨ h = x5) (Uh : Finset (Sym2 (Fin 11)))
        (hUh_eq : U = Uh)
        (hUh_wit : ∀ u v : Fin 11, s(u, v) ∈ Uh → ∃ a ∈ T, ∃ b : Fin 2,
          gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) h ∧
          gateVal 11 C h (pairInput u v) = true)
        (hno_diag : ¬ ∃ z : Fin 11, gateVal 11 C h (pairInput z z) = true) : False := by
      have hUh_ne : Uh.Nonempty := by
        rw [← hUh_eq]; exact Finset.nonempty_iff_ne_empty.mpr hU_empty
      have hcov_res := junk_cover_and_R_bound G hnf C hao hTop hStars hj h45 h54 hh hdisj_top Uh
        (hUh_eq ▸ Finset.Subset.rfl) hUh_wit hUh_ne
      rcases hcov_res with ⟨Xh, hXh_card, hXh_cov, hRc_le⟩ | hdiag
      · have h7 := hcover_lift Xh (hUh_eq ▸ hXh_cov)
        have htr := hTrace_cost h hh Uh hUh_wit hUh_ne
        let Rcone := (orN G C \ lam G C).filter fun g =>
          g < h ∧ (OrReaches 11 C (opnd C h 0) g ∨ OrReaches 11 C (opnd C h 1) g)
        let Rh := R.filter fun m => h < m ∧ (∃ a ∈ T, ∃ b : Fin 2, OrReaches 11 C (opnd C a b) m) ∧
          OrReaches 11 C (11 + m) h
        have hdisj_Rc : Disjoint Rcone Rh := by
          rw [Finset.disjoint_left]
          intro g hg1 hg2
          simp only [Rcone, Rh, Finset.mem_filter] at hg1 hg2
          omega
        have hR_sub : (Rcone ∪ Rh) ⊆ R := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        have hR_card : Rcone.card + Rh.card ≤ R.card := by
          rw [← Finset.card_union_of_disjoint hdisj_Rc]
          exact Finset.card_le_card hR_sub
        have hV_le : (V.filter fun a => InCone 11 C h a).card ≤ V.card := Finset.card_le_card (Finset.filter_subset _ _)
        change Uh.card ≤ 1 + Rcone.card at hRc_le
        change 1 ≤ 2 * (V.filter fun a => InCone 11 C h a).card + Rh.card at htr
        rw [hUh_eq] at hBudget
        omega
      · exact hno_diag hdiag
    have hno_diag := hNoDiag G C x4 x5 hG hLeast hTop hSize hlt hj h45 h54
    by_cases hU4_ne : U4.Nonempty
    · by_cases hU5_ne : U5.Nonempty
      · obtain ⟨e4, he4⟩ := hU4_ne
        obtain ⟨e5, he5⟩ := hU5_ne
        induction e4 using Sym2.ind with
        | _ u1 v1 =>
          induction e5 using Sym2.ind with
          | _ u2 v2 =>
            simp only [U4, Finset.mem_filter] at he4
            simp only [U5, U4, Finset.mem_sdiff, Finset.mem_filter] at he5
            obtain ⟨a, ha, b, h1, h2, h3⟩ := hU4_wit u1 v1 (Finset.mem_filter.mpr he4)
            refine hTwoJunk G C x4 x5 hG hLeast hTop hSize hStars hOff hCount hCoverBound hlt hj h45 h54 hdisj_top ?_ ?_
            · exact ⟨u1, v1, he4.1, a, ha, b, h1, h2, h3⟩
            · refine ⟨u2, v2, he5.1, ?_⟩
              rintro ⟨a', ha', b', h1', h2', h3'⟩
              exact he5.2 ⟨he5.1, u2, v2, rfl, a', ha', b', h1', h2', h3'⟩
      · have hU5_empty : U5 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU5_ne
        have hU_eq4 : U = U4 := by rw [hU_eq, hU5_empty, Finset.union_empty]
        exact hsingle x4 (Or.inl rfl) U4 hU_eq4 hU4_wit (hno_diag x4 (Or.inl rfl))
    · have hU4_empty : U4 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU4_ne
      have hU_eq5 : U = U5 := by rw [hU_eq, hU4_empty, Finset.empty_union]
      exact hsingle x5 (Or.inr rfl) U5 hU_eq5 hU5_wit (hno_diag x5 (Or.inr rfl))
