import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_2309_3

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

theorem normalized_eq (g : Gate) (h : FanInTwo ⟨[g], 0⟩) :
    (Gate.mk g.op (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs)) = normGate g := by
  obtain ⟨op, ins⟩ := g
  have hop := (h ⟨op, ins⟩ (by simp)).1
  rcases hop with h1 | h1 | h1
  · simp only at h1; rw [h1]; simp [normGate, GateOp.eval]
  · simp only at h1; rw [h1]; simp [normGate, GateOp.eval]
  · simp only at h1; rw [h1]; simp [normGate, GateOp.eval]

def reads09 (g : Gate) : Bool :=
  [(0 : ℕ), (9 : ℕ)].any fun x => g.inputs.contains x

theorem wiresFrom_eq_of_no_reads09 (gs : List Gate)
    (hno : ∀ g ∈ gs, reads09 g = false) :
    ∀ (w1 w2 : List Bool),
      w1.length = w2.length →
      (∀ i, i < w1.length → i ≠ 0 → i ≠ 9 → w1.getD i false = w2.getD i false) →
      ∀ j, j ≠ 0 → j ≠ 9 →
        (wiresFrom gs w1).getD j false = (wiresFrom gs w2).getD j false := by
  induction gs with
  | nil =>
    intro w1 w2 hlen hw j hj0 hj9
    by_cases hj : j < w1.length
    · exact hw j hj hj0 hj9
    · rw [List.getD_eq_default _ _ (by simp [wiresFrom]; omega),
          List.getD_eq_default _ _ (by simp [wiresFrom]; omega)]
  | cons g gs ih =>
    intro w1 w2 hlen hw j hj0 hj9
    have hg : reads09 g = false := hno g (by simp)
    have hmap : g.inputs.map (fun i => w1.getD i false) =
        g.inputs.map (fun i => w2.getD i false) := by
      apply List.map_congr_left
      intro i hi
      have hne0 : i ≠ 0 := by
        intro h0; subst h0
        simp [reads09, hi] at hg
      have hne9 : i ≠ 9 := by
        intro h9; subst h9
        simp [reads09, hi] at hg
      by_cases hil : i < w1.length
      · exact hw i hil hne0 hne9
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    have hev : g.op.eval (g.inputs.map fun i => w1.getD i false) =
        g.op.eval (g.inputs.map fun i => w2.getD i false) := by rw [hmap]
    have s1 : wiresFrom (g :: gs) w1 = wiresFrom gs (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w2 = wiresFrom gs (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)]) := rfl
    rw [s1, s2]
    apply ih (fun g' hg' => hno g' (by simp [hg']))
    · simp [hlen]
    · intro i hi hi0 hi9
      by_cases hiw : i < w1.length
      · rw [List.getD_append _ _ _ _ hiw, List.getD_append _ _ _ _ (by omega)]
        exact hw i hiw hi0 hi9
      · have hieq : i = w1.length := by simp at hi; omega
        subst hieq
        rw [hev]
        nth_rw 2 [hlen]
        simp
    · exact hj0
    · exact hj9

end PEqualNP.Outside.R_meta_2309_3

open PEqualNP.Outside.R_meta_2309_3 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_2309_3 :
    (∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (p t : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate),
      let x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) =>
        x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) ||
        x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) ||
        x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) ||
        x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) ||
        x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) ||
        x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ));
      FanInTwo x2 →
      (∀ (x7 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = !x7 (0 : Fin (9 : ℕ))) →
      circuitFun (9 : ℕ) x2 = x1 →
      x2.size ≤ (15 : ℕ) →
      (List.drop 1 x2.gates).map normGate = p ++ g :: t →
      reads09 g = true →
      (∀ h ∈ p, reads09 h = false) →
      (∀ h ∈ t, reads09 h = false) →
      x2.output ≠ 0 →
      x2.output ≠ 9 →
      False) →
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   have x3 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => { op := x3.op, inputs := if x3.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x3.inputs else x3.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x2.gates);   have x4 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x5 : ℕ) => x4.inputs.contains x5;   have x5 : ℕ := (List.filter x4 x3).length;   PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = !x7 (0 : Fin (9 : ℕ))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → x2.size ≤ (15 : ℕ) → x5 ≤ (1 : ℕ) → False := by
  intro hOne x1 C
  dsimp only
  intro hC hfirst hfun hsize hle
  have hnorm : List.map (fun g : Gate =>
      (Gate.mk g.op (if g.op.eval [false] = true then g.inputs.take 1 else g.inputs)))
      (C.gates.drop 1) = (C.gates.drop 1).map normGate := by
    apply List.map_congr_left
    intro g hg
    exact normalized_eq g (fun _ hmem => by rw [List.mem_singleton] at hmem; rw [hmem]; exact hC g (List.mem_of_mem_drop hg))
  rw [hnorm] at hle
  have hne : C.gates ≠ [] := by
    intro he
    have h := hfirst (fun _ => false)
    simp [Circuit.wires, he] at h
  obtain ⟨g0, gs, hgs⟩ := List.exists_cons_of_ne_nil hne
  have hout0 : C.output ≠ 0 := by
    intro h0
    have e0 := congrArg (fun f => f (fun _ => false)) hfun
    have e1 := congrArg (fun f => f (fun i => decide (i = 0))) hfun
    have c0 : C.eval (List.ofFn (fun _ : Fin 9 => false)) = false := by
      unfold Circuit.eval; rw [h0, wires_eq, getD_wiresFrom_lt _ _ 0 (by simp)]
      simp
    have c1 : C.eval (List.ofFn (fun i : Fin 9 => decide (i = 0))) = true := by
      unfold Circuit.eval; rw [h0, wires_eq, getD_wiresFrom_lt _ _ 0 (by simp)]
      simp
    simp only [circuitFun, List.ofFn_succ, List.ofFn_zero] at c1 e1
    simp at c1 e1
    rw [c1] at e1; cases e1
  have hout9 : C.output ≠ 9 := by
    intro h9
    have e0 := congrArg (fun f => f (fun _ => false)) hfun
    have c0 : C.eval (List.ofFn (fun _ : Fin 9 => false)) = true := by
      unfold Circuit.eval; rw [h9]
      exact hfirst (fun _ => false)
    simp only [circuitFun, List.ofFn_succ, List.ofFn_zero] at c0 e0
    rw [c0] at e0; cases e0
  let ns := (C.gates.drop 1).map normGate
  have hfilt : (ns.filter reads09).length ≤ 1 := hle
  by_cases hzero : ns.filter reads09 = []
  · have hno : ∀ h ∈ ns, reads09 h = false := by
      intro h hh
      by_contra htrue
      have hmem : h ∈ ns.filter reads09 := List.mem_filter.mpr ⟨hh, by cases h' : reads09 h <;> simp_all⟩
      rw [hzero] at hmem; exact List.not_mem_nil hmem
    let z0 : Fin 9 → Bool := fun i => decide (i = 1)
    let z1 : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
    have ev0 : C.eval (List.ofFn z0) = C.eval (List.ofFn z1) := by
      unfold Circuit.eval
      have hw0 : C.wires (List.ofFn z0) = wiresFrom ns (List.ofFn z0 ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn z0).getD i false)]) := by
        rw [wires_eq, hgs]
        simp only [ns, hgs, List.drop_succ_cons, List.drop_zero, wiresFrom_norm]
        rfl
      have hw1 : C.wires (List.ofFn z1) = wiresFrom ns (List.ofFn z1 ++ [g0.op.eval (g0.inputs.map fun i => (List.ofFn z1).getD i false)]) := by
        rw [wires_eq, hgs]
        simp only [ns, hgs, List.drop_succ_cons, List.drop_zero, wiresFrom_norm]
        rfl
      rw [hw0, hw1]
      apply wiresFrom_eq_of_no_reads09 ns hno _ _ (by simp) _ _ hout0 hout9
      intro i hi hi0 hi9
      by_cases hil : i < 9
      · rw [List.getD_append _ _ _ _ (by simp; exact hil), List.getD_append _ _ _ _ (by simp; exact hil)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [hil, ↓reduceDIte, Option.getD_some, z0, z1]
        have : (⟨i, hil⟩ : Fin 9) ≠ 0 := fun heq => hi0 (congrArg Fin.val heq)
        simp [this]
      · simp at hi; omega
    have f0 := congrArg (fun f => f z0) hfun
    have f1 := congrArg (fun f => f z1) hfun
    simp only [circuitFun] at f0 f1
    rw [ev0, f1] at f0
    simp [x1, z0, z1] at f0
  · obtain ⟨g, hg_mem, hg_eq⟩ : ∃ g ∈ ns, reads09 g = true := by
      obtain ⟨g, gs', hgs'⟩ := List.exists_cons_of_ne_nil hzero
      have hmem : g ∈ ns.filter reads09 := by rw [hgs']; simp
      exact ⟨g, (List.mem_filter.mp hmem).1, (List.mem_filter.mp hmem).2⟩
    obtain ⟨p, t, hsplit⟩ := List.append_of_mem hg_mem
    have hp_no : ∀ h ∈ p, reads09 h = false := by
      intro h hh
      by_contra htrue
      have h2 : (ns.filter reads09).length ≥ 2 := by
        rw [hsplit, List.filter_append, List.filter_cons_of_pos hg_eq, List.length_append, List.length_cons]
        have : 1 ≤ (p.filter reads09).length := List.length_pos_of_ne_nil (by
          intro he
          have : h ∈ p.filter reads09 := List.mem_filter.mpr ⟨hh, by cases h' : reads09 h <;> simp_all⟩
          rw [he] at this; exact List.not_mem_nil this)
        omega
      omega
    have ht_no : ∀ h ∈ t, reads09 h = false := by
      intro h hh
      by_contra htrue
      have h2 : (ns.filter reads09).length ≥ 2 := by
        rw [hsplit, List.filter_append, List.filter_cons_of_pos hg_eq, List.length_append, List.length_cons]
        have : 1 ≤ (t.filter reads09).length := List.length_pos_of_ne_nil (by
          intro he
          have : h ∈ t.filter reads09 := List.mem_filter.mpr ⟨hh, by cases h' : reads09 h <;> simp_all⟩
          rw [he] at this; exact List.not_mem_nil this)
        omega
      omega
    exact hOne C p t g hC hfirst hfun hsize hsplit hg_eq hp_no ht_no hout0 hout9
