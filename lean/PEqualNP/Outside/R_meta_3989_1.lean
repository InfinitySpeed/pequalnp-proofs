import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_3989_1

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

end PEqualNP.Outside.R_meta_3989_1

open PEqualNP.Outside.R_meta_3989_1 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.R_meta_3989_1 :
    (∀ (x2 : Circuit),
      let x1 : (Fin 9 → Bool) → Bool := fun x6 =>
        x6 0 && x6 1 || x6 1 && x6 2 || x6 2 && x6 3 || x6 3 && x6 4 || x6 4 && x6 0 ||
        x6 0 && x6 5 || x6 1 && x6 6 || x6 2 && x6 7 || x6 3 && x6 8 || x6 5 && x6 7 ||
        x6 6 && x6 8 || x6 8 && x6 5;
      let reads : Gate → ℕ → Prop := fun g v =>
        g.op = GateOp.not ∧ g.inputs.head? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs;
      FanInTwo x2 →
      (∃ (x4 x5 : Fin x2.gates.length), x4 < x5 ∧ (x4 : ℕ) = 3 ∧
        (x2.gates.get x4).op = GateOp.not ∧ (x2.gates.get x5).op = GateOp.not ∧
        ∀ x6 : Fin x2.gates.length, (x2.gates.get x6).op = GateOp.not → x6 = x4 ∨ x6 = x5) →
      (∀ x5 : Fin 9 → Bool, (x2.wires (List.ofFn x5)).getD 9 false = (x5 0 || x5 2)) →
      circuitFun 9 x2 = x1 →
      (∀ x7 : ℕ, x7 = 0 ∨ x7 = 2 → ∃ x9 ∈ x2.gates.drop 1, reads x9 x7) →
      5 ≤ x2.size →
      x2.size ≤ 15 →
      10 ≤ x2.output →
      False) →
    have x1 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : ℕ) => x1.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x1.inputs.head? = Option.some x2 ∨ x1.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2 ∈ x1.inputs; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∃ (x4 : Fin x2.gates.length) (x5 : Fin x2.gates.length), x4 < x5 ∧ ↑x4 = (3 : ℕ) ∧ (x2.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x2.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x6 : Fin x2.gates.length), (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not → x6 = x4 ∨ x6 = x5) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) → (∀ (x7 : ℕ), x7 = (0 : ℕ) ∨ x7 = (2 : ℕ) → ∃ x9 ∈ List.drop (1 : ℕ) x2.gates, x1 x9 x7) → (16 : ℕ) ≤ x2.size := by
  intro hRed reads C hC hNots hfirst hfun hreads
  by_contra hlt
  have hsize : C.size ≤ 15 := by omega
  have h5 : 5 ≤ C.size := by
    obtain ⟨x4, x5, h45, h43, _⟩ := hNots
    have hlt5 : (x5 : ℕ) < C.gates.length := x5.isLt
    change C.gates.length ≥ 5
    omega
  have hout10 : 10 ≤ C.output := by
    by_contra hout
    have hout' : C.output ≤ 9 := by omega
    by_cases h9 : C.output = 9
    · have e0 := congrArg (fun f => f (fun i : Fin 9 => decide (i = 0))) hfun
      have c0 : C.eval (List.ofFn (fun i : Fin 9 => decide (i = 0))) = true := by
        unfold Circuit.eval; rw [h9]
        simpa using hfirst (fun i : Fin 9 => decide (i = 0))
      simp only [circuitFun, List.ofFn_succ, List.ofFn_zero] at c0 e0
      simp at c0 e0
      rw [c0] at e0; cases e0
    · have hout9 : C.output < 9 := by omega
      let z : Fin 9 → Bool := fun i => decide ((i : ℕ) = C.output)
      have e0 := congrArg (fun f => f z) hfun
      have c0 : C.eval (List.ofFn z) = true := by
        unfold Circuit.eval
        rw [wires_eq, getD_wiresFrom_lt _ _ C.output (by simp; exact hout9)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp only [hout9, ↓reduceDIte, Option.getD_some, z, decide_true]
      simp only [circuitFun] at e0
      rw [c0] at e0
      have hfalse : (z 0 && z 1 || z 1 && z 2 || z 2 && z 3 || z 3 && z 4 || z 4 && z 0 ||
          z 0 && z 5 || z 1 && z 6 || z 2 && z 7 || z 3 && z 8 || z 5 && z 7 ||
          z 6 && z 8 || z 8 && z 5) = false := by
        rcases Nat.lt_or_ge C.output 9 with hlt9 | _
        · interval_cases hco : C.output <;> simp [z, hco]
        · omega
      rw [hfalse] at e0; cases e0
  exact hRed C hC hNots hfirst hfun hreads h5 hsize hout10
