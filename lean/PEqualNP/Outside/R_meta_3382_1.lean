import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3382_1
    (h_mono :
      have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) =>
        [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) =>
          x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ)))
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
        (∀ g ∈ x2.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
        PEqualNP.MetaComplexity.FanInTwo x2 →
        x2.size = (11 : ℕ) →
        PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 →
        List.Forall₂
          (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) =>
            x9.op = x10.op ∧
              List.Forall₂
                (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5))
                x9.inputs x10.inputs)
          x2.gates x3.gates →
        (∀ (x10 : Fin (7 : ℕ) → Bool),
          (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false =
            (x1 x10 || x10 (2 : Fin (7 : ℕ)))) →
        (List.filter
          (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) =>
            x11.op.eval [Bool.true, Bool.false] && x11.inputs.contains (2 : ℕ))
          x2.gates).length < (2 : ℕ))
    (h_not :
      have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) =>
        [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) =>
          x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ)))
      ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
        (∃ g ∈ x2.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
        PEqualNP.MetaComplexity.FanInTwo x2 →
        x2.size = (11 : ℕ) →
        PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 →
        List.Forall₂
          (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) =>
            x9.op = x10.op ∧
              List.Forall₂
                (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5))
                x9.inputs x10.inputs)
          x2.gates x3.gates →
        (∀ (x10 : Fin (7 : ℕ) → Bool),
          (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false =
            (x1 x10 || x10 (2 : Fin (7 : ℕ)))) →
        (List.filter
          (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) =>
            x11.op.eval [Bool.true, Bool.false] && x11.inputs.contains (2 : ℕ))
          x2.gates).length < (2 : ℕ)) :
    have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) =>
      [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) =>
        x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ)))
    ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
      PEqualNP.MetaComplexity.FanInTwo x2 →
      x2.size = (11 : ℕ) →
      PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 →
      List.Forall₂
        (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) =>
          x9.op = x10.op ∧
            List.Forall₂
              (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5))
              x9.inputs x10.inputs)
        x2.gates x3.gates →
      (∀ (x10 : Fin (7 : ℕ) → Bool),
        (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false =
          (x1 x10 || x10 (2 : Fin (7 : ℕ)))) →
      (List.filter
        (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) =>
          x11.op.eval [Bool.true, Bool.false] && x11.inputs.contains (2 : ℕ))
        x2.gates).length < (2 : ℕ) := by
  intro x1 x2 x3 x4 x5 hfan hsize hfun hrel h3
  by_cases h : ∃ g ∈ x2.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · exact h_not x2 x3 x4 x5 h hfan hsize hfun hrel h3
  · exact h_mono x2 x3 x4 x5 (fun g hg hnot => h ⟨g, hg, hnot⟩) hfan hsize hfun hrel h3
