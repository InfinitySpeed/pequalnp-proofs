import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4852_1
    (h_mono :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ g ∈ x1.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
        PEqualNP.MetaComplexity.FanInTwo x1 →
        x1.size ≤ (13 : ℕ) →
        ∃ (x4 : Fin (9 : ℕ) → Bool),
          x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (9 : ℕ)), x4 (1 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ))]) ≠
            (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) ||
              x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) ||
              x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) ||
              x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) ||
              x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) ||
              x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) ||
              x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) ||
              x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) ||
              x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) ||
              x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) ||
              x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) ||
              x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))))
    (h_not :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        (∃ g ∈ x1.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
        PEqualNP.MetaComplexity.FanInTwo x1 →
        x1.size ≤ (13 : ℕ) →
        ∃ (x4 : Fin (9 : ℕ) → Bool),
          x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (9 : ℕ)), x4 (1 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ))]) ≠
            (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) ||
              x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) ||
              x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) ||
              x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) ||
              x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) ||
              x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) ||
              x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) ||
              x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) ||
              x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) ||
              x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) ||
              x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) ||
              x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x1 →
      x1.size ≤ (13 : ℕ) →
      ∃ (x4 : Fin (9 : ℕ) → Bool),
        x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (9 : ℕ)), x4 (1 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ))]) ≠
          (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) ||
            x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) ||
            x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) ||
            x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) ||
            x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) ||
            x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) ||
            x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) ||
            x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) ||
            x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) ||
            x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) ||
            x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) ||
            x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) := by
  intro x1 hfan hsize
  by_cases h : ∃ g ∈ x1.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · exact h_not x1 h hfan hsize
  · exact h_mono x1 (fun g hg hnot => h ⟨g, hg, hnot⟩) hfan hsize
