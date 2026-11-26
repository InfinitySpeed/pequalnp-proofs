import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25156

def circuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [3, 1]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [6, 0]⟩, ⟨.or, [3, 0]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.not, [12]⟩, ⟨.or, [9, 13]⟩], 14⟩

theorem valid : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_25156

theorem PEqualNP.Outside.L_meta_25156 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16522 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_25156.circuit, PEqualNP.Outside.L_meta_25156.valid, by decide, by decide +kernel⟩
