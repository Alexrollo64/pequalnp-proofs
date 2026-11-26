import PEqualNP.Defs

theorem Alexrollo64.Graph23736Reference : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841069 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 15]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 16]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 17]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 18]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 19]⟩], 20⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
