import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56226

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 21 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [13, 9]⟩, ⟨GateOp.or, [14, 10]⟩, ⟨GateOp.or, [15, 12]⟩], 16⟩

def okOp : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

def shapeB (C : Circuit) : Bool :=
  C.gates.all fun g => okOp g.op && decide (g.inputs.length ≤ 2)

theorem shapeB_sound {C : Circuit} (h : shapeB C = true) : FanInTwo C := by
  intro g hg
  have := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨?_, this.2⟩
  have h1 := this.1
  cases hop : g.op <;> rw [hop] at h1 <;> simp_all [okOp]

theorem fits : FanInTwo circ := shapeB_sound (by decide)

theorem small : circ.size ≤ 11 := by decide

theorem right : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (281251647 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_56226

theorem PEqualNP.Outside.L_meta_56226 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (281251647 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_56226.circ, PEqualNP.Outside.L_meta_56226.fits, PEqualNP.Outside.L_meta_56226.small, PEqualNP.Outside.L_meta_56226.right⟩
