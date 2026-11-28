import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53429

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The gate list held in the sketch of the step, replayed; right on all 15 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [5, 4]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [11, 4]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [16, 14]⟩, ⟨GateOp.or, [17, 15]⟩], 18⟩

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

theorem small : circ.size ≤ 14 := by decide

theorem right : ∀ i j : Fin 5, circ.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266906 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_53429

theorem PEqualNP.Outside.L_meta_53429 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266906 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_53429.circ, PEqualNP.Outside.L_meta_53429.fits, PEqualNP.Outside.L_meta_53429.small, PEqualNP.Outside.L_meta_53429.right⟩
