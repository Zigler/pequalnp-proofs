import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53301

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The gate list held in the sketch of the step, replayed; right on all 15 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

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

theorem small : circ.size ≤ 8 := by decide

theorem right : ∀ i j : Fin 5, circ.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8595 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_53301

theorem PEqualNP.Outside.L_meta_53301 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8595 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_53301.circ, PEqualNP.Outside.L_meta_53301.fits, PEqualNP.Outside.L_meta_53301.small, PEqualNP.Outside.L_meta_53301.right⟩
