import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56621

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 21 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.and, [7, 11]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.and, [8, 15]⟩, ⟨GateOp.or, [13, 16]⟩], 17⟩

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

theorem small : circ.size ≤ 12 := by decide

theorem right : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52793 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_56621

theorem PEqualNP.Outside.L_meta_56621 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52793 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_56621.circ, PEqualNP.Outside.L_meta_56621.fits, PEqualNP.Outside.L_meta_56621.small, PEqualNP.Outside.L_meta_56621.right⟩
