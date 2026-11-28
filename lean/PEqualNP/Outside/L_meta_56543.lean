import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56543

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 21 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [2, 14]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [16, 15]⟩], 17⟩

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

theorem right : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50616 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_56543

theorem PEqualNP.Outside.L_meta_56543 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50616 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_56543.circ, PEqualNP.Outside.L_meta_56543.fits, PEqualNP.Outside.L_meta_56543.small, PEqualNP.Outside.L_meta_56543.right⟩
