import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19175

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 16 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.not, [6]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩

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

theorem right : PEqualNP.Represents.Represents (fun u v : Fin 4 => (4683 : ℕ).testBit (4 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_19175

theorem PEqualNP.Outside.L_meta_19175 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4683 : ℕ).testBit (4 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_19175.circ, PEqualNP.Outside.L_meta_19175.fits, PEqualNP.Outside.L_meta_19175.small, PEqualNP.Outside.L_meta_19175.right⟩
