import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23059

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 24 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [15, 8]⟩, ⟨GateOp.and, [14, 16]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [5, 18]⟩, ⟨GateOp.and, [3, 19]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [1, 21]⟩, ⟨GateOp.and, [22, 4]⟩, ⟨GateOp.or, [13, 17]⟩, ⟨GateOp.or, [24, 20]⟩, ⟨GateOp.or, [25, 23]⟩], 26⟩

def okOp : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

def shapeB (C : Circuit) : Bool :=
  C.gates.all fun g => okOp g.op && decide (g.inputs.length ≤ 2)

theorem shapeB_sound {C : Circuit} (h : shapeB C = true) : Monotone2 C := by
  intro g hg
  have := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨?_, this.2⟩
  have h1 := this.1
  cases hop : g.op <;> rw [hop] at h1 <;> simp_all [okOp]

theorem fits : Monotone2 circ := shapeB_sound (by decide)

theorem small : circ.size ≤ 17 := by decide

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (1948542 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_23059

theorem PEqualNP.Outside.L_meta_23059 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948542 : ℕ).testBit (6 * u.val + v.val)) 17 := by
  exact ⟨PEqualNP.Outside.L_meta_23059.circ, PEqualNP.Outside.L_meta_23059.fits, PEqualNP.Outside.L_meta_23059.small, PEqualNP.Outside.L_meta_23059.right⟩
