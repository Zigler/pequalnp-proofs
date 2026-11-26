import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22356

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 24 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.and, [1, 15]⟩, ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.and, [2, 17]⟩, ⟨GateOp.and, [3, 13]⟩, ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.or, [20, 18]⟩, ⟨GateOp.or, [21, 19]⟩], 22⟩

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

theorem small : circ.size ≤ 13 := by decide

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (841196 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22356

theorem PEqualNP.Outside.L_meta_22356 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841196 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨PEqualNP.Outside.L_meta_22356.circ, PEqualNP.Outside.L_meta_22356.fits, PEqualNP.Outside.L_meta_22356.small, PEqualNP.Outside.L_meta_22356.right⟩
