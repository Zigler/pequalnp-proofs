import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22398

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 24 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.and, [15, 16]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [18, 19]⟩, ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.or, [21, 20]⟩], 22⟩

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

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (851773 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22398

theorem PEqualNP.Outside.L_meta_22398 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851773 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨PEqualNP.Outside.L_meta_22398.circ, PEqualNP.Outside.L_meta_22398.fits, PEqualNP.Outside.L_meta_22398.small, PEqualNP.Outside.L_meta_22398.right⟩
