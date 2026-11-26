import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22686

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 24 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.and, [4, 14]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.and, [11, 15]⟩, ⟨GateOp.or, [6, 19]⟩, ⟨GateOp.and, [16, 21]⟩, ⟨GateOp.or, [20, 22]⟩], 23⟩

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

theorem small : circ.size ≤ 14 := by decide

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (843191 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22686

theorem PEqualNP.Outside.L_meta_22686 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843191 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  exact ⟨PEqualNP.Outside.L_meta_22686.circ, PEqualNP.Outside.L_meta_22686.fits, PEqualNP.Outside.L_meta_22686.small, PEqualNP.Outside.L_meta_22686.right⟩
