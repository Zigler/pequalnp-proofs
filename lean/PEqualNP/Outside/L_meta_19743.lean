import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19743

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 64 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [17, 13]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.and, [0, 19]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [21, 15]⟩, ⟨GateOp.or, [10, 22]⟩, ⟨GateOp.or, [8, 23]⟩, ⟨GateOp.and, [1, 24]⟩, ⟨GateOp.or, [9, 15]⟩, ⟨GateOp.or, [13, 26]⟩, ⟨GateOp.or, [8, 27]⟩, ⟨GateOp.or, [12, 28]⟩, ⟨GateOp.and, [2, 29]⟩, ⟨GateOp.or, [18, 21]⟩, ⟨GateOp.and, [3, 31]⟩, ⟨GateOp.or, [11, 23]⟩, ⟨GateOp.and, [4, 33]⟩, ⟨GateOp.or, [16, 14]⟩, ⟨GateOp.or, [17, 35]⟩, ⟨GateOp.and, [5, 36]⟩, ⟨GateOp.or, [21, 27]⟩, ⟨GateOp.and, [6, 38]⟩, ⟨GateOp.or, [10, 27]⟩, ⟨GateOp.or, [11, 40]⟩, ⟨GateOp.and, [7, 41]⟩, ⟨GateOp.or, [20, 25]⟩, ⟨GateOp.or, [43, 30]⟩, ⟨GateOp.or, [44, 32]⟩, ⟨GateOp.or, [45, 34]⟩, ⟨GateOp.or, [46, 37]⟩, ⟨GateOp.or, [47, 39]⟩, ⟨GateOp.or, [48, 42]⟩], 49⟩

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

theorem small : circ.size ≤ 34 := by decide

theorem right : PEqualNP.Represents.Represents (fun u v : Fin 8 => (12606226115316667695 : ℕ).testBit (8 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_19743

theorem PEqualNP.Outside.L_meta_19743 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12606226115316667695 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  exact ⟨PEqualNP.Outside.L_meta_19743.circ, PEqualNP.Outside.L_meta_19743.fits, PEqualNP.Outside.L_meta_19743.small, PEqualNP.Outside.L_meta_19743.right⟩
