import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20862

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 25 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.and, [4, 15]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.or, [14, 18]⟩], 19⟩

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

theorem small : circ.size ≤ 10 := by decide

theorem right : PEqualNP.Represents.Represents (fun u v : Fin 5 => (29755425 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_20862

theorem PEqualNP.Outside.L_meta_20862 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (29755425 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.L_meta_20862.circ, PEqualNP.Outside.L_meta_20862.fits, PEqualNP.Outside.L_meta_20862.small, PEqualNP.Outside.L_meta_20862.right⟩
