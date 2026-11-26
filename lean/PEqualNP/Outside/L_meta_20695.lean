import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20695

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 25 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [2, 13]⟩, ⟨GateOp.and, [5, 15]⟩, ⟨GateOp.or, [14, 16]⟩], 17⟩

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

theorem small : circ.size ≤ 8 := by decide

theorem right : PEqualNP.Represents.Represents (fun u v : Fin 5 => (16188448 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_20695

theorem PEqualNP.Outside.L_meta_20695 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (16188448 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  exact ⟨PEqualNP.Outside.L_meta_20695.circ, PEqualNP.Outside.L_meta_20695.fits, PEqualNP.Outside.L_meta_20695.small, PEqualNP.Outside.L_meta_20695.right⟩
