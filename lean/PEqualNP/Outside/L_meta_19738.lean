import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19738

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 64 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [9, 15]⟩, ⟨GateOp.or, [10, 16]⟩, ⟨GateOp.or, [12, 17]⟩, ⟨GateOp.or, [11, 18]⟩, ⟨GateOp.and, [0, 19]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [10, 21]⟩, ⟨GateOp.or, [8, 22]⟩, ⟨GateOp.or, [23, 15]⟩, ⟨GateOp.and, [1, 24]⟩, ⟨GateOp.or, [11, 23]⟩, ⟨GateOp.and, [2, 26]⟩, ⟨GateOp.or, [8, 14]⟩, ⟨GateOp.or, [22, 28]⟩, ⟨GateOp.and, [3, 29]⟩, ⟨GateOp.or, [28, 17]⟩, ⟨GateOp.and, [4, 31]⟩, ⟨GateOp.or, [11, 14]⟩, ⟨GateOp.or, [33, 16]⟩, ⟨GateOp.or, [8, 34]⟩, ⟨GateOp.and, [5, 35]⟩, ⟨GateOp.or, [13, 34]⟩, ⟨GateOp.and, [6, 37]⟩, ⟨GateOp.or, [9, 21]⟩, ⟨GateOp.or, [39, 33]⟩, ⟨GateOp.and, [7, 40]⟩, ⟨GateOp.or, [20, 25]⟩, ⟨GateOp.or, [42, 27]⟩, ⟨GateOp.or, [43, 30]⟩, ⟨GateOp.or, [44, 32]⟩, ⟨GateOp.or, [45, 36]⟩, ⟨GateOp.or, [46, 38]⟩, ⟨GateOp.or, [47, 41]⟩], 48⟩

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

theorem small : circ.size ≤ 33 := by decide

theorem right : PEqualNP.Represents.Represents (fun u v : Fin 8 => (8857115674703410590 : ℕ).testBit (8 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_19738

theorem PEqualNP.Outside.L_meta_19738 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8857115674703410590 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  exact ⟨PEqualNP.Outside.L_meta_19738.circ, PEqualNP.Outside.L_meta_19738.fits, PEqualNP.Outside.L_meta_19738.small, PEqualNP.Outside.L_meta_19738.right⟩
