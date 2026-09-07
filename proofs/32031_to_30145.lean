-- Equation32031 → Equation30145
-- Recorded verdict: true
-- Premise: x = (x ◇ ((y ◇ (z ◇ y)) ◇ y)) ◇ z
-- Conclusion: x = (x ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ z
-- Original submission SHA-256: a6a44b82d33d68b964285e48047282e7591d25fda4e378725c136ac5e9e31750
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Tactic

-- Embedded module: JudgeMagma.Magma
section
/- Magma class, ◇ notation, and helpers for building finite magmas. -/

class Magma (α : Type _) where
  /-- The binary magma operation, written `◇`. -/
  op : α → α → α

@[inherit_doc] infix:65 " ◇ " => Magma.op

/-- Build a `Magma (Fin n)` from a flat list of values.
    Entry at index `i*n + j` gives the result of `i ◇ j`.
    Usage: `instance : Magma (Fin 3) := magmaFin 3 [0,0,0, 0,0,0, 0,0,1]`

    Marked `@[implicit_reducible]` because Lean 4.32 requires class-valued
    definitions to be transparent to instance resolution. Deliberately not
    plain `@[reducible]`: that would unfold the table literal during general
    unification too, which is pure cost for the large `Fin n` tables here. -/
@[implicit_reducible]
def magmaFin (n : Nat) (table : List Nat) : Magma (Fin n) where
  op a b :=
    let idx := a.val * n + b.val
    ⟨table[idx]! % n, Nat.mod_lt _ (Fin.pos a)⟩
end

-- Embedded module: JudgeProblem
section
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ ((y ◇ (z ◇ y)) ◇ y)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q1 ◇ (q1 ◇ q1))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ (q1 ◇ q1))) (cg (fun t => q0 ◇ t) ((h q1 q1 q1).symm))).symm).trans ((h q0 q1 (q1 ◇ (q1 ◇ q1))).symm)
  have apc1 : forall (x y z:G), ((x ◇ ((y ◇ (z ◇ y)) ◇ y)) ◇ z) = ((x ◇ ((x ◇ (x ◇ x)) ◇ x)) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc6 : forall (q2 q3 q4:G), ((q4 ◇ (((q3 ◇ (q3 ◇ q3)) ◇ q2) ◇ (q3 ◇ (q3 ◇ q3)))) ◇ (q2 ◇ q3)) = q4:=by
    intro q2 q3 q4
    exact ((cg (fun t => t ◇ (q2 ◇ q3)) (cg (fun t => q4 ◇ t) (cg (fun t => t ◇ (q3 ◇ (q3 ◇ q3))) (cg (fun t => (q3 ◇ (q3 ◇ q3)) ◇ t) (apc0 q2 q3))))).symm).trans ((h q4 (q3 ◇ (q3 ◇ q3)) (q2 ◇ q3)).symm)
  have apc7 : forall (q5 q6:G), ((q6 ◇ (q5 ◇ (q5 ◇ q5))) ◇ (q5 ◇ q5)) = q6:=by
    intro q5 q6
    exact ((cg (fun t => t ◇ (q5 ◇ q5)) (cg (fun t => q6 ◇ t) (apc0 (q5 ◇ (q5 ◇ q5)) q5))).symm).trans (apc6 q5 q5 q6)
  have apc9 : forall (q7 q8:G), (q7 ◇ (q8 ◇ q8)) = (q7 ◇ q8):=by
    intro q7 q8
    exact ((cg (fun t => t ◇ (q8 ◇ q8)) (apc0 q7 q8)).symm).trans (apc7 q8 (q7 ◇ q8))
  have apc11 : forall (q0 q1:G), ((q0 ◇ q1) ◇ q1) = q0:=by
    intro q0 q1
    exact (((cg (fun t => (q0 ◇ q1) ◇ t) (apc9 q1 q1)).trans (apc9 (q0 ◇ q1) q1)).symm).trans (apc0 q0 q1)
  have apc13 : forall (q9 q10 q11:G), (q9 ◇ ((q10 ◇ (q11 ◇ q10)) ◇ q10)) = (q9 ◇ q11):=by
    intro q9 q10 q11
    exact (((((((cg (fun t => t ◇ (q11 ◇ (q11 ◇ q11))) (cg (fun t => t ◇ q9) (cg (fun t => q9 ◇ t) (cg (fun t => t ◇ q9) (apc9 q9 q9))))).trans (cg (fun t => t ◇ (q11 ◇ (q11 ◇ q11))) (cg (fun t => t ◇ q9) (cg (fun t => q9 ◇ t) (apc11 q9 q9))))).trans (cg (fun t => t ◇ (q11 ◇ (q11 ◇ q11))) (apc11 q9 q9))).trans (cg (fun t => q9 ◇ t) (apc9 q11 q11))).trans (apc9 q9 q11)).symm).trans (((cg (fun t => t ◇ (q11 ◇ (q11 ◇ q11))) (apc1 q9 q10 q11)).symm).trans (apc0 (q9 ◇ ((q10 ◇ (q11 ◇ q10)) ◇ q10)) q11))).symm
  have apc14 : forall (q12 q13 q14:G), (q13 ◇ (q14 ◇ (q12 ◇ q14))) = (q13 ◇ ((q14 ◇ q12) ◇ q14)):=by
    intro q12 q13 q14
    exact (((cg (fun t => q13 ◇ t) (cg (fun t => t ◇ q14) (apc13 q14 q14 q12))).symm).trans (apc13 q13 q14 (q14 ◇ (q12 ◇ q14)))).symm
  have apc15 : forall (q15 q16 q17:G), (q16 ◇ (q17 ◇ q15)) = (q16 ◇ q15):=by
    intro q15 q16 q17
    exact (((cg (fun t => q16 ◇ t) (cg (fun t => q17 ◇ t) (apc11 q15 q17))).symm).trans (apc14 (q15 ◇ q17) q16 q17)).trans (apc13 q16 q17 q15)
  have apc17 : forall (q18 q19 q20 q21:G), ((q19 ◇ q20) ◇ q18) = q19:=by
    intro q18 q19 q20 q21
    exact ((((((((cg (fun t => t ◇ (q21 ◇ ((q18 ◇ (q20 ◇ q18)) ◇ q18))) (cg (fun t => q19 ◇ t) (cg (fun t => t ◇ q20) (cg (fun t => q20 ◇ t) (cg (fun t => t ◇ q21) (cg (fun t => q21 ◇ t) (cg (fun t => t ◇ q21) (apc15 q21 q21 q21)))))))).trans (cg (fun t => t ◇ (q21 ◇ ((q18 ◇ (q20 ◇ q18)) ◇ q18))) (cg (fun t => q19 ◇ t) (cg (fun t => t ◇ q20) (cg (fun t => q20 ◇ t) (cg (fun t => t ◇ q21) (cg (fun t => q21 ◇ t) (apc11 q21 q21)))))))).trans (cg (fun t => t ◇ (q21 ◇ ((q18 ◇ (q20 ◇ q18)) ◇ q18))) (cg (fun t => q19 ◇ t) (cg (fun t => t ◇ q20) (cg (fun t => q20 ◇ t) (apc11 q21 q21)))))).trans (cg (fun t => (q19 ◇ ((q20 ◇ q21) ◇ q20)) ◇ t) (cg (fun t => q21 ◇ t) (cg (fun t => t ◇ q18) (apc15 q18 q18 q20))))).trans (cg (fun t => (q19 ◇ ((q20 ◇ q21) ◇ q20)) ◇ t) (cg (fun t => q21 ◇ t) (apc11 q18 q18)))).trans (cg (fun t => t ◇ (q21 ◇ q18)) (apc15 q20 q19 (q20 ◇ q21)))).trans (apc15 q18 (q19 ◇ q20) q21)).symm).trans ((((cg (fun t => t ◇ (q21 ◇ ((q18 ◇ (q20 ◇ q18)) ◇ q18))) (cg (fun t => q19 ◇ t) (cg (fun t => t ◇ q20) (cg (fun t => q20 ◇ t) (apc1 q21 q18 q20))))).symm).trans (apc1 q19 q20 (q21 ◇ ((q18 ◇ (q20 ◇ q18)) ◇ q18)))).trans (((cg (fun t => t ◇ q19) (cg (fun t => q19 ◇ t) (cg (fun t => t ◇ q19) (apc15 q19 q19 q19)))).trans (cg (fun t => t ◇ q19) (cg (fun t => q19 ◇ t) (apc11 q19 q19)))).trans (apc11 q19 q19)))
  exact (calc
    x = x:=rfl
    _ = ((x ◇ (x ◇ ((y ◇ x) ◇ x))) ◇ z):=(((cg (fun t => t ◇ z) (cg (fun t => x ◇ t) (cg (fun t => x ◇ t) (apc17 x y x ((y ◇ x) ◇ x))))).trans (cg (fun t => t ◇ z) (apc15 y x x))).trans (apc17 z x y ((x ◇ y) ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32031_to_30145 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_32031_to_30145
