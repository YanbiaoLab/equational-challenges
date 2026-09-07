-- Equation15408 → Equation10071
-- Recorded verdict: true
-- Premise: x = x * (((y * (z * w)) * z) * z)
-- Conclusion: x = x * ((y * y) * ((z * y) * y))
-- Original submission SHA-256: 83f40cf92757ffed7142330c42e62eae3bcbf3fb4fcae562fcc98b9958429368
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (((y ◇ (z ◇ w)) ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ y) ◇ ((z ◇ y) ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2:G), (q0 ◇ (((q1 ◇ q2) ◇ q2) ◇ q2)) = q0:=by
    intro q0 q1 q2
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ q2) (cg (fun t => q1 ◇ t) ((h q2 q0 q0 q0).symm))))).symm).trans ((h q0 q1 q2 (((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5 q6:G), (q5 ◇ ((q6 ◇ ((q3 ◇ q4) ◇ q4)) ◇ ((q3 ◇ q4) ◇ q4))) = q5:=by
    intro q3 q4 q5 q6
    exact ((cg (fun t => q5 ◇ t) (cg (fun t => t ◇ ((q3 ◇ q4) ◇ q4)) (cg (fun t => t ◇ ((q3 ◇ q4) ◇ q4)) (apc0 q6 q3 q4)))).symm).trans ((h q5 q6 ((q3 ◇ q4) ◇ q4) q4).symm)
  have apc2 : forall (q7 q8 q9 q10 q11:G), (q8 ◇ ((q9 ◇ q7) ◇ q7)) = q8:=by
    intro q7 q8 q9 q10 q11
    exact ((((cg (fun t => q8 ◇ t) (cg (fun t => t ◇ ((q7 ◇ (((q10 ◇ q11) ◇ q11) ◇ q11)) ◇ (((q10 ◇ q11) ◇ q11) ◇ q11))) (cg (fun t => q9 ◇ t) (apc0 q7 q10 q11)))).trans (cg (fun t => q8 ◇ t) (cg (fun t => (q9 ◇ q7) ◇ t) (cg (fun t => t ◇ (((q10 ◇ q11) ◇ q11) ◇ q11)) (apc0 q7 q10 q11))))).trans (cg (fun t => q8 ◇ t) (cg (fun t => (q9 ◇ q7) ◇ t) (apc0 q7 q10 q11)))).symm).trans (((cg (fun t => q8 ◇ t) (cg (fun t => t ◇ ((q7 ◇ (((q10 ◇ q11) ◇ q11) ◇ q11)) ◇ (((q10 ◇ q11) ◇ q11) ◇ q11))) (cg (fun t => q9 ◇ t) (apc0 (q7 ◇ (((q10 ◇ q11) ◇ q11) ◇ q11)) q10 q11)))).symm).trans (apc1 q7 (((q10 ◇ q11) ◇ q11) ◇ q11) q8 q9))
  have apc3 : forall (q12 q13 q14 q15:G), (q12 ◇ q13) = q12:=by
    intro q12 q13 q14 q15
    exact (((cg (fun t => q12 ◇ t) (cg (fun t => t ◇ (((q14 ◇ q15) ◇ q15) ◇ q15)) (apc2 q15 q13 (q14 ◇ q15) (q13 ◇ (((q14 ◇ q15) ◇ q15) ◇ q15)) (q13 ◇ (((q14 ◇ q15) ◇ q15) ◇ q15))))).trans (cg (fun t => q12 ◇ t) (apc2 q15 q13 (q14 ◇ q15) (q13 ◇ (((q14 ◇ q15) ◇ q15) ◇ q15)) (q13 ◇ (((q14 ◇ q15) ◇ q15) ◇ q15))))).symm).trans (((cg (fun t => q12 ◇ t) (apc0 ((q13 ◇ (((q14 ◇ q15) ◇ q15) ◇ q15)) ◇ (((q14 ◇ q15) ◇ q15) ◇ q15)) q14 q15)).symm).trans (apc0 q12 q13 (((q14 ◇ q15) ◇ q15) ◇ q15)))
  exact (apc3 x ((y ◇ y) ◇ ((z ◇ y) ◇ y)) x x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_15408_to_10071 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_15408_to_10071
