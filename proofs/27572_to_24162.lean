-- Equation27572 → Equation24162
-- Recorded verdict: true
-- Premise: x = ((x * (y * x)) * z) * (x * w)
-- Conclusion: x = ((x * y) * z) * ((z * w) * y)
-- Original submission SHA-256: 2a46c2221b63add0423503ffb12a6a05226d077a92733cb71cbcd88d9d967bef
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((x ◇ (y ◇ x)) ◇ z) ◇ (x ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((x ◇ y) ◇ z) ◇ ((z ◇ w) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), ((((q1 ◇ q0) ◇ q1) ◇ q3) ◇ ((q1 ◇ q0) ◇ q2)) = (q1 ◇ q0):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ ((q1 ◇ q0) ◇ q2)) (congrArg (fun t => t ◇ q3) (congrArg (fun t => (q1 ◇ q0) ◇ t) ((h q1 q0 q0 q0).symm)))).symm).trans ((h (q1 ◇ q0) ((q1 ◇ (q0 ◇ q1)) ◇ q0) q3 q2).symm)
  have apc1 : forall (q4 q5 q6 q7:G), (((q5 ◇ q4) ◇ q7) ◇ (q5 ◇ q4)) = (((q5 ◇ q4) ◇ q5) ◇ q6):=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => t ◇ (q5 ◇ q4)) (congrArg (fun t => t ◇ q7) (apc0 q4 q5 q5 q6))).symm).trans (((congrArg (fun t => (((((q5 ◇ q4) ◇ q5) ◇ q6) ◇ ((q5 ◇ q4) ◇ q5)) ◇ q7) ◇ t) (apc0 q4 q5 q4 q6)).symm).trans (apc0 q6 ((q5 ◇ q4) ◇ q5) ((q5 ◇ q4) ◇ q4) q7))
  have apc2 : forall (q8 q9 q10:G), (((q9 ◇ (q10 ◇ q9)) ◇ q9) ◇ q8) = q9:=by
    intro q8 q9 q10
    exact ((apc1 (q10 ◇ q9) q9 q8 q8).symm).trans ((h q9 q10 q8 (q10 ◇ q9)).symm)
  have apc3 : forall (q11 q12 q13 q14:G), (((q13 ◇ q11) ◇ q14) ◇ (q13 ◇ q12)) = q13:=by
    intro q11 q12 q13 q14
    exact ((congrArg (fun t => t ◇ (q13 ◇ q12)) (congrArg (fun t => t ◇ q14) (congrArg (fun t => q13 ◇ t) (apc2 q13 q11 q11)))).symm).trans ((h q13 ((q11 ◇ (q11 ◇ q11)) ◇ q11) q14 q12).symm)
  have apc6 : forall (q15 q16 q17:G), (q15 ◇ (q16 ◇ q15)) = (q15 ◇ q17):=by
    intro q15 q16 q17
    exact (((congrArg (fun t => t ◇ q17) ((h q15 q16 (q15 ◇ (q15 ◇ (q16 ◇ q15))) (q16 ◇ q15)).symm)).symm).trans (apc2 q17 (q15 ◇ (q16 ◇ q15)) q15)).symm
  have apc7 : forall (q18 q19 q20 q21:G), (((q20 ◇ q19) ◇ q21) ◇ q18) = q20:=by
    intro q18 q19 q20 q21
    exact ((apc6 ((q20 ◇ q19) ◇ q21) q20 q18).symm).trans (apc3 q19 ((q20 ◇ q19) ◇ q21) q20 q21)
  exact (calc
    x = x:=rfl
    _ = (((x ◇ y) ◇ z) ◇ ((z ◇ w) ◇ y)):=(apc7 ((z ◇ w) ◇ y) y x z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_27572_to_24162 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_27572_to_24162
