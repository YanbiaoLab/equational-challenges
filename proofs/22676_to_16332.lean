-- Equation22676 → Equation16332
-- Recorded verdict: true
-- Premise: x = (y ◇ (y ◇ z)) ◇ ((x ◇ w) ◇ y)
-- Conclusion: x = y ◇ ((((x ◇ x) ◇ z) ◇ w) ◇ y)
-- Original submission SHA-256: 378c0e29f0d0cec293ef1633aec054b960a7d35ba3dcf08bf62cf62fb0970656
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (y ◇ z)) ◇ ((x ◇ w) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((((x ◇ x) ◇ z) ◇ w) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (q3 ◇ ((q2 ◇ q1) ◇ (q3 ◇ (q3 ◇ q0)))) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ ((q2 ◇ q1) ◇ (q3 ◇ (q3 ◇ q0)))) ((h q3 q3 q0 (q3 ◇ q0)).symm)).symm).trans ((h q2 (q3 ◇ (q3 ◇ q0)) q3 q1).symm)
  have apc1 : forall (q4 q5 q6 q7:G), ((q7 ◇ q4) ◇ ((q6 ◇ q5) ◇ q7)) = q6:=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => t ◇ ((q6 ◇ q5) ◇ q7)) (congrArg (fun t => q7 ◇ t) (apc0 q4 q4 q4 q7))).symm).trans ((h q6 q7 ((q4 ◇ q4) ◇ (q7 ◇ (q7 ◇ q4))) q5).symm)
  have apc2 : forall (q8 q9 q10 q11:G), (q8 ◇ ((q10 ◇ q9) ◇ q11)) = q10:=by
    intro q8 q9 q10 q11
    exact ((congrArg (fun t => t ◇ ((q10 ◇ q9) ◇ q11)) (apc0 q8 q8 q8 q11)).symm).trans (apc1 ((q8 ◇ q8) ◇ (q11 ◇ (q11 ◇ q8))) q9 q10 q11)
  have apc4 : forall (q12 q13 q14:G), (q13 ◇ q12) = q14:=by
    intro q12 q13 q14
    exact ((congrArg (fun t => q13 ◇ t) (apc2 (q14 ◇ q12) q12 q12 q12)).symm).trans (apc2 q13 q12 q14 ((q12 ◇ q12) ◇ q12))
  exact ((apc4 x x x).symm).trans ((apc4 ((((x ◇ x) ◇ z) ◇ w) ◇ y) y (x ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22676_to_16332 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22676_to_16332
