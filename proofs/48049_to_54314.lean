-- Equation48049 → Equation54314
-- Recorded verdict: true
-- Premise: x * y = (y * (x * z)) * (y * w)
-- Conclusion: x * (y * z) = x * (x * (x * z))
-- Original submission SHA-256: 2a2c3e61df095af07221319e45245d8df2cca60e23418d80198630e7194eebe8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ (x ◇ z)) ◇ (y ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = x ◇ (x ◇ (x ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q4 ◇ (q0 ◇ q1)) ◇ (q4 ◇ q3)) = ((q1 ◇ (q0 ◇ q2)) ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ (q4 ◇ q3)) (congrArg (fun t => q4 ◇ t) ((h q0 q1 q2 q0).symm))).symm).trans ((h (q1 ◇ (q0 ◇ q2)) q4 (q1 ◇ q0) q3).symm)
  have apc1 : forall (q5 q6 q7 q8:G), ((q8 ◇ (q6 ◇ q5)) ◇ q7) = (q6 ◇ q7):=by
    intro q5 q6 q7 q8
    exact ((apc0 q6 q8 q5 q5 q7).symm).trans ((h q6 q7 q8 q5).symm)
  have apc2 : forall (q0 q3 q4 q1 q2:G), (q0 ◇ (q4 ◇ q3)) = (q0 ◇ q4):=by
    intro q0 q3 q4 q1 q2
    exact ((apc1 q1 q0 (q4 ◇ q3) q4).symm).trans ((apc0 q0 q1 q2 q3 q4).trans (apc1 q2 q0 q4 q1))
  have apc3 : forall (q9 q10 q11 q12:G), (q11 ◇ q10) = (q11 ◇ q9):=by
    intro q9 q10 q11 q12
    exact (((apc2 q11 q10 q9 (q11 ◇ (q9 ◇ q10)) (q11 ◇ (q9 ◇ q10))).symm).trans ((((congrArg (fun t => q11 ◇ t) ((h q9 q10 q12 q9).symm)).symm).trans (apc2 q11 (q10 ◇ q9) (q10 ◇ (q9 ◇ q12)) q9 q9)).trans ((congrArg (fun t => q11 ◇ t) (apc2 q10 q12 q9 (q10 ◇ (q9 ◇ q12)) (q10 ◇ (q9 ◇ q12)))).trans (apc2 q11 q9 q10 (q11 ◇ (q10 ◇ q9)) (q11 ◇ (q10 ◇ q9)))))).symm
  exact (apc3 (x ◇ (y ◇ z)) (y ◇ z) x (x ◇ (y ◇ z))).trans ((apc3 (x ◇ (y ◇ z)) (x ◇ (x ◇ z)) x (x ◇ (y ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48049_to_54314 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48049_to_54314
