-- Equation42113 → Equation3339
-- Recorded verdict: true
-- Premise: x * y = z * (y * (x * (x * z)))
-- Conclusion: x * y = x * (z * (w * z))
-- Original submission SHA-256: 906a56d994c0a00b033f8917f6665398cafd9c3913a6d927671d149d620fc38b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ (y ◇ (x ◇ (x ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = x ◇ (z ◇ (w ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((q0 ◇ (q0 ◇ q1)) ◇ (q2 ◇ (q0 ◇ q1))) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q0 ◇ (q0 ◇ q1)) ◇ t) (congrArg (fun t => q2 ◇ t) ((h q0 q1 q1).symm))).symm).trans ((h q1 q2 (q0 ◇ (q0 ◇ q1))).symm)
  have apc1 : forall (q3 q4:G), (q3 ◇ (q3 ◇ (q3 ◇ q4))) = (q4 ◇ (q4 ◇ q3)):=by
    intro q3 q4
    exact (((congrArg (fun t => q4 ◇ t) (apc0 q3 q4 q3)).symm).trans ((h q3 (q3 ◇ (q3 ◇ q4)) q4).symm)).symm
  have apc2 : forall (q5 q6:G), (q5 ◇ (q5 ◇ q6)) = (q5 ◇ q5):=by
    intro q5 q6
    exact ((apc1 q6 q5).symm).trans (((congrArg (fun t => q6 ◇ t) (apc1 q5 q6)).symm).trans ((h q5 q5 q6).symm))
  have apc3 : forall (q7 q8 q9:G), (q9 ◇ (q8 ◇ (q7 ◇ q7))) = (q7 ◇ q8):=by
    intro q7 q8 q9
    exact ((congrArg (fun t => q9 ◇ t) (congrArg (fun t => q8 ◇ t) (apc2 q7 q9))).symm).trans ((h q7 q8 q9).symm)
  have apc5 : forall (q10 q11 q12:G), (q12 ◇ (q10 ◇ q11)) = (q12 ◇ q12):=by
    intro q10 q11 q12
    exact ((congrArg (fun t => q12 ◇ t) ((h q10 q11 q12).symm)).symm).trans (apc2 q12 (q11 ◇ (q10 ◇ (q10 ◇ q12))))
  have apc7 : forall (q13 q14:G), (q14 ◇ q14) = (q14 ◇ q13):=by
    intro q13 q14
    exact ((apc5 q14 q14 q14).symm).trans (((congrArg (fun t => q14 ◇ t) (apc3 q14 q14 q13)).symm).trans ((h q14 q13 q14).symm))
  exact ((apc7 y x).symm).trans (apc7 (z ◇ (w ◇ z)) x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42113_to_3339 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42113_to_3339
