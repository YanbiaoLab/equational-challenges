-- Equation25906 → Equation60316
-- Recorded verdict: true
-- Premise: x = (x * ((y * z) * z)) * (x * w)
-- Conclusion: (x * y) * y = (x * y) * (z * x)
-- Original submission SHA-256: d8acd71d801b87a112dc7147e0c137489417bb92c48cb7358bad449050cfdcd0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ ((y ◇ z) ◇ z)) ◇ (x ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ y = (x ◇ y) ◇ (z ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), ((q3 ◇ (q0 ◇ q1)) ◇ (q3 ◇ q2)) = q3:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ (q3 ◇ q2)) (congrArg (fun t => q3 ◇ t) ((h (q0 ◇ q1) q0 q1 q1).symm))).symm).trans ((h q3 (q0 ◇ q1) ((q0 ◇ q1) ◇ q1) q2).symm)
  have apc1 : forall (q4 q5 q6:G), ((q6 ◇ q4) ◇ (q6 ◇ q5)) = q6:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => t ◇ (q6 ◇ q5)) (congrArg (fun t => q6 ◇ t) (apc0 q4 q4 q4 q4))).symm).trans (apc0 (q4 ◇ (q4 ◇ q4)) (q4 ◇ q4) q5 q6)
  have apc2 : forall (q7 q8 q9 q10:G), ((q9 ◇ q10) ◇ (((q9 ◇ q10) ◇ q7) ◇ q8)) = ((q9 ◇ q10) ◇ q7):=by
    intro q7 q8 q9 q10
    exact ((congrArg (fun t => t ◇ (((q9 ◇ q10) ◇ q7) ◇ q8)) (apc1 q7 q10 (q9 ◇ q10))).symm).trans ((h ((q9 ◇ q10) ◇ q7) q9 q10 q8).symm)
  have apc3 : forall (q11 q12 q13:G), ((q12 ◇ q13) ◇ q11) = q12:=by
    intro q11 q12 q13
    exact (((apc1 q13 q13 q12).symm).trans (((congrArg (fun t => (q12 ◇ q13) ◇ t) (apc1 q11 q11 (q12 ◇ q13))).symm).trans (apc2 q11 ((q12 ◇ q13) ◇ q11) q12 q13))).symm
  exact (apc3 y x y).trans ((apc3 (z ◇ x) x y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_25906_to_60316 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_25906_to_60316
