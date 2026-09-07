-- Equation45462 → Equation4273
-- Recorded verdict: true
-- Premise: x * y = y * (((y * z) * w) * z)
-- Conclusion: x * (x * x) = y * (x * y)
-- Original submission SHA-256: dbc2106d527c2bb8a25f6437f0120e1fb37ef65cd416c7706fc522191416107a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (((y ◇ z) ◇ w) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ x) = y ◇ (x ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ (q2 ◇ q2)) = (q0 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q1 ◇ t) ((apc0 ((q1 ◇ q2) ◇ q0) q2 q0 q0).symm)).symm).trans ((h q0 q1 q2 q0).symm)
  have apc2 : forall (q0 q1 q2:G), (q1 ◇ (q2 ◇ q2)) = (q1 ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact (apc1 q0 q1 q2).trans ((apc1 q0 q1 q0).symm)
  have apc3 : forall (q0 q1 q2:G), (q1 ◇ (q1 ◇ q1)) = (q1 ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact (((apc2 q0 q1 q2).symm).trans (apc2 q1 q1 q2)).symm
  have apc6 : forall (q3 q4 q5:G), (q5 ◇ (q4 ◇ q4)) = (q3 ◇ (q4 ◇ q4)):=by
    intro q3 q4 q5
    exact (((apc1 q3 (q4 ◇ q4) q4).symm).trans (apc0 q5 (q4 ◇ q4) q3 q3)).symm
  have apc7 : forall (q3 q4 q5:G), (q4 ◇ (q4 ◇ q4)) = (q3 ◇ (q4 ◇ q4)):=by
    intro q3 q4 q5
    exact (((apc6 q3 q4 q5).symm).trans (apc6 q4 q4 q5)).symm
  have apc9 : forall (q6 q7:G), (q7 ◇ (q7 ◇ q7)) = (q6 ◇ (q6 ◇ q6)):=by
    intro q6 q7
    exact ((apc7 q7 q6 q6).trans ((apc3 q6 q7 q6).symm)).symm
  have apc10 : forall (q8 q9 q10:G), (q10 ◇ (q8 ◇ q10)) = (q9 ◇ (q9 ◇ q9)):=by
    intro q8 q9 q10
    exact ((congrArg (fun t => q10 ◇ t) (apc0 q8 q10 q8 q8)).symm).trans (apc9 q9 q10)
  exact (apc10 x (x ◇ (x ◇ x)) x).trans ((apc10 x (x ◇ (x ◇ x)) y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45462_to_4273 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45462_to_4273
