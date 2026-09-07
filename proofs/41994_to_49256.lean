-- Equation41994 → Equation49256
-- Recorded verdict: true
-- Premise: x * y = y * (z * (z * (x * w)))
-- Conclusion: x * y = ((z * z) * w) * (x * y)
-- Original submission SHA-256: 77b161a2074621c4118d53fa3cef1a925db5bc3e8939323f26c0294ebbbea7d6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (z ◇ (z ◇ (x ◇ w)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ z) ◇ w) ◇ (x ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ q1)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) ((h q0 q1 q1 q0).symm)).symm).trans ((h q1 q2 q1 (q0 ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5 q6:G), ((q3 ◇ q4) ◇ q6) = (q5 ◇ q6):=by
    intro q3 q4 q5 q6
    exact (((apc0 q4 q5 q6).symm).trans (((congrArg (fun t => q6 ◇ t) (apc0 q3 q4 q5)).symm).trans (apc0 q5 (q3 ◇ q4) q6))).symm
  have apc11 : forall (q7 q8 q9 q10 q11:G), (q9 ◇ q8) = (q7 ◇ q9):=by
    intro q7 q8 q9 q10 q11
    exact ((apc0 q10 q9 q8).symm).trans ((((apc1 q11 q7 q8 (q10 ◇ q9)).symm).trans (apc0 q10 q9 (q11 ◇ q7))).trans (apc0 q11 q7 q9))
  exact (apc11 (x ◇ y) y x (x ◇ y) (x ◇ y)).trans (apc11 ((z ◇ z) ◇ w) x (x ◇ y) (x ◇ y) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41994_to_49256 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41994_to_49256
