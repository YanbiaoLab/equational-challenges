-- Equation46701 → Equation54289
-- Recorded verdict: true
-- Premise: x * y = (z * w) * (y * (u * v))
-- Conclusion: x * (y * y) = z * (w * (x * w))
-- Original submission SHA-256: a81bd60e8f96d3cea7393094b83c10575af1373056034f9c7b2b4bbd144fccc6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = (z ◇ w) ◇ (y ◇ (u ◇ v))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = z ◇ (w ◇ (x ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0 q0 q0).trans ((h q1 q2 q0 q0 q0 q0).symm)).symm
  have apc2 : forall (q3 q4 q5 q6 q7:G), (q3 ◇ (q7 ◇ (q4 ◇ q5))) = (q6 ◇ q7):=by
    intro q3 q4 q5 q6 q7
    exact ((apc0 q3 (q3 ◇ q3) (q7 ◇ (q4 ◇ q5))).symm).trans ((h q6 q7 q3 q3 q4 q5).symm)
  have apc3 : forall (q8 q9 q10 q11 q12:G), (q9 ◇ (q8 ◇ q10)) = (q11 ◇ q12):=by
    intro q8 q9 q10 q11 q12
    exact ((congrArg (fun t => q9 ◇ t) (apc2 q12 q8 q8 q8 q10)).symm).trans (apc2 q9 q10 (q8 ◇ q8) q11 q12)
  exact (apc3 y x y (x ◇ (y ◇ y)) (z ◇ (w ◇ (x ◇ w)))).trans ((apc3 w z (x ◇ w) (x ◇ (y ◇ y)) (z ◇ (w ◇ (x ◇ w)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46701_to_54289 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46701_to_54289
