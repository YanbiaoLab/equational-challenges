-- Equation25684 → Equation43136
-- Recorded verdict: true
-- Premise: x = (y ◇ (z ◇ (w ◇ w))) ◇ (x ◇ u)
-- Conclusion: x ◇ y = z ◇ (z ◇ ((w ◇ u) ◇ x))
-- Original submission SHA-256: f26649b3bf7459871076b96ebd789182a89a960e58febe472893bae1701498ea
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ (z ◇ (w ◇ w))) ◇ (x ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (z ◇ ((w ◇ u) ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ q0)) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q1 ◇ q0)) ((h q2 q0 q0 q0 (q0 ◇ q0)).symm)).symm).trans ((h q1 (q0 ◇ (q0 ◇ (q0 ◇ q0))) q2 q0 q0).symm)
  have apc1 : forall (q3 q4 q5 q6 q7:G), (q6 ◇ q4) = (q5 ◇ q3):=by
    intro q3 q4 q5 q6 q7
    exact (((congrArg (fun t => q6 ◇ t) ((h q4 q5 q7 q3 q3).symm)).symm).trans (apc0 (q4 ◇ q3) (q5 ◇ (q7 ◇ (q3 ◇ q3))) q6)).trans (congrArg (fun t => q5 ◇ t) (apc0 q3 q3 q7))
  have apc2 : forall (q3 q4 q5 q7 q6:G), (q5 ◇ q3) = (q4 ◇ q4):=by
    intro q3 q4 q5 q7 q6
    exact ((apc1 q3 q4 q5 q6 q7).symm).trans (apc1 q4 q4 q4 q6 q7)
  exact (apc2 y (x ◇ y) x (x ◇ y) (x ◇ y)).trans ((apc2 (z ◇ ((w ◇ u) ◇ x)) (x ◇ y) z (x ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_25684_to_43136 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_25684_to_43136
