-- Equation31142 → Equation45319
-- Recorded verdict: true
-- Premise: x = (x * ((y * z) * (x * z))) * w
-- Conclusion: x * y = x * (((z * x) * y) * y)
-- Original submission SHA-256: d88b6dbee6cb4c15817ed02270b12c19c8e435f536f748959c02c0ff73215a4a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ ((y ◇ z) ◇ (x ◇ z))) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ (((z ◇ x) ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (q0 ◇ ((q1 ◇ q2) ◇ (q0 ◇ q2))) = (q0 ◇ q3):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => t ◇ q3) ((h q0 q1 q2 ((q0 ◇ q0) ◇ ((q0 ◇ ((q1 ◇ q2) ◇ (q0 ◇ q2))) ◇ q0))).symm)).symm).trans ((h (q0 ◇ ((q1 ◇ q2) ◇ (q0 ◇ q2))) q0 q0 q3).symm)).symm
  have apc1 : forall (q0 q1 q2 q3:G), (q0 ◇ q3) = (q0 ◇ q0):=by
    intro q0 q1 q2 q3
    exact ((apc0 q0 q1 q2 q3).symm).trans (apc0 q0 q1 q2 q0)
  exact (apc1 x (x ◇ y) (x ◇ y) y).trans ((apc1 x (x ◇ y) (x ◇ y) (((z ◇ x) ◇ y) ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_31142_to_45319 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_31142_to_45319
