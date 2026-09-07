-- Equation32067 → Equation43534
-- Recorded verdict: true
-- Premise: x = (x * ((y * (z * w)) * y)) * w
-- Conclusion: x * y = x * ((y * y) * (x * y))
-- Original submission SHA-256: 5dca5580544cfcbeffb4cded9559aa00b7413bd16f432594f01934fc2d3252e6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ ((y ◇ (z ◇ w)) ◇ y)) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = x ◇ ((y ◇ y) ◇ (x ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ q0) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q0) (congrArg (fun t => q1 ◇ t) ((h q2 q0 q0 q2).symm))).symm).trans ((h q1 q2 (q0 ◇ (q0 ◇ q2)) q0).symm)
  have apc1 : forall (q3 q4 q5:G), (q3 ◇ q5) = (q3 ◇ q4):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => t ◇ q5) (apc0 q3 q3 q4)).symm).trans (apc0 q5 (q3 ◇ q4) q3)
  exact (apc1 x (x ◇ y) y).trans ((apc1 x (x ◇ y) ((y ◇ y) ◇ (x ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32067_to_43534 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_32067_to_43534
