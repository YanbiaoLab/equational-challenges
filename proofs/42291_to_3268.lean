-- Equation42291 → Equation3268
-- Recorded verdict: true
-- Premise: x * y = z * (w * (y * (x * x)))
-- Conclusion: x * x = y * (x * (x * x))
-- Original submission SHA-256: e22d5f1850fd87f54475737aca3a5623544ae4c287722e906e48534e61f6182f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (w ◇ (y ◇ (x ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = y ◇ (x ◇ (x ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ (q0 ◇ q0))) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) ((h q0 (q0 ◇ q0) q0 q1).symm)).symm).trans ((h (q0 ◇ q0) q1 q2 q0).symm)
  have apc1 : forall (q3 q4 q5 q6:G), (q4 ◇ (q3 ◇ (q3 ◇ q3))) = (q5 ◇ q6):=by
    intro q3 q4 q5 q6
    exact (apc0 q3 (q3 ◇ (q6 ◇ (q5 ◇ q5))) q4).trans ((h q5 q6 (q3 ◇ q3) q3).symm)
  exact (apc1 x y x x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42291_to_3268 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42291_to_3268
