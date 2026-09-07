-- Equation43983 → Equation54352
-- Recorded verdict: true
-- Premise: x * y = z * ((z * z) * (y * w))
-- Conclusion: x * (y * z) = x * (z * (y * z))
-- Original submission SHA-256: 57ca506a879b969e304d98bc1046998990c32e25b1195070ca7f8e28ec7a4409
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((z ◇ z) ◇ (y ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = x ◇ (z ◇ (y ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) = (q3 ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => q3 ◇ t) ((h q0 q1 (q3 ◇ q3) q0).symm)).symm).trans ((h q2 ((q3 ◇ q3) ◇ (q3 ◇ q3)) q3 (q1 ◇ q0)).symm)).symm
  exact ((apc0 y z (x ◇ (y ◇ z)) x).symm).trans (apc0 z (y ◇ z) (x ◇ (y ◇ z)) x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43983_to_54352 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43983_to_54352
