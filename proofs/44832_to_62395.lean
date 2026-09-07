-- Equation44832 → Equation62395
-- Recorded verdict: true
-- Premise: x * y = z * ((z * (x * w)) * y)
-- Conclusion: (x * y) * z = ((z * z) * x) * z
-- Original submission SHA-256: 6b5c474b17ff9341d04b8388711c15437bedbfbbb01d62ac4f47b1c688abe057
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((z ◇ (x ◇ w)) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = ((z ◇ z) ◇ x) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q4 ◇ ((q1 ◇ q2) ◇ q3)) = ((q4 ◇ (q1 ◇ q0)) ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => q4 ◇ t) (congrArg (fun t => t ◇ q3) ((h q1 q2 q4 q0).symm))).symm).trans ((h (q4 ◇ (q1 ◇ q0)) q3 q4 q2).symm)
  have apc1 : forall (q5 q6 q7 q8:G), ((q8 ◇ (q8 ◇ q5)) ◇ q7) = (q6 ◇ q7):=by
    intro q5 q6 q7 q8
    exact ((apc0 q5 q8 (q6 ◇ q5) q7 q8).symm).trans ((h q6 q7 q8 q5).symm)
  exact ((apc1 (((z ◇ z) ◇ x) ◇ z) (x ◇ y) z ((x ◇ y) ◇ z)).symm).trans (apc1 (((z ◇ z) ◇ x) ◇ z) ((z ◇ z) ◇ x) z ((x ◇ y) ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_44832_to_62395 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_44832_to_62395
