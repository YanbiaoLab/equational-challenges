-- Equation42493 → Equation41638
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ ((z ◇ w) ◇ w))
-- Conclusion: x ◇ x = y ◇ (y ◇ (z ◇ (x ◇ x)))
-- Original submission SHA-256: 3a129ada865b04400109ebfe31ad9800d87e055098e01e56ce0581d9f5f6bc3a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (x ◇ ((z ◇ w) ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (y ◇ (z ◇ (x ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have p0 : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ (q0 ◇ q0))) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => q1 ◇ t) ((h q0 (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) q0 q0).symm))).symm).trans ((h q1 q2 q0 (q0 ◇ ((q0 ◇ q0) ◇ q0))).symm)
  have p1 : forall (q1 q2 q3 q0:G), (q2 ◇ (q3 ◇ q3)) = (q1 ◇ q1):=by
    intro q1 q2 q3 q0
    exact ((congrArg (fun t => q2 ◇ t) (p0 q0 q3 (q3 ◇ (q0 ◇ q0)))).symm).trans (((congrArg (fun t => q2 ◇ t) (p0 q0 (q3 ◇ (q0 ◇ q0)) q1)).symm).trans ((h q1 q2 q3 (q0 ◇ q0)).symm))
  exact (((p0 z x y).symm).trans (congrArg (fun t => y ◇ t) (p1 z x z x))).trans ((congrArg (fun t => y ◇ t) (p0 x z y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42493_to_41638 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42493_to_41638
