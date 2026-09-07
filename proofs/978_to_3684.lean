-- Equation978 → Equation3684
-- Recorded verdict: true
-- Premise: x = y ◇ ((z ◇ z) ◇ (x ◇ y))
-- Conclusion: x ◇ x = (y ◇ y) ◇ (x ◇ x)
-- Original submission SHA-256: 43eb6dd1a04946caf8b1c6b9ec7ab99471317021a4dd8dfd6cf8ccbb6af393a4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ z) ◇ (x ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = (y ◇ y) ◇ (x ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have p0 : forall (q0 q1 q2:G), ((q0 ◇ (q2 ◇ q2)) ◇ q0) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q0 ◇ (q2 ◇ q2)) ◇ t) ((h q0 (q2 ◇ q2) q1).symm)).symm).trans ((h (q1 ◇ q1) (q0 ◇ (q2 ◇ q2)) q2).symm)
  exact (((p0 y x x).symm).trans (p0 y (x ◇ x) x)).trans (((congrArg (fun t => t ◇ (x ◇ x)) ((p0 x y x).symm)).trans (congrArg (fun t => t ◇ (x ◇ x)) (p0 x x x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_978_to_3684 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_978_to_3684
