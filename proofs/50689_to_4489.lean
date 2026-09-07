-- Equation50689 → Equation4489
-- Recorded verdict: true
-- Premise: x * y = (y * ((x * z) * w)) * u
-- Conclusion: x * (y * y) = (z * x) * x
-- Original submission SHA-256: 941810cc49f410b37d65e3aad50586b382066d51c2cc43f500c7a997e1c3b31c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (y ◇ ((x ◇ z) ◇ w)) ◇ u
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ y) = (z ◇ x) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), ((q3 ◇ (q0 ◇ q2)) ◇ q1) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => q3 ◇ t) ((h q0 q2 q0 q0 q0).symm))).symm).trans ((h q2 q3 ((q0 ◇ q0) ◇ q0) q0 q1).symm)
  have apc2 : forall (q4 q5 q6 q7 q8 q9:G), (q6 ◇ q7) = (q4 ◇ q5):=by
    intro q4 q5 q6 q7 q8 q9
    exact ((apc0 (q4 ◇ q5) q8 q6 q7).symm).trans ((((congrArg (fun t => t ◇ q8) (congrArg (fun t => q7 ◇ t) (congrArg (fun t => t ◇ q6) (apc0 q9 q9 q4 q5)))).symm).trans ((h (q5 ◇ (q9 ◇ q4)) q7 q9 q6 q8).symm)).trans (apc0 q9 q7 q4 q5))
  exact (apc2 (x ◇ (y ◇ y)) ((z ◇ x) ◇ x) x (y ◇ y) (x ◇ (y ◇ y)) (x ◇ (y ◇ y))).trans ((apc2 (x ◇ (y ◇ y)) ((z ◇ x) ◇ x) (z ◇ x) x (x ◇ (y ◇ y)) (x ◇ (y ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50689_to_4489 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50689_to_4489
