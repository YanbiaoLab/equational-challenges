-- Equation51754 → Equation43281
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * (w * u)) * z
-- Conclusion: x * y = z * (w * ((u * v) * v))
-- Original submission SHA-256: 7ecfd1b18c9e2e15dc11a149100e790df00d61b9443f035ca401dfde45929f82
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ x) ◇ (w ◇ u)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = z ◇ (w ◇ ((u ◇ v) ◇ v))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have apc0 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc2 : forall (q0 q1 q2 q3 q4:G), (((q3 ◇ q3) ◇ (q1 ◇ q0)) ◇ q3) = (q2 ◇ q2):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => t ◇ q3) (congrArg (fun t => t ◇ (q1 ◇ q0)) (apc0 q3 q2 q0 q0 q0))).symm).trans ((h q2 q4 q3 q1 q0).symm)).trans (apc0 q2 q4 (q2 ◇ q4) (q2 ◇ q4) (q2 ◇ q4))
  have apc3 : forall (q5 q6 q7:G), (q7 ◇ q5) = (q6 ◇ q6):=by
    intro q5 q6 q7
    exact (h q7 q5 q7 q5 q5).trans (apc2 q5 q5 q6 q7 q5)
  exact (apc3 y (x ◇ y) x).trans ((apc3 (w ◇ ((u ◇ v) ◇ v)) (x ◇ y) z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51754_to_43281 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51754_to_43281
