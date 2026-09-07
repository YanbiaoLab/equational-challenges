-- Equation43177 → Equation48048
-- Recorded verdict: true
-- Premise: x * y = z * (w * ((y * y) * u))
-- Conclusion: x * y = (y * (x * z)) * (y * z)
-- Original submission SHA-256: 081bc0958f4745aa312f35bca42275f2e251d68c144a50622c66663cd0beb321
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (w ◇ ((y ◇ y) ◇ u))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ (x ◇ z)) ◇ (y ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q4 ◇ (q0 ◇ q1)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => q4 ◇ t) ((h q0 q1 q0 (q3 ◇ q3) q0).symm)).symm).trans ((h q2 q3 q4 q0 ((q1 ◇ q1) ◇ q0)).symm)
  have apc1 : forall (x y z w u:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w u
    exact ((h x y z w u).trans ((h y y z w u).symm)).symm
  have apc2 : forall (q5 q6 q7 q8:G), ((q5 ◇ q6) ◇ (q5 ◇ q6)) = (q7 ◇ q8):=by
    intro q5 q6 q7 q8
    exact (apc1 q5 (q5 ◇ q6) q5 q5 q5).trans (apc0 q5 q6 q7 q8 q5)
  exact ((apc2 (x ◇ y) ((y ◇ (x ◇ z)) ◇ (y ◇ z)) x y).symm).trans (apc2 (x ◇ y) ((y ◇ (x ◇ z)) ◇ (y ◇ z)) (y ◇ (x ◇ z)) (y ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43177_to_48048 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43177_to_48048
