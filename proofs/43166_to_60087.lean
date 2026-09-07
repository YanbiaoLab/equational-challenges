-- Equation43166 → Equation60087
-- Recorded verdict: true
-- Premise: x * y = z * (w * ((x * u) * u))
-- Conclusion: (x * x) * y = (z * x) * (w * w)
-- Original submission SHA-256: 062792cff9888a75b18c438aa7c516a25e1ed2fc02c32cb84f3c09085a1c1b4a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (w ◇ ((x ◇ u) ◇ u))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ x) ◇ y = (z ◇ x) ◇ (w ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q4 ◇ (q0 ◇ q1)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => q4 ◇ t) ((h q0 q1 q0 (q2 ◇ ((q0 ◇ q0) ◇ q0)) q0).symm)).symm).trans ((h q2 q3 q4 q0 ((q0 ◇ q0) ◇ q0)).symm)
  have apc1 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc2 : forall (q0 q1 q2 q3 q4:G), (q2 ◇ q2) = (q0 ◇ q0):=by
    intro q0 q1 q2 q3 q4
    exact ((apc1 q2 q3 (q2 ◇ q3) (q2 ◇ q3) (q2 ◇ q3)).symm).trans (((apc0 q0 q1 q2 q3 q4).symm).trans (apc0 q0 q1 q0 q0 q4))
  exact (calc
    ((x ◇ x) ◇ y) = ((x ◇ x) ◇ (x ◇ x)):=apc1 (x ◇ x) y w w w
    _ = ((z ◇ x) ◇ (z ◇ x)):=apc2 (z ◇ x) w (x ◇ x) w w
    _ = ((z ◇ x) ◇ (w ◇ w)):=(apc1 (z ◇ x) (w ◇ w) w w w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43166_to_60087 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43166_to_60087
