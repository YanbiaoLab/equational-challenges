-- Equation51147 → Equation59767
-- Recorded verdict: true
-- Premise: x * y = (z * ((w * u) * y)) * z
-- Conclusion: (x * y) * z = z * ((z * y) * y)
-- Original submission SHA-256: d49190c9e31a8069f68ef6596c06038edf4065902fee3f061c389b5a9afd777a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ ((w ◇ u) ◇ y)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = z ◇ ((z ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w u:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w u
    exact ((h x y z w u).trans ((h y y z w u).symm)).symm
  have apc2 : forall (q0 q1 q2:G), (q2 ◇ q2) = (q0 ◇ q1):=by
    intro q0 q1 q2
    exact (apc0 (q2 ◇ ((q0 ◇ q0) ◇ q1)) q2 q0 q0 q0).trans ((h q0 q1 q2 q0 q0).symm)
  exact ((apc2 (x ◇ y) z ((x ◇ y) ◇ z)).symm).trans (apc2 z ((z ◇ y) ◇ y) ((x ◇ y) ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51147_to_59767 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51147_to_59767
