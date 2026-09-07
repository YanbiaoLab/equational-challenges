-- Equation53406 → Equation48711
-- Recorded verdict: true
-- Premise: x * y = (((y * z) * z) * w) * z
-- Conclusion: x * x = ((y * z) * z) * (y * z)
-- Original submission SHA-256: 7f83a6823c78e4af9a2254f0624f02457d1cd7419236848e23f169fb657f9686
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (((y ◇ z) ◇ z) ◇ w) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ z) ◇ z) ◇ (y ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2 q3:G), (((q3 ◇ q3) ◇ q0) ◇ q3) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q3) (congrArg (fun t => t ◇ q0) ((apc0 (q2 ◇ q3) q3 q0 q0).symm))).symm).trans ((h q1 q2 q3 q0).symm)
  exact ((apc1 (((y ◇ z) ◇ z) ◇ (y ◇ z)) x x (x ◇ x)).symm).trans (apc1 (((y ◇ z) ◇ z) ◇ (y ◇ z)) ((y ◇ z) ◇ z) (y ◇ z) (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53406_to_48711 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53406_to_48711
