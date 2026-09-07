-- Equation48361 → Equation45926
-- Recorded verdict: true
-- Premise: x * y = (z * (z * z)) * (x * x)
-- Conclusion: x * x = (x * x) * (y * (z * y))
-- Original submission SHA-256: 04dbc380d9752b2fc2f157dfbdc8854972b071a9cd0abd29b3938aa63a022b01
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ (z ◇ z)) ◇ (x ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (x ◇ x) ◇ (y ◇ (z ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => t ◇ (q0 ◇ q0)) (apc0 q1 (q1 ◇ q1) q0)).symm).trans ((h q0 q2 q1).symm)).trans (apc0 q0 q2 (q0 ◇ q2))
  exact (calc
    (x ◇ x) = (x ◇ x):=rfl
    _ = ((x ◇ x) ◇ (y ◇ (z ◇ y))):=(((congrArg (fun t => (x ◇ x) ◇ t) (apc0 y (z ◇ y) (y ◇ (z ◇ y)))).trans (apc0 (x ◇ x) (y ◇ y) ((x ◇ x) ◇ (y ◇ y)))).trans (apc1 x x ((x ◇ x) ◇ (x ◇ x)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48361_to_45926 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48361_to_45926
