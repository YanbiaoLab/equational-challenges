-- Equation3015 → Equation56387
-- Recorded verdict: true
-- Premise: x = ((y * (z * z)) * z) * x
-- Conclusion: x * (y * z) = (w * w) * (z * z)
-- Original submission SHA-256: f3fabe88781d4ccf01ff4a2fa00734e9ed517891ff7924fbdd21e46b1f2e84f2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ (z ◇ z)) ◇ z) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (w ◇ w) ◇ (z ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), (q1 ◇ q0) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q0) ((h q1 q0 (q1 ◇ q1)).symm)).symm).trans ((h q0 (q0 ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1))) q1).symm)
  exact (calc
    (x ◇ (y ◇ z)) = z:=(congrArg (fun t => x ◇ t) (apc0 z y)).trans (apc0 z x)
    _ = ((w ◇ w) ◇ (z ◇ z)):=(((congrArg (fun t => t ◇ (z ◇ z)) (apc0 w w)).trans (congrArg (fun t => w ◇ t) (apc0 z z))).trans (apc0 z w)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3015_to_56387 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3015_to_56387
