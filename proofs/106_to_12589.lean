-- Equation106 → Equation12589
-- Recorded verdict: true
-- Premise: x = x ◇ ((y ◇ x) ◇ z)
-- Conclusion: x = x ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ y)
-- Original submission SHA-256: 72a83502a007385d7f2bf1c8bd10bedd4e52d32b945766df20400b8d2bc02f5d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ x) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = x ◇ ((x ◇ (x ◇ (x ◇ x))) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have p0 : forall (q0 q1:G), (q0 ◇ (q1 ◇ q0)) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => q0 ◇ t) ((h (q1 ◇ q0) q0 q0).symm)).symm).trans ((h q0 q1 ((q0 ◇ (q1 ◇ q0)) ◇ q0)).symm)
  exact (h x x y).trans ((congrArg (fun t => x ◇ t) (congrArg (fun t => t ◇ y) (congrArg (fun t => x ◇ t) (p0 x x)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_106_to_12589 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_106_to_12589
