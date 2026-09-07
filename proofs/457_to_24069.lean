-- Equation457 → Equation24069
-- Recorded verdict: true
-- Premise: x = x * (y * (z * (z * w)))
-- Conclusion: x = ((x * y) * x) * ((z * z) * x)
-- Original submission SHA-256: d9918942a38c07343e4e8d645ac4dc1d6c01a1e95509474b647fbb5e19669e97
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (y ◇ (z ◇ (z ◇ w)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ y) ◇ x) ◇ ((z ◇ z) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc1 : forall (q0 q1:G), (q0 ◇ q1) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => q0 ◇ t) ((h q1 q0 q0 q0).symm)).symm).trans ((h q0 q1 q0 (q0 ◇ q0)).symm)
  exact (calc
    x = x:=rfl
    _ = (((x ◇ y) ◇ x) ◇ ((z ◇ z) ◇ x)):=(((((congrArg (fun t => t ◇ ((z ◇ z) ◇ x)) (congrArg (fun t => t ◇ x) (apc1 x y))).trans (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => t ◇ x) (apc1 z z)))).trans (congrArg (fun t => t ◇ (z ◇ x)) (apc1 x x))).trans (congrArg (fun t => x ◇ t) (apc1 z x))).trans (apc1 x z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_457_to_24069 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_457_to_24069
