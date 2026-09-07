-- Equation39392 → Equation46505
-- Recorded verdict: true
-- Premise: x = (((y * y) * (z * w)) * w) * x
-- Conclusion: x * y = (z * y) * (x * (z * y))
-- Original submission SHA-256: e86b58e2013f66586eea8a45badd6845dfbb6cc57059af0c999d6975e4fb30f2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ y) ◇ (z ◇ w)) ◇ w) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ y) ◇ (x ◇ (z ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), (q0 ◇ q1) = q1:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q1) ((h q0 (q0 ◇ q0) (q0 ◇ q0) (q0 ◇ q0)).symm)).symm).trans ((h q1 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q0 q0).symm)
  exact (calc
    (x ◇ y) = y:=apc0 x y
    _ = ((z ◇ y) ◇ (x ◇ (z ◇ y))):=((((congrArg (fun t => (z ◇ y) ◇ t) (congrArg (fun t => x ◇ t) (apc0 z y))).trans (congrArg (fun t => (z ◇ y) ◇ t) (apc0 x y))).trans (congrArg (fun t => t ◇ y) (apc0 z y))).trans (apc0 y y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_39392_to_46505 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_39392_to_46505
