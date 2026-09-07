-- Equation12467 → Equation18865
-- Recorded verdict: true
-- Premise: x = y * (((z * w) * x) * (u * x))
-- Conclusion: x = (x * y) * ((z * x) * (w * x))
-- Original submission SHA-256: 5cb4b7d0446e4249d7bf97046f1d95d8f39a731c76833a28f6316f3d45bbb3f0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ (((z ◇ w) ◇ x) ◇ (u ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ y) ◇ ((z ◇ x) ◇ (w ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (q3 ◇ ((q0 ◇ q2) ◇ (q1 ◇ q2))) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ (q1 ◇ q2)) (congrArg (fun t => t ◇ q2) ((h q0 q0 q0 q0 q0).symm)))).symm).trans ((h q2 q3 q0 (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) q1).symm)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ y) ◇ ((z ◇ x) ◇ (w ◇ x))):=(apc0 z w x (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_12467_to_18865 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_12467_to_18865
