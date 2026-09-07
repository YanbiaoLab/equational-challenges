-- Equation5770 → Equation62215
-- Recorded verdict: true
-- Premise: x = x * (y * (z * ((w * u) * y)))
-- Conclusion: (x * y) * z = ((x * x) * z) * z
-- Original submission SHA-256: 441b04414130a0a1ac0a39a21112d8836398d81513155a896ed3bbf8d17f837e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = x ◇ (y ◇ (z ◇ ((w ◇ u) ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = ((x ◇ x) ◇ z) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ ((q1 ◇ q0) ◇ q3)) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) ((h ((q1 ◇ q0) ◇ q3) q3 (q0 ◇ q0) q1 q0).symm)).symm).trans ((h q2 ((q1 ◇ q0) ◇ q3) q3 q0 q0).symm)
  have apc1 : forall (q4 q5:G), (q4 ◇ q5) = q4:=by
    intro q4 q5
    exact ((congrArg (fun t => q4 ◇ t) (apc0 q4 q4 q5 ((q4 ◇ q4) ◇ q5))).symm).trans ((h q4 q5 (q4 ◇ q4) q4 q4).symm)
  exact (calc
    ((x ◇ y) ◇ z) = x:=(congrArg (fun t => t ◇ z) (apc1 x y)).trans (apc1 x z)
    _ = (((x ◇ x) ◇ z) ◇ z):=(((congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ z) (apc1 x x))).trans (congrArg (fun t => t ◇ z) (apc1 x z))).trans (apc1 x z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5770_to_62215 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5770_to_62215
