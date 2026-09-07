-- Equation5765 → Equation27612
-- Recorded verdict: true
-- Premise: x = x * (y * (z * ((w * w) * y)))
-- Conclusion: x = ((x * (y * y)) * z) * (y * z)
-- Original submission SHA-256: f500d9a2c099c436c660fd752e8e154508c5347d194e8bf9d0cf6ec651e54f38
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (y ◇ (z ◇ ((w ◇ w) ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ (y ◇ y)) ◇ z) ◇ (y ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ ((q0 ◇ q0) ◇ q2)) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q1 ◇ t) ((h ((q0 ◇ q0) ◇ q2) q2 (q0 ◇ q0) q0).symm)).symm).trans ((h q1 ((q0 ◇ q0) ◇ q2) q2 q0).symm)
  have apc2 : forall (q3 q4:G), (q3 ◇ q4) = q3:=by
    intro q3 q4
    exact ((congrArg (fun t => q3 ◇ t) (apc0 q3 q4 ((q3 ◇ q3) ◇ q4))).symm).trans ((h q3 q4 (q3 ◇ q3) q3).symm)
  exact (calc
    x = x:=rfl
    _ = (((x ◇ (y ◇ y)) ◇ z) ◇ (y ◇ z)):=(((((congrArg (fun t => t ◇ (y ◇ z)) (congrArg (fun t => t ◇ z) (congrArg (fun t => x ◇ t) (apc2 y y)))).trans (congrArg (fun t => t ◇ (y ◇ z)) (congrArg (fun t => t ◇ z) (apc2 x y)))).trans (congrArg (fun t => t ◇ (y ◇ z)) (apc2 x z))).trans (congrArg (fun t => x ◇ t) (apc2 y z))).trans (apc2 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5765_to_27612 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5765_to_27612
