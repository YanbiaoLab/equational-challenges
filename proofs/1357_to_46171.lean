-- Equation1357 → Equation46171
-- Recorded verdict: true
-- Premise: x = y * (((z * x) * z) * x)
-- Conclusion: x * y = (x * y) * (y * (z * y))
-- Original submission SHA-256: 56509b1b660079499335765fcfc7046b7c4bfa6386247116360a288f32e976f0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (((z ◇ x) ◇ z) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (x ◇ y) ◇ (y ◇ (z ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (((q1 ◇ q0) ◇ q1) ◇ q0) = (q2 ◇ q0):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => q2 ◇ t) ((h q0 ((q0 ◇ (((q1 ◇ q0) ◇ q1) ◇ q0)) ◇ q0) q1).symm)).symm).trans ((h (((q1 ◇ q0) ◇ q1) ◇ q0) q2 q0).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q2 ◇ q0) = (q0 ◇ q0):=by
    intro q0 q1 q2
    exact ((apc0 q0 q1 q2).symm).trans (apc0 q0 q1 q0)
  have apc3 : forall (q0 q3 q2:G), (q2 ◇ (q0 ◇ q3)) = q3:=by
    intro q0 q3 q2
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ q3) ((h q0 ((((q0 ◇ q0) ◇ q0) ◇ q0) ◇ q3) q0).symm))).symm).trans ((h q3 q2 (((q0 ◇ q0) ◇ q0) ◇ q0)).symm)
  exact (calc
    (x ◇ y) = (y ◇ y):=apc1 y x x
    _ = (z ◇ y):=(apc1 y x z).symm
    _ = ((x ◇ y) ◇ (y ◇ (z ◇ y))):=(apc3 y (z ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1357_to_46171 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_1357_to_46171
