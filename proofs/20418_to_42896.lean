-- Equation20418 → Equation42896
-- Recorded verdict: true
-- Premise: x = (y * z) * ((w * (w * x)) * x)
-- Conclusion: x * y = y * (z * ((w * z) * y))
-- Original submission SHA-256: 0fe9bb641e9076b82ec0fe9a71781e57cbd507ecfe3d701b95b7119d3d68da63
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ ((w ◇ (w ◇ x)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (z ◇ ((w ◇ z) ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ (q0 ◇ q0)) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q1 ◇ q2) ◇ t) (congrArg (fun t => t ◇ q0) ((h q0 q0 (q0 ◇ q0) q0).symm))).symm).trans ((h q0 q1 q2 (q0 ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (q3 q4:G), (q3 ◇ (q4 ◇ q4)) = q4:=by
    intro q3 q4
    exact ((congrArg (fun t => t ◇ (q4 ◇ q4)) (apc0 q3 q3 q3)).symm).trans (apc0 q4 (q3 ◇ q3) (q3 ◇ q3))
  have apc2 : forall (q5 q6:G), (q6 ◇ q5) = (q5 ◇ q5):=by
    intro q5 q6
    exact ((congrArg (fun t => q6 ◇ t) (apc1 (q5 ◇ q5) q5)).symm).trans (apc1 q6 (q5 ◇ q5))
  exact (calc
    (x ◇ y) = (y ◇ y):=apc2 y x
    _ = ((w ◇ z) ◇ y):=(apc2 y (w ◇ z)).symm
    _ = (y ◇ (((w ◇ z) ◇ y) ◇ ((w ◇ z) ◇ y))):=(apc1 y ((w ◇ z) ◇ y)).symm
    _ = (y ◇ (z ◇ ((w ◇ z) ◇ y))):=(congrArg (fun t => y ◇ t) (apc2 ((w ◇ z) ◇ y) z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20418_to_42896 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20418_to_42896
