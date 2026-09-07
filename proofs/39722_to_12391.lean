-- Equation39722 → Equation12391
-- Recorded verdict: true
-- Premise: x = (((y * z) * (w * w)) * z) * x
-- Conclusion: x = y * (((z * z) * y) * (y * x))
-- Original submission SHA-256: 6b03ce418fb86bf770378ae03a4273e6e34db646c653b5062f5f04a6580e18da
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ z) ◇ (w ◇ w)) ◇ z) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (((z ◇ z) ◇ y) ◇ (y ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), ((q0 ◇ q0) ◇ q1) = q1:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q1) ((h (q0 ◇ q0) q0 (q0 ◇ q0) q0).symm)).symm).trans ((h q1 (q0 ◇ (q0 ◇ q0)) (q0 ◇ q0) q0).symm)
  have apc1 : forall (q2 q3:G), (q2 ◇ q3) = q3:=by
    intro q2 q3
    exact ((congrArg (fun t => t ◇ q3) (apc0 (q2 ◇ q2) q2)).symm).trans ((h q3 q2 q2 q2).symm)
  exact (calc
    x = x:=rfl
    _ = (y ◇ (((z ◇ z) ◇ y) ◇ (y ◇ x))):=(((((congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ (y ◇ x)) (congrArg (fun t => t ◇ y) (apc1 z z)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => (z ◇ y) ◇ t) (apc1 y x)))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ x) (apc1 z y)))).trans (congrArg (fun t => y ◇ t) (apc1 y x))).trans (apc1 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_39722_to_12391 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_39722_to_12391
