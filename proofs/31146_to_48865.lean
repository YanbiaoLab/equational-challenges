-- Equation31146 → Equation48865
-- Recorded verdict: true
-- Premise: x = (x * ((y * z) * (x * w))) * w
-- Conclusion: x * y = ((x * z) * z) * (z * y)
-- Original submission SHA-256: b772f899c6bd58ab51e5a80e867f5f0dce5984384d57efe1475a5f1e01fd21c5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ ((y ◇ z) ◇ (x ◇ w))) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((x ◇ z) ◇ z) ◇ (z ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ q0) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q0) (congrArg (fun t => q1 ◇ t) ((h q2 q0 q0 (q1 ◇ q0)).symm))).symm).trans ((h q1 q2 ((q0 ◇ q0) ◇ (q2 ◇ (q1 ◇ q0))) q0).symm)
  have apc1 : forall (q3 q4 q5:G), (q3 ◇ q5) = (q3 ◇ q4):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => t ◇ q5) (apc0 q3 q3 q4)).symm).trans (apc0 q5 (q3 ◇ q4) q3)
  have apc2 : forall (q3 q4 q5:G), (q3 ◇ q4) = (q3 ◇ q3):=by
    intro q3 q4 q5
    exact ((apc1 q3 q4 q5).symm).trans (apc1 q3 q3 q5)
  have apc4 : forall (q0 q1 q2 q3 q4 q5:G), ((q1 ◇ q1) ◇ q0) = q1:=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => t ◇ q0) (apc2 q1 q2 (q1 ◇ q2))).symm).trans (apc0 q0 q1 q2)
  exact (calc
    (x ◇ y) = (x ◇ x):=apc2 x y (x ◇ y)
    _ = (((x ◇ z) ◇ z) ◇ (z ◇ y)):=(((congrArg (fun t => t ◇ (z ◇ y)) (congrArg (fun t => t ◇ z) (apc2 x z (x ◇ z)))).trans (congrArg (fun t => t ◇ (z ◇ y)) (apc4 z x ((x ◇ x) ◇ z) ((x ◇ x) ◇ z) ((x ◇ x) ◇ z) ((x ◇ x) ◇ z)))).trans (apc2 x (z ◇ y) (x ◇ (z ◇ y)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_31146_to_48865 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_31146_to_48865
