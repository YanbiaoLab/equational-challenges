-- Equation1683 → Equation263
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ ((x ◇ x) ◇ z)
-- Conclusion: x = ((x ◇ y) ◇ y) ◇ x
-- Original submission SHA-256: 054afe9d1f1d9644e857a5a0e215dda3ea8d8718aa6e225a1107173ce81e53e5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ ((x ◇ x) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((x ◇ y) ◇ y) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1:G), ((q1 ◇ q0) ◇ q0) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => (q1 ◇ q0) ◇ t) ((h q0 q0 q0).symm)).symm).trans ((h q0 q1 ((q0 ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q2:G), (q2 ◇ q2) = q2:=by
    intro q2
    exact ((congrArg (fun t => t ◇ q2) (apc0 q2 q2)).symm).trans (apc0 q2 (q2 ◇ q2))
  have apc3 : forall (q3 q4:G), (q3 ◇ (q3 ◇ q4)) = q3:=by
    intro q3 q4
    exact ((congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ q4) (apc1 q3))).symm).trans (((congrArg (fun t => t ◇ ((q3 ◇ q3) ◇ q4)) (apc1 q3)).symm).trans ((h q3 q3 q4).symm))
  have apc4 : forall (q5 q6:G), (q6 ◇ q5) = q6:=by
    intro q5 q6
    exact (((apc3 q6 q5).symm).trans (((congrArg (fun t => t ◇ (q6 ◇ q5)) (apc3 q6 q5)).symm).trans (apc0 (q6 ◇ q5) q6))).symm
  have apc5 : forall (x y z:G), y = x:=by
    intro x y z
    exact (((((congrArg (fun t => (y ◇ x) ◇ t) (congrArg (fun t => t ◇ z) (apc4 x x))).trans (congrArg (fun t => (y ◇ x) ◇ t) (apc4 z x))).trans (congrArg (fun t => t ◇ x) (apc4 x y))).trans (apc4 x y)).symm).trans ((((h x y z).symm).trans (h x x x)).trans ((((congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => t ◇ x) (apc4 x x))).trans (congrArg (fun t => t ◇ (x ◇ x)) (apc4 x x))).trans (congrArg (fun t => x ◇ t) (apc4 x x))).trans (apc4 x x)))
  exact (apc5 x x x).trans ((apc5 x (((x ◇ y) ◇ y) ◇ x) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1683_to_263 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_1683_to_263
