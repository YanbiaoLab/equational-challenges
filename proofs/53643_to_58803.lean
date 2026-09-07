-- Equation53643 → Equation58803
-- Recorded verdict: true
-- Premise: x * y = (((z * z) * w) * x) * w
-- Conclusion: (x * y) * z = y * (y * (w * x))
-- Original submission SHA-256: aff289de12f6b9cadc4c0a375547fa3f7e9c2d9d93ec7a624a3c91598db578f0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (((z ◇ z) ◇ w) ◇ x) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = y ◇ (y ◇ (w ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc10 : forall (q0 q1 q2 q3 q4:G), (((((q1 ◇ q1) ◇ q2) ◇ q0) ◇ q3) ◇ q2) = (q3 ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact (((congrArg (fun t => t ◇ q2) (congrArg (fun t => t ◇ q3) ((h ((q1 ◇ q1) ◇ q2) q0 q1 q2).symm))).symm).trans ((h q3 q4 ((q1 ◇ q1) ◇ q2) q2).symm)).trans (apc0 q3 q4 (q3 ◇ q4) (q3 ◇ q4))
  have apc11 : forall (q5 q6 q7:G), ((q6 ◇ q5) ◇ q7) = (q7 ◇ q7):=by
    intro q5 q6 q7
    exact ((congrArg (fun t => t ◇ q7) ((h q6 q5 q5 q7).symm)).symm).trans (apc10 q6 q5 q7 q7 q5)
  have apc13 : forall (q8 q9 q10:G), (q10 ◇ q10) = (q9 ◇ q8):=by
    intro q8 q9 q10
    exact ((h q9 q8 q8 q10).trans (apc11 q9 ((q8 ◇ q8) ◇ q10) q10)).symm
  exact ((apc13 z (x ◇ y) ((x ◇ y) ◇ z)).symm).trans (apc13 (y ◇ (w ◇ x)) y ((x ◇ y) ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53643_to_58803 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53643_to_58803
