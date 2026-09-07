-- Equation25788 → Equation54336
-- Recorded verdict: true
-- Premise: x = (x * ((x * y) * z)) * (z * z)
-- Conclusion: x * (y * z) = x * (y * (y * w))
-- Original submission SHA-256: 8829def19af2196883886108bd099e38bb43cb9aabadb1eaf7c04654ea6263b0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ ((x ◇ y) ◇ z)) ◇ (z ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = x ◇ (y ◇ (y ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), ((q1 ◇ q1) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = q1:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (congrArg (fun t => q1 ◇ t) ((h q1 q0 q0).symm))).symm).trans ((h q1 ((q1 ◇ q0) ◇ q0) (q0 ◇ q0)).symm)
  have apc2 : forall (q2 q3:G), ((q3 ◇ q3) ◇ (q2 ◇ q2)) = q3:=by
    intro q2 q3
    exact ((congrArg (fun t => (q3 ◇ q3) ◇ t) (apc0 q2 (q2 ◇ q2))).symm).trans (apc0 (q2 ◇ q2) q3)
  have apc3 : forall (q4 q5:G), (q4 ◇ (q5 ◇ q5)) = (q4 ◇ q4):=by
    intro q4 q5
    exact ((congrArg (fun t => t ◇ (q5 ◇ q5)) (apc2 q4 q4)).symm).trans (apc2 q5 (q4 ◇ q4))
  have apc5 : forall (q6 q7:G), (q7 ◇ q7) = (q7 ◇ q6):=by
    intro q6 q7
    exact (((congrArg (fun t => q7 ◇ t) (apc2 q6 q6)).symm).trans (((congrArg (fun t => q7 ◇ t) (apc3 (q6 ◇ q6) q6)).symm).trans (apc3 q7 (q6 ◇ q6)))).symm
  exact ((apc5 (y ◇ z) x).symm).trans (apc5 (y ◇ (y ◇ w)) x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_25788_to_54336 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_25788_to_54336
