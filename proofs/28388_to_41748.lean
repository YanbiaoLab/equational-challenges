-- Equation28388 → Equation41748
-- Recorded verdict: true
-- Premise: x = (((x * x) * x) * y) * (z * w)
-- Conclusion: x * y = x * (x * (y * (z * x)))
-- Original submission SHA-256: 7f61b2cae37678883d74ce06287c8ec62f5ffed8a9f7967f28807b552f4c59a0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (((x ◇ x) ◇ x) ◇ y) ◇ (z ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ (x ◇ (y ◇ (z ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), ((q0 ◇ q2) ◇ (q3 ◇ q1)) = ((q0 ◇ q0) ◇ q0):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ (q3 ◇ q1)) (congrArg (fun t => t ◇ q2) ((h q0 ((q0 ◇ q0) ◇ q0) (q0 ◇ q0) q0).symm))).symm).trans ((h ((q0 ◇ q0) ◇ q0) q2 q3 q1).symm)
  have apc1 : forall (q4 q5 q6:G), ((q5 ◇ q6) ◇ q4) = ((q5 ◇ q5) ◇ q5):=by
    intro q4 q5 q6
    exact ((congrArg (fun t => (q5 ◇ q6) ◇ t) ((h q4 q4 q4 q4).symm)).symm).trans (apc0 q5 (q4 ◇ q4) q6 (((q4 ◇ q4) ◇ q4) ◇ q4))
  have apc2 : forall (q0 q7 q2:G), ((((q7 ◇ q7) ◇ q7) ◇ q2) ◇ q0) = q7:=by
    intro q0 q7 q2
    exact ((congrArg (fun t => (((q7 ◇ q7) ◇ q7) ◇ q2) ◇ t) ((h q0 q0 q0 q0).symm)).symm).trans ((h q7 q2 (((q0 ◇ q0) ◇ q0) ◇ q0) (q0 ◇ q0)).symm)
  have apc3 : forall (q8 q9 q10 q11:G), (q8 ◇ q10) = (q8 ◇ q9):=by
    intro q8 q9 q10 q11
    exact ((congrArg (fun t => t ◇ q10) (apc2 q11 q8 (q8 ◇ q9))).symm).trans (((congrArg (fun t => t ◇ q10) (congrArg (fun t => t ◇ q11) (congrArg (fun t => t ◇ (q8 ◇ q9)) (apc1 (q8 ◇ q9) q8 q9)))).symm).trans (apc2 q10 (q8 ◇ q9) q11))
  exact (apc3 x (x ◇ y) y (x ◇ y)).trans ((apc3 x (x ◇ y) (x ◇ (y ◇ (z ◇ x))) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_28388_to_41748 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_28388_to_41748
