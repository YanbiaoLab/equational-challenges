-- Equation11894 → Equation60003
-- Recorded verdict: true
-- Premise: x = x * (((y * z) * w) * (y * y))
-- Conclusion: (x * x) * y = (x * x) * (y * z)
-- Original submission SHA-256: 0d77fa5235d376adc008e9df88702954886323e33043c37bd05f5284e1b430ec
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (((y ◇ z) ◇ w) ◇ (y ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = (x ◇ x) ◇ (y ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q0 ◇ ((q1 ◇ q2) ◇ (q1 ◇ q1))) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q0 ◇ t) (congrArg (fun t => t ◇ (q1 ◇ q1)) ((h (q1 ◇ q2) q0 q0 q0).symm))).symm).trans ((h q0 q1 q2 (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (q3 q4 q5:G), (q4 ◇ ((q3 ◇ q3) ◇ q5)) = q4:=by
    intro q3 q4 q5
    exact ((congrArg (fun t => q4 ◇ t) (apc0 ((q3 ◇ q3) ◇ q5) q3 q3)).symm).trans (apc0 q4 (q3 ◇ q3) q5)
  have apc2 : forall (q6 q7:G), (q7 ◇ (q6 ◇ q6)) = q7:=by
    intro q6 q7
    exact ((congrArg (fun t => q7 ◇ t) (apc1 q6 (q6 ◇ q6) q6)).symm).trans (apc1 q6 q7 ((q6 ◇ q6) ◇ q6))
  have apc3 : forall (q0 q1 q2 q6 q7:G), (q0 ◇ (q1 ◇ q2)) = q0:=by
    intro q0 q1 q2 q6 q7
    exact ((congrArg (fun t => q0 ◇ t) (apc2 q1 (q1 ◇ q2))).symm).trans (apc0 q0 q1 q2)
  have apc4 : forall (q8 q9:G), (q8 ◇ q9) = q8:=by
    intro q8 q9
    exact ((congrArg (fun t => q8 ◇ t) (apc3 q9 q8 q8 q8 q8)).symm).trans (apc3 q8 q9 (q8 ◇ q8) q8 q8)
  exact (apc4 (x ◇ x) y).trans ((apc4 (x ◇ x) (y ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_11894_to_60003 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_11894_to_60003
