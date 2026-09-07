-- Equation53596 → Equation56018
-- Recorded verdict: true
-- Premise: x * y = (((z * z) * x) * y) * w
-- Conclusion: x * (y * y) = (z * y) * (w * x)
-- Original submission SHA-256: 231c33bdefc3f9e800692425adb1604486df73ad5ec918f75dbfb07dc63dd826
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (((z ◇ z) ◇ x) ◇ y) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = (z ◇ y) ◇ (w ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (((q0 ◇ q0) ◇ q2) ◇ q1) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q1) ((h (q0 ◇ q0) q2 q0 q3).symm)).symm).trans ((h q2 q3 (q0 ◇ q0) q1).symm)
  have apc3 : forall (q4 q5 q6 q7:G), ((q6 ◇ q4) ◇ q5) = (q6 ◇ q7):=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => t ◇ q5) (apc0 q4 q7 q6 q4)).symm).trans ((h q6 q7 q4 q5).symm)
  have apc4 : forall (q4 q7 q8:G), ((q8 ◇ q8) ◇ q7) = (q7 ◇ q4):=by
    intro q4 q7 q8
    exact (((apc0 (q8 ◇ q8) q4 q7 q4).symm).trans ((h (q8 ◇ q8) q7 q8 q4).symm)).symm
  have apc6 : forall (q9 q10 q11 q12:G), (q11 ◇ q9) = (q10 ◇ q12):=by
    intro q9 q10 q11 q12
    exact ((apc4 q9 q11 q10).symm).trans (apc3 q10 q11 q10 q12)
  have apc7 : forall (q9 q10 q12 q11:G), (q10 ◇ q12) = (q9 ◇ q9):=by
    intro q9 q10 q12 q11
    exact ((apc6 q9 q10 q11 q12).symm).trans (apc6 q9 q9 q11 q9)
  exact (apc7 (x ◇ (y ◇ y)) x (y ◇ y) (x ◇ (y ◇ y))).trans ((apc7 (x ◇ (y ◇ y)) (z ◇ y) (w ◇ x) (x ◇ (y ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53596_to_56018 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53596_to_56018
