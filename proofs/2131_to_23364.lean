-- Equation2131 → Equation23364
-- Recorded verdict: true
-- Premise: x = ((y * y) * x) * (z * y)
-- Conclusion: x = ((y * x) * y) * (y * (x * z))
-- Original submission SHA-256: 5e66e68c1b746aaf3c172edffbe3a48dfc6691b12ead8cc6cc1b6e2f8f066012
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ x) ◇ (z ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ y) ◇ (y ◇ (x ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc1 : forall (q0 q1 q2:G), ((q0 ◇ q1) ◇ (q2 ◇ ((q0 ◇ q0) ◇ q0))) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q2 ◇ ((q0 ◇ q0) ◇ q0))) (congrArg (fun t => t ◇ q1) ((h q0 q0 (q0 ◇ q0)).symm))).symm).trans ((h q1 ((q0 ◇ q0) ◇ q0) q2).symm)
  have apc2 : forall (q3 q4 q5:G), (((q3 ◇ q3) ◇ q4) ◇ (q5 ◇ (q3 ◇ q3))) = q4:=by
    intro q3 q4 q5
    exact ((congrArg (fun t => ((q3 ◇ q3) ◇ q4) ◇ t) (congrArg (fun t => q5 ◇ t) ((h (q3 ◇ q3) q3 q3).symm))).symm).trans (apc1 (q3 ◇ q3) q4 q5)
  have apc3 : forall (q6 q7 q8:G), (((q7 ◇ q7) ◇ q8) ◇ q6) = q8:=by
    intro q6 q7 q8
    exact ((congrArg (fun t => ((q7 ◇ q7) ◇ q8) ◇ t) ((h q6 q7 q7).symm)).symm).trans (apc2 q7 q8 ((q7 ◇ q7) ◇ q6))
  have apc4 : forall (q9 q10 q11:G), ((q9 ◇ q9) ◇ (q11 ◇ (q9 ◇ q9))) = q10:=by
    intro q9 q10 q11
    exact ((congrArg (fun t => t ◇ (q11 ◇ (q9 ◇ q9))) (apc3 q10 q9 (q9 ◇ q9))).symm).trans ((h q10 (q9 ◇ q9) q11).symm)
  exact ((apc4 x x x).symm).trans (apc4 x (((y ◇ x) ◇ y) ◇ (y ◇ (x ◇ z))) x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_2131_to_23364 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_2131_to_23364
