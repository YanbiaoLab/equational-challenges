-- Equation10810 → Equation62146
-- Recorded verdict: true
-- Premise: x = y * ((z * w) * ((u * z) * y))
-- Conclusion: (x * y) * y = ((z * y) * x) * y
-- Original submission SHA-256: 734156bd8d6803c4cfcadffce50cb33148eea1d096270a80bf80d157db380ba4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ ((z ◇ w) ◇ ((u ◇ z) ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ y = ((z ◇ y) ◇ x) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), (((q0 ◇ q2) ◇ (q5 ◇ q3)) ◇ q1) = q4:=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => ((q0 ◇ q2) ◇ (q5 ◇ q3)) ◇ t) ((h q1 (q5 ◇ q3) q2 q5 q0).symm)).symm).trans ((h q4 ((q0 ◇ q2) ◇ (q5 ◇ q3)) q5 q3 q2).symm)
  have apc1 : forall (q6 q7 q8 q9 q10:G), (((q7 ◇ q9) ◇ q6) ◇ q8) = q10:=by
    intro q6 q7 q8 q9 q10
    exact ((congrArg (fun t => t ◇ q8) (congrArg (fun t => (q7 ◇ q9) ◇ t) (apc0 q6 q6 q6 q6 q6 q6))).symm).trans (apc0 q7 q8 q9 q6 q10 ((q6 ◇ q6) ◇ (q6 ◇ q6)))
  have apc2 : forall (q6 q7 q8 q9 q10:G), (((q10 ◇ q10) ◇ q10) ◇ q10) = (((q7 ◇ q9) ◇ q6) ◇ q8):=by
    intro q6 q7 q8 q9 q10
    exact ((apc1 q6 q7 q8 q9 q10).trans ((apc1 q10 q10 q10 q10 q10).symm)).symm
  have apc3 : forall (q11 q12 q13 q14:G), (((q14 ◇ q14) ◇ q14) ◇ q14) = ((q11 ◇ q12) ◇ q13):=by
    intro q11 q12 q13 q14
    exact (((congrArg (fun t => t ◇ q13) (congrArg (fun t => t ◇ q12) (apc1 q11 q11 q11 q11 q11))).symm).trans ((apc2 q12 ((q11 ◇ q11) ◇ q11) q13 q11 q14).symm)).symm
  exact ((apc3 x y y ((x ◇ y) ◇ y)).symm).trans (apc3 (z ◇ y) x y ((x ◇ y) ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_10810_to_62146 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_10810_to_62146
