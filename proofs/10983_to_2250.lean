-- Equation10983 → Equation2250
-- Recorded verdict: true
-- Premise: x = x * ((y * (z * y)) * (y * z))
-- Conclusion: x = (x * (x * (y * z))) * y
-- Original submission SHA-256: f750f2437751ce2a17eda7ead219a956669d1066cf5a8c20d16e02f1270d9679
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ ((y ◇ (z ◇ y)) ◇ (y ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (x ◇ (y ◇ z))) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc5 : forall (q0 q1 q2 q3:G), (q2 ◇ ((((q0 ◇ (q1 ◇ q0)) ◇ (q0 ◇ q1)) ◇ q3) ◇ (((q0 ◇ (q1 ◇ q0)) ◇ (q0 ◇ q1)) ◇ q3))) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ (((q0 ◇ (q1 ◇ q0)) ◇ (q0 ◇ q1)) ◇ q3)) (congrArg (fun t => ((q0 ◇ (q1 ◇ q0)) ◇ (q0 ◇ q1)) ◇ t) ((h q3 q0 q1).symm)))).symm).trans ((h q2 ((q0 ◇ (q1 ◇ q0)) ◇ (q0 ◇ q1)) q3).symm)
  have apc6 : forall (q4 q5 q6 q7:G), (q7 ◇ (((q4 ◇ (q5 ◇ q4)) ◇ (q4 ◇ q5)) ◇ q6)) = q7:=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => q7 ◇ t) (apc5 q4 q5 (((q4 ◇ (q5 ◇ q4)) ◇ (q4 ◇ q5)) ◇ q6) q6)).symm).trans (((congrArg (fun t => q7 ◇ t) (apc5 q4 q5 ((((q4 ◇ (q5 ◇ q4)) ◇ (q4 ◇ q5)) ◇ q6) ◇ ((((q4 ◇ (q5 ◇ q4)) ◇ (q4 ◇ q5)) ◇ q6) ◇ (((q4 ◇ (q5 ◇ q4)) ◇ (q4 ◇ q5)) ◇ q6))) q6)).symm).trans ((h q7 (((q4 ◇ (q5 ◇ q4)) ◇ (q4 ◇ q5)) ◇ q6) (((q4 ◇ (q5 ◇ q4)) ◇ (q4 ◇ q5)) ◇ q6)).symm))
  have apc7 : forall (q8 q9 q10 q11 q12:G), (q10 ◇ ((q8 ◇ q8) ◇ q9)) = q10:=by
    intro q8 q9 q10 q11 q12
    exact ((congrArg (fun t => q10 ◇ t) (congrArg (fun t => t ◇ q9) (congrArg (fun t => t ◇ q8) (apc6 q11 q12 q8 q8)))).symm).trans (((congrArg (fun t => q10 ◇ t) (congrArg (fun t => t ◇ q9) (congrArg (fun t => (q8 ◇ (((q11 ◇ (q12 ◇ q11)) ◇ (q11 ◇ q12)) ◇ q8)) ◇ t) ((h q8 q11 q12).symm)))).symm).trans (apc6 q8 ((q11 ◇ (q12 ◇ q11)) ◇ (q11 ◇ q12)) q9 q10))
  have apc8 : forall (q13 q14:G), (q14 ◇ (q13 ◇ q13)) = q14:=by
    intro q13 q14
    exact ((congrArg (fun t => q14 ◇ t) (apc7 q13 q13 (q13 ◇ q13) q13 q13)).symm).trans (apc7 q13 ((q13 ◇ q13) ◇ q13) q14 q13 q13)
  have apc9 : forall (q15 q16:G), (q15 ◇ q16) = q15:=by
    intro q15 q16
    exact ((congrArg (fun t => q15 ◇ t) (apc8 q16 q16)).symm).trans (((congrArg (fun t => q15 ◇ t) (apc8 q16 (q16 ◇ (q16 ◇ q16)))).symm).trans ((h q15 q16 q16).symm))
  exact ((apc9 x (x ◇ (y ◇ z))).symm).trans ((apc9 (x ◇ (x ◇ (y ◇ z))) y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_10983_to_2250 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_10983_to_2250
