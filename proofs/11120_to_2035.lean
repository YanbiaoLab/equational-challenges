-- Equation11120 → Equation2035
-- Recorded verdict: true
-- Premise: x = y * ((x * (z * x)) * (z * y))
-- Conclusion: x = ((x * x) * x) * (x * x)
-- Original submission SHA-256: 7a5798245f13e0afbb45c5a67536a083e36bf004fcba51766588659476d718cb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ (z ◇ x)) ◇ (z ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = ((x ◇ x) ◇ x) ◇ (x ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x
  have apc0 : forall (q0 q1 q2 q3:G), (((q0 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q3)) ◇ ((q2 ◇ (q3 ◇ q2)) ◇ q0)) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => ((q0 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q3)) ◇ t) (congrArg (fun t => (q2 ◇ (q3 ◇ q2)) ◇ t) ((h q0 q3 q1).symm))).symm).trans ((h q2 ((q0 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q3)) q3).symm)
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ (q2 ◇ ((q0 ◇ (q1 ◇ q0)) ◇ q2))) ◇ q0) = q2:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q1 ◇ (q2 ◇ ((q0 ◇ (q1 ◇ q0)) ◇ q2))) ◇ t) ((h q0 (q2 ◇ ((q0 ◇ (q1 ◇ q0)) ◇ q2)) q1).symm)).symm).trans ((h q2 (q1 ◇ (q2 ◇ ((q0 ◇ (q1 ◇ q0)) ◇ q2))) (q0 ◇ (q1 ◇ q0))).symm)
  have apc4 : forall (q4 q5 q6 q7 q8:G), (((q6 ◇ q5) ◇ ((q4 ◇ (q5 ◇ ((q6 ◇ (q4 ◇ q6)) ◇ q5))) ◇ q8)) ◇ ((q7 ◇ (q8 ◇ q7)) ◇ q6)) = q7:=by
    intro q4 q5 q6 q7 q8
    exact ((congrArg (fun t => t ◇ ((q7 ◇ (q8 ◇ q7)) ◇ q6)) (congrArg (fun t => t ◇ ((q4 ◇ (q5 ◇ ((q6 ◇ (q4 ◇ q6)) ◇ q5))) ◇ q8)) (congrArg (fun t => q6 ◇ t) (apc1 q6 q4 q5)))).symm).trans (apc0 q6 (q4 ◇ (q5 ◇ ((q6 ◇ (q4 ◇ q6)) ◇ q5))) q7 q8)
  have apc5 : forall (x y z:G), (y ◇ ((x ◇ (z ◇ x)) ◇ (z ◇ y))) = (x ◇ ((x ◇ (x ◇ x)) ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc6 : forall (q9 q10 q11:G), (((q11 ◇ q9) ◇ q9) ◇ ((q10 ◇ (q11 ◇ q10)) ◇ q11)) = q10:=by
    intro q9 q10 q11
    exact ((congrArg (fun t => t ◇ ((q10 ◇ (q11 ◇ q10)) ◇ q11)) (congrArg (fun t => (q11 ◇ q9) ◇ t) (apc1 q11 q9 q9))).symm).trans (apc4 q9 q9 q11 q10 q11)
  have apc7 : forall (q12:G), (q12 ◇ ((q12 ◇ (q12 ◇ q12)) ◇ (q12 ◇ q12))) = q12:=by
    intro q12
    exact ((apc5 q12 q12 q12).symm).trans ((h q12 q12 q12).symm)
  have apc8 : forall (q13 q14:G), (q14 ◇ ((q13 ◇ (q14 ◇ q13)) ◇ q14)) = q13:=by
    intro q13 q14
    exact ((congrArg (fun t => t ◇ ((q13 ◇ (q14 ◇ q13)) ◇ q14)) (apc7 q14)).symm).trans (((congrArg (fun t => t ◇ ((q13 ◇ (q14 ◇ q13)) ◇ q14)) (congrArg (fun t => t ◇ ((q14 ◇ (q14 ◇ q14)) ◇ (q14 ◇ q14))) (apc7 q14))).symm).trans (apc6 ((q14 ◇ (q14 ◇ q14)) ◇ (q14 ◇ q14)) q13 q14))
  have apc9 : forall (q15 q16:G), ((q16 ◇ q15) ◇ q15) = q16:=by
    intro q15 q16
    exact ((congrArg (fun t => t ◇ q15) (congrArg (fun t => q16 ◇ t) (apc8 q15 q16))).symm).trans (apc1 q15 q16 q16)
  have apc10 : forall (q12 q15 q16:G), (q12 ◇ q12) = q12:=by
    intro q12 q15 q16
    exact ((congrArg (fun t => q12 ◇ t) (apc9 (q12 ◇ q12) q12)).symm).trans (apc7 q12)
  exact (calc
    x = x:=rfl
    _ = (((x ◇ x) ◇ x) ◇ (x ◇ x)):=((((congrArg (fun t => t ◇ (x ◇ x)) (congrArg (fun t => t ◇ x) (apc10 x (x ◇ x) (x ◇ x)))).trans (congrArg (fun t => t ◇ (x ◇ x)) (apc10 x (x ◇ x) (x ◇ x)))).trans (congrArg (fun t => x ◇ t) (apc10 x (x ◇ x) (x ◇ x)))).trans (apc10 x (x ◇ x) (x ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_11120_to_2035 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_11120_to_2035
