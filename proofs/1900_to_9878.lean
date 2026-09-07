-- Equation1900 → Equation9878
-- Recorded verdict: true
-- Premise: x = (y * (x * y)) * (z * x)
-- Conclusion: x = y * ((z * w) * (z * (z * x)))
-- Original submission SHA-256: 3d75b867c0b6f0a5a4594fe05338eac05bd43bea4dbd0c72dc4ffe4998632c40
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ y)) ◇ (z ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((z ◇ w) ◇ (z ◇ (z ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (((q2 ◇ q0) ◇ q0) ◇ (q3 ◇ (q1 ◇ (q0 ◇ q1)))) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ (q3 ◇ (q1 ◇ (q0 ◇ q1)))) (congrArg (fun t => (q2 ◇ q0) ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h (q1 ◇ (q0 ◇ q1)) (q2 ◇ q0) q3).symm)
  have apc1 : forall (q4 q5 q6:G), (q5 ◇ (q6 ◇ (q4 ◇ ((q5 ◇ q5) ◇ q4)))) = (q4 ◇ ((q5 ◇ q5) ◇ q4)):=by
    intro q4 q5 q6
    exact ((congrArg (fun t => t ◇ (q6 ◇ (q4 ◇ ((q5 ◇ q5) ◇ q4)))) ((h q5 q5 q5).symm)).symm).trans (apc0 (q5 ◇ q5) q4 q5 q6)
  have apc4 : forall (q0 q2 q7:G), ((q7 ◇ ((q2 ◇ q0) ◇ q7)) ◇ q0) = (q2 ◇ q0):=by
    intro q0 q2 q7
    exact ((congrArg (fun t => (q7 ◇ ((q2 ◇ q0) ◇ q7)) ◇ t) ((h q0 q0 q2).symm)).symm).trans ((h (q2 ◇ q0) q7 (q0 ◇ (q0 ◇ q0))).symm)
  have apc8 : forall (q8 q9 q10:G), ((q10 ◇ (q8 ◇ q10)) ◇ ((q8 ◇ q10) ◇ q9)) = (q9 ◇ ((q8 ◇ q10) ◇ q9)):=by
    intro q8 q9 q10
    exact ((congrArg (fun t => t ◇ ((q8 ◇ q10) ◇ q9)) (congrArg (fun t => q10 ◇ t) (apc4 q10 q8 q9))).symm).trans (apc4 ((q8 ◇ q10) ◇ q9) q9 q10)
  have apc9 : forall (q11 q12:G), (q11 ◇ ((q11 ◇ q12) ◇ q11)) = q11:=by
    intro q11 q12
    exact ((apc8 q11 q11 q12).symm).trans ((h q11 q12 (q11 ◇ q12)).symm)
  have apc11 : forall (q13 q14:G), (q13 ◇ (q14 ◇ q13)) = q13:=by
    intro q13 q14
    exact (((congrArg (fun t => q13 ◇ t) (congrArg (fun t => q14 ◇ t) (apc9 q13 q13))).symm).trans (apc1 q13 q13 q14)).trans (apc9 q13 q13)
  have apc13 : forall (q4 q5 q6 q13 q14:G), (q5 ◇ (q6 ◇ q4)) = q4:=by
    intro q4 q5 q6 q13 q14
    exact ((congrArg (fun t => q5 ◇ t) (congrArg (fun t => q6 ◇ t) (apc11 q4 (q5 ◇ q5)))).symm).trans ((apc1 q4 q5 q6).trans (apc11 q4 (q5 ◇ q5)))
  exact (calc
    x = x:=rfl
    _ = (y ◇ ((z ◇ w) ◇ (z ◇ (z ◇ x)))):=((congrArg (fun t => y ◇ t) (congrArg (fun t => (z ◇ w) ◇ t) (apc13 x z z (z ◇ (z ◇ x)) (z ◇ (z ◇ x))))).trans (apc13 x y (z ◇ w) (y ◇ ((z ◇ w) ◇ x)) (y ◇ ((z ◇ w) ◇ x)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1900_to_9878 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_1900_to_9878
