-- Equation29725 → Equation44212
-- Recorded verdict: true
-- Premise: x = (y * (y * (z * (z * w)))) * x
-- Conclusion: x * x = y * ((x * (x * x)) * x)
-- Original submission SHA-256: 1e4647a83c3c2111b83f3e80158ea564c802586b10de5b5e787d50b48da559b0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (y ◇ (z ◇ (z ◇ w)))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = y ◇ ((x ◇ (x ◇ x)) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), (((q1 ◇ (q1 ◇ (q2 ◇ (q2 ◇ q0)))) ◇ (q5 ◇ (q5 ◇ q3))) ◇ q4) = q4:=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => t ◇ q4) ((h ((q1 ◇ (q1 ◇ (q2 ◇ (q2 ◇ q0)))) ◇ (q5 ◇ (q5 ◇ q3))) q1 q2 q0).symm)).symm).trans ((h q4 (q1 ◇ (q1 ◇ (q2 ◇ (q2 ◇ q0)))) q5 q3).symm)
  have apc1 : forall (q6 q7 q8 q9 q10 q11 q12 q13:G), ((q8 ◇ (q8 ◇ q6)) ◇ q7) = q7:=by
    intro q6 q7 q8 q9 q10 q11 q12 q13
    exact ((congrArg (fun t => t ◇ q7) (apc0 q9 q10 q11 q12 (q8 ◇ (q8 ◇ q6)) q13)).symm).trans (((congrArg (fun t => t ◇ q7) (apc0 q9 q10 q11 q12 (((q10 ◇ (q10 ◇ (q11 ◇ (q11 ◇ q9)))) ◇ (q13 ◇ (q13 ◇ q12))) ◇ (q8 ◇ (q8 ◇ q6))) q13)).symm).trans ((h q7 ((q10 ◇ (q10 ◇ (q11 ◇ (q11 ◇ q9)))) ◇ (q13 ◇ (q13 ◇ q12))) q8 q6).symm))
  have apc2 : forall (q14 q15 q16 q17:G), (q14 ◇ q15) = q15:=by
    intro q14 q15 q16 q17
    exact ((congrArg (fun t => t ◇ q15) (apc1 q16 q14 q17 ((q17 ◇ (q17 ◇ q16)) ◇ q14) ((q17 ◇ (q17 ◇ q16)) ◇ q14) ((q17 ◇ (q17 ◇ q16)) ◇ q14) ((q17 ◇ (q17 ◇ q16)) ◇ q14) ((q17 ◇ (q17 ◇ q16)) ◇ q14))).symm).trans (((congrArg (fun t => t ◇ q15) (apc1 q16 ((q17 ◇ (q17 ◇ q16)) ◇ q14) q17 q16 q16 q16 q16 q16)).symm).trans (apc1 q14 q15 (q17 ◇ (q17 ◇ q16)) q16 q16 q16 q16 q16))
  exact (calc
    (x ◇ x) = x:=apc2 x x (x ◇ x) (x ◇ x)
    _ = (y ◇ ((x ◇ (x ◇ x)) ◇ x)):=((((congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ x) (congrArg (fun t => x ◇ t) (apc2 x x (x ◇ x) (x ◇ x))))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ x) (apc2 x x (x ◇ x) (x ◇ x))))).trans (congrArg (fun t => y ◇ t) (apc2 x x (x ◇ x) (x ◇ x)))).trans (apc2 y x (y ◇ x) (y ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_29725_to_44212 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_29725_to_44212
