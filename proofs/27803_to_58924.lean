-- Equation27803 → Equation58924
-- Recorded verdict: true
-- Premise: x = ((y * (x * z)) * y) * (w * x)
-- Conclusion: (x * y) * z = z * (w * (u * z))
-- Original submission SHA-256: 7f8dc6da1d3ffd05fa4e8705e8729c1b50aeef0746cdb48c10d6c19dd34b634a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (x ◇ z)) ◇ y) ◇ (w ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = z ◇ (w ◇ (u ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3:G), (((q2 ◇ ((q0 ◇ q1) ◇ q3)) ◇ q2) ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => ((q2 ◇ ((q0 ◇ q1) ◇ q3)) ◇ q2) ◇ t) ((h q1 q0 q0 q0).symm)).symm).trans ((h (q0 ◇ q1) q2 q3 ((q0 ◇ (q1 ◇ q0)) ◇ q0)).symm)
  have apc1 : forall (q4 q5 q6 q7 q8:G), ((q8 ◇ ((q4 ◇ (q8 ◇ q5)) ◇ q4)) ◇ q7) = (q6 ◇ q7):=by
    intro q4 q5 q6 q7 q8
    exact ((congrArg (fun t => t ◇ q7) (congrArg (fun t => t ◇ ((q4 ◇ (q8 ◇ q5)) ◇ q4)) ((h q8 q4 q5 (q6 ◇ q7)).symm))).symm).trans (apc0 q6 q7 ((q4 ◇ (q8 ◇ q5)) ◇ q4) q8)
  have apc2 : forall (q9 q10 q11 q12:G), ((q10 ◇ q11) ◇ (q11 ◇ q9)) = (q12 ◇ (q11 ◇ q9)):=by
    intro q9 q10 q11 q12
    exact ((congrArg (fun t => t ◇ (q11 ◇ q9)) (apc1 q12 q9 q10 q11 q11)).symm).trans (apc0 q12 (q11 ◇ q9) q11 q12)
  have apc3 : forall (q13 q14 q15:G), (q13 ◇ (q14 ◇ q15)) = q15:=by
    intro q13 q14 q15
    exact ((apc2 q15 (q14 ◇ (q15 ◇ q13)) q14 q13).symm).trans ((h q15 q14 q13 q14).symm)
  have apc4 : forall (q0 q1 q2 q3 q13 q14 q15:G), ((q3 ◇ q2) ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1 q2 q3 q13 q14 q15
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => t ◇ q2) (apc3 q2 (q0 ◇ q1) q3))).symm).trans (apc0 q0 q1 q2 q3)
  have apc6 : forall (q0 q1 q2 q3 q13 q14 q15:G), (q1 ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1 q2 q3 q13 q14 q15
    exact (((apc4 q0 q1 q2 q3 q13 q14 q15).symm).trans (apc4 q1 q1 q2 q3 q13 q14 q15)).symm
  have apc7 : forall (q16 q17 q18:G), ((q18 ◇ q17) ◇ q16) = (q16 ◇ q16):=by
    intro q16 q17 q18
    exact ((apc6 q16 q16 q16 q16 q16 q16 q16).trans ((apc4 q16 q16 q17 q18 q16 q16 q16).symm)).symm
  exact (calc
    ((x ◇ y) ◇ z) = (z ◇ z):=apc7 z y x
    _ = (z ◇ (w ◇ (u ◇ z))):=(congrArg (fun t => z ◇ t) (apc3 w u z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_27803_to_58924 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_27803_to_58924
