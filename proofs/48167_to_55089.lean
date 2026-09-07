-- Equation48167 → Equation55089
-- Recorded verdict: true
-- Premise: x * y = (y * (z * w)) * (u * x)
-- Conclusion: x * (y * y) = y * ((y * y) * y)
-- Original submission SHA-256: 2b5b4ca1ce8a92433dad1bb5a8588a1c41bf1111620f9c56f822cffcfaea7b11
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (y ◇ (z ◇ w)) ◇ (u ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (y ◇ y) = y ◇ ((y ◇ y) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc5 : forall (x y z w u:G), ((y ◇ (z ◇ w)) ◇ (u ◇ x)) = ((y ◇ (x ◇ x)) ◇ (x ◇ x)):=by
    intro x y z w u
    exact ((h x y z w u).symm).trans (h x y x x x)
  have apc6 : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((apc5 q0 q1 q0 q0 q0).symm).trans ((h q0 q1 q0 q0 q0).symm)
  have apc11 : forall (q2 q3 q4 q5 q6 q7:G), ((q6 ◇ (q7 ◇ q5)) ◇ (q3 ◇ q4)) = ((q2 ◇ q3) ◇ q6):=by
    intro q2 q3 q4 q5 q6 q7
    exact ((congrArg (fun t => (q6 ◇ (q7 ◇ q5)) ◇ t) ((h q3 q4 q2 q2 q2).symm)).symm).trans ((h (q2 ◇ q3) q6 q7 q5 (q4 ◇ (q2 ◇ q2))).symm)
  have apc12 : forall (q8 q9 q10 q11:G), ((q8 ◇ q9) ◇ q11) = (q10 ◇ q11):=by
    intro q8 q9 q10 q11
    exact ((apc11 q8 q9 q10 q8 q11 q8).symm).trans ((h q10 q11 q8 q8 q9).symm)
  have apc13 : forall (q8 q10 q11 q9:G), (q10 ◇ q11) = (q8 ◇ q11):=by
    intro q8 q10 q11 q9
    exact ((apc12 q8 q9 q10 q11).symm).trans (apc12 q8 q9 q8 q11)
  have apc14 : forall (q12 q13 q14:G), (q13 ◇ q14) = (q13 ◇ q12):=by
    intro q12 q13 q14
    exact (((apc6 q13 q12).symm).trans (((congrArg (fun t => t ◇ (q13 ◇ q13)) (apc13 q12 q14 (q13 ◇ q13) q12)).symm).trans (apc6 q13 q14))).symm
  have apc15 : forall (q15 q16 q17 q18:G), (q17 ◇ q15) = (q16 ◇ q18):=by
    intro q15 q16 q17 q18
    exact ((apc14 q15 q17 q18).symm).trans (apc13 q16 q17 q18 q15)
  exact (apc15 (y ◇ y) (x ◇ (y ◇ y)) x (y ◇ ((y ◇ y) ◇ y))).trans ((apc15 ((y ◇ y) ◇ y) (x ◇ (y ◇ y)) y (y ◇ ((y ◇ y) ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48167_to_55089 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48167_to_55089
