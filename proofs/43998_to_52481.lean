-- Equation43998 → Equation52481
-- Recorded verdict: true
-- Premise: x * y = z * ((z * w) * (y * x))
-- Conclusion: x * y = ((y * (z * x)) * x) * x
-- Original submission SHA-256: e4fa7b731e58d29d1a71acfbd264072664e1416ca5a1e25cda0a79b707184766
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((z ◇ w) ◇ (y ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ (z ◇ x)) ◇ x) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q4 ◇ ((q0 ◇ q1) ◇ (q3 ◇ q2))) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => q4 ◇ t) (congrArg (fun t => t ◇ (q3 ◇ q2)) ((h q0 q1 q4 q0).symm))).symm).trans ((h q2 q3 q4 ((q4 ◇ q0) ◇ (q1 ◇ q0))).symm)
  have apc1 : forall (q5 q6 q7 q8 q9 q10 q11:G), (((q5 ◇ q6) ◇ (q8 ◇ q7)) ◇ q9) = (q8 ◇ q7):=by
    intro q5 q6 q7 q8 q9 q10 q11
    exact (((apc0 q10 q11 q8 q7 q10).symm).trans (((congrArg (fun t => q10 ◇ t) (congrArg (fun t => (q10 ◇ q11) ◇ t) (apc0 q5 q6 q7 q8 q9))).symm).trans ((h ((q5 ◇ q6) ◇ (q8 ◇ q7)) q9 q10 q11).symm))).symm
  have apc4 : forall (q12 q13 q14 q15:G), (q14 ◇ q15) = (q13 ◇ q12):=by
    intro q12 q13 q14 q15
    exact (((apc1 q12 q12 q12 q13 ((((q12 ◇ q12) ◇ (q13 ◇ q12)) ◇ q12) ◇ (q15 ◇ q14)) q12 q12).symm).trans ((h q14 q15 ((q12 ◇ q12) ◇ (q13 ◇ q12)) q12).symm)).symm
  exact (apc4 (x ◇ y) (((y ◇ (z ◇ x)) ◇ x) ◇ x) x y).trans ((apc4 (x ◇ y) (((y ◇ (z ◇ x)) ◇ x) ◇ x) ((y ◇ (z ◇ x)) ◇ x) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43998_to_52481 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43998_to_52481
