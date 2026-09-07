-- Equation57046 → Equation55268
-- Recorded verdict: true
-- Premise: x * (y * z) = (y * (y * z)) * y
-- Conclusion: x * (y * z) = y * ((x * x) * z)
-- Original submission SHA-256: 2494e22f421c5e2bdc15a2dac9b35e6b0635caf8b795afdcc64ad3e89a410dd3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = (y ◇ (y ◇ z)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = y ◇ ((x ◇ x) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z:G), (y ◇ (y ◇ z)) = (x ◇ (y ◇ z)):=by
    intro x y z
    exact ((h x y z).trans ((h y y z).symm)).symm
  have apc1 : forall (q0 q1 q2 q3:G), (q2 ◇ ((q0 ◇ q1) ◇ q3)) = (q0 ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((apc0 ((q0 ◇ q1) ◇ ((q0 ◇ q1) ◇ q3)) q0 q1).trans ((h q2 (q0 ◇ q1) q3).symm)).symm
  have apc3 : forall (q4 q5 q6 q7 q8:G), (q6 ◇ (q4 ◇ (q4 ◇ q5))) = (q4 ◇ (q4 ◇ q5)):=by
    intro q4 q5 q6 q7 q8
    exact ((congrArg (fun t => q6 ◇ t) (apc1 q4 q5 q7 q8)).symm).trans (((congrArg (fun t => q6 ◇ t) (apc0 q7 (q4 ◇ q5) q8)).symm).trans (apc1 q4 q5 q6 ((q4 ◇ q5) ◇ q8)))
  have apc5 : forall (q9 q10 q11 q12 q13:G), (q11 ◇ (q11 ◇ q12)) = (q9 ◇ (q9 ◇ q10)):=by
    intro q9 q10 q11 q12 q13
    exact (((apc3 q9 q10 q13 (q13 ◇ (q9 ◇ (q9 ◇ q10))) (q13 ◇ (q9 ◇ (q9 ◇ q10)))).symm).trans (((congrArg (fun t => q13 ◇ t) (apc3 q9 q10 (q11 ◇ q12) q9 q9)).symm).trans (apc1 q11 q12 q13 (q9 ◇ (q9 ◇ q10))))).symm
  have apc6 : forall (q14 q15 q16 q17 q18:G), (q16 ◇ (q17 ◇ q18)) = (q14 ◇ (q14 ◇ q15)):=by
    intro q14 q15 q16 q17 q18
    exact (((apc5 q14 q15 q17 q18 q14).symm).trans (apc0 q16 q17 q18)).symm
  exact (apc6 (x ◇ (y ◇ z)) (y ◇ ((x ◇ x) ◇ z)) x y z).trans ((apc6 (x ◇ (y ◇ z)) (y ◇ ((x ◇ x) ◇ z)) y (x ◇ x) z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_57046_to_55268 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_57046_to_55268
