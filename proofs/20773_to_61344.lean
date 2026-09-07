-- Equation20773 → Equation61344
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ (((z ◇ x) ◇ w) ◇ w)
-- Conclusion: (x ◇ y) ◇ z = (x ◇ (x ◇ w)) ◇ u
-- Original submission SHA-256: 4e609187b232f2be9ebb1df36c319165d50cf805731caab29283d5ddd414e601
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ x) ◇ (((z ◇ x) ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = (x ◇ (x ◇ w)) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc4 : forall (q0 q1 q2 q3 q4:G), ((q4 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)) ◇ ((q1 ◇ q3) ◇ q3)) = (((q2 ◇ q1) ◇ q0) ◇ q0):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => (q4 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)) ◇ t) (congrArg (fun t => t ◇ q3) (congrArg (fun t => t ◇ q3) ((h q1 q0 q2 q0).symm)))).symm).trans ((h (((q2 ◇ q1) ◇ q0) ◇ q0) q4 (q0 ◇ q1) q3).symm)
  have apc5 : forall (q5 q6 q7 q8:G), (q6 ◇ ((q6 ◇ q8) ◇ q8)) = (((q7 ◇ q6) ◇ q5) ◇ q5):=by
    intro q5 q6 q7 q8
    exact ((congrArg (fun t => t ◇ ((q6 ◇ q8) ◇ q8)) ((h q6 q5 q7 q5).symm)).symm).trans (apc4 q5 q6 q7 q8 (q5 ◇ q6))
  have apc7 : forall (q5 q6 q7 q8:G), (((q7 ◇ q6) ◇ q5) ◇ q5) = (((q6 ◇ q6) ◇ q6) ◇ q6):=by
    intro q5 q6 q7 q8
    exact ((apc5 q5 q6 q7 q5).symm).trans (apc5 q6 q6 q6 q5)
  have apc8 : forall (q9 q10 q11 q12:G), (((q10 ◇ (q12 ◇ q11)) ◇ q9) ◇ q9) = q11:=by
    intro q9 q10 q11 q12
    exact ((apc5 q9 (q12 ◇ q11) q10 q9).symm).trans ((h q11 q12 q12 q9).symm)
  have apc9 : forall (q13 q14:G), q14 = q13:=by
    intro q13 q14
    exact (((apc8 q13 q13 q13 ((q13 ◇ q13) ◇ q13)).symm).trans (((congrArg (fun t => t ◇ q13) (congrArg (fun t => t ◇ q13) (congrArg (fun t => q13 ◇ t) (apc7 q14 q13 q13 q13)))).symm).trans (apc8 q13 q13 q14 ((q13 ◇ q13) ◇ q14)))).symm
  exact (apc9 ((x ◇ y) ◇ z) ((x ◇ y) ◇ z)).trans ((apc9 ((x ◇ y) ◇ z) ((x ◇ (x ◇ w)) ◇ u)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20773_to_61344 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20773_to_61344
