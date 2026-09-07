-- Equation3764 → Equation54651
-- Recorded verdict: true
-- Premise: x * y = (y * y) * (z * x)
-- Conclusion: x * (y * z) = w * (u * (x * u))
-- Original submission SHA-256: 6fe9cef3d29e047015edc85928e5696c758fd6a3fd057289a9b869b3b4e08bc5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ y) ◇ (z ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = w ◇ (u ◇ (x ◇ u))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2:G), ((q0 ◇ q0) ◇ (q2 ◇ q1)) = (q1 ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q2 ◇ q1)) ((h q0 q0 q0).symm)).symm).trans ((h q1 (q0 ◇ q0) q2).symm)
  have apc1 : forall (q3 q4 q5:G), (q4 ◇ (q3 ◇ (q3 ◇ q3))) = (q4 ◇ (q3 ◇ q3)):=by
    intro q3 q4 q5
    exact (((apc0 q3 q4 q5).symm).trans ((((congrArg (fun t => t ◇ (q5 ◇ q4)) ((h q3 q3 q3).symm)).symm).trans (apc0 (q3 ◇ q3) q4 q5)).trans (congrArg (fun t => q4 ◇ t) (apc0 q3 q3 q3)))).symm
  have apc2 : forall (q6 q7:G), (q7 ◇ (q6 ◇ q6)) = (q6 ◇ (q7 ◇ q7)):=by
    intro q6 q7
    exact ((apc0 q6 q7 q7).symm).trans ((((apc1 q7 (q6 ◇ q6) q6).symm).trans (apc0 q6 (q7 ◇ q7) q7)).trans (apc0 q7 q6 q6))
  have apc4 : forall (q8 q9:G), (q8 ◇ (q9 ◇ q9)) = (q8 ◇ q9):=by
    intro q8 q9
    exact ((apc0 q9 q8 q8).symm).trans ((h q8 q9 q8).symm)
  have apc6 : forall (q8 q9 q6 q7:G), (q7 ◇ q6) = (q6 ◇ q7):=by
    intro q8 q9 q6 q7
    exact ((apc4 q7 q6).symm).trans ((apc2 q6 q7).trans (apc4 q6 q7))
  have apc7 : forall (q10 q11:G), (((q11 ◇ q11) ◇ (q11 ◇ q11)) ◇ q10) = (q10 ◇ q11):=by
    intro q10 q11
    exact ((apc6 (q10 ◇ ((q11 ◇ q11) ◇ (q11 ◇ q11))) (q10 ◇ ((q11 ◇ q11) ◇ (q11 ◇ q11))) ((q11 ◇ q11) ◇ (q11 ◇ q11)) q10).symm).trans (((apc2 q10 (q11 ◇ q11)).symm).trans ((h q10 q11 q10).symm))
  have apc8 : forall (q12 q13 q14:G), ((q12 ◇ q12) ◇ (q13 ◇ q14)) = (q12 ◇ q13):=by
    intro q12 q13 q14
    exact (((congrArg (fun t => (((q12 ◇ q12) ◇ (q12 ◇ q12)) ◇ q12) ◇ t) (apc6 (q14 ◇ q13) (q14 ◇ q13) q13 q14)).trans (congrArg (fun t => t ◇ (q13 ◇ q14)) (apc7 q12 q12))).symm).trans ((((congrArg (fun t => t ◇ (q14 ◇ q13)) (apc7 ((q12 ◇ q12) ◇ (q12 ◇ q12)) q12)).symm).trans ((h q13 ((q12 ◇ q12) ◇ (q12 ◇ q12)) q14).symm)).trans (((apc6 (q13 ◇ ((q12 ◇ q12) ◇ (q12 ◇ q12))) (q13 ◇ ((q12 ◇ q12) ◇ (q12 ◇ q12))) ((q12 ◇ q12) ◇ (q12 ◇ q12)) q13).trans (apc7 q13 q12)).trans (apc6 (q13 ◇ q12) (q13 ◇ q12) q12 q13)))
  have apc9 : forall (q15 q16 q17:G), (q16 ◇ q17) = (q15 ◇ q16):=by
    intro q15 q16 q17
    exact ((apc8 q16 q17 q15).symm).trans ((h q15 q16 q17).symm)
  exact (apc9 (u ◇ (x ◇ u)) x (y ◇ z)).trans (apc9 w (u ◇ (x ◇ u)) x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3764_to_54651 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3764_to_54651
