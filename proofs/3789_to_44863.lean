-- Equation3789 → Equation44863
-- Recorded verdict: true
-- Premise: x * y = (z * x) * (y * x)
-- Conclusion: x * y = z * ((z * (z * z)) * z)
-- Original submission SHA-256: 408b4a772e45115dbc76cc2a08e1592be7dc03d943538cb30ece393f339e023b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ x) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ ((z ◇ (z ◇ z)) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z:G), ((z ◇ x) ◇ (y ◇ x)) = ((x ◇ x) ◇ (y ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q1 ◇ q0)) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((apc0 q0 q1 q0).symm).trans ((h q0 q1 q0).symm)
  have apc2 : forall (q2 q3 q4:G), ((q2 ◇ q3) ◇ (q4 ◇ (q3 ◇ q2))) = ((q3 ◇ q2) ◇ q4):=by
    intro q2 q3 q4
    exact ((congrArg (fun t => t ◇ (q4 ◇ (q3 ◇ q2))) ((h q2 q3 q2).symm)).symm).trans ((h (q3 ◇ q2) q4 (q2 ◇ q2)).symm)
  have apc3 : forall (q5 q6 q7:G), ((q7 ◇ q6) ◇ (q5 ◇ q6)) = ((q6 ◇ q7) ◇ (q6 ◇ q7)):=by
    intro q5 q6 q7
    exact (((congrArg (fun t => (q6 ◇ q7) ◇ t) ((h q6 q7 q5).symm)).symm).trans (apc2 q6 q7 (q5 ◇ q6))).symm
  have apc5 : forall (q5 q6 q7 q0 q1:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ q1):=by
    intro q5 q6 q7 q0 q1
    exact ((apc3 q1 q0 q0).symm).trans (apc1 q0 q1)
  have apc6 : forall (q5 q6 q7 q0 q1:G), (q0 ◇ q1) = (q0 ◇ q0):=by
    intro q5 q6 q7 q0 q1
    exact ((apc5 q5 q6 q7 q0 q1).symm).trans (apc5 q5 q6 q7 q0 q0)
  have apc7 : forall (q8 q9 q10:G), ((q8 ◇ q8) ◇ (q8 ◇ q8)) = (q8 ◇ q8):=by
    intro q8 q9 q10
    exact (((congrArg (fun t => t ◇ (q8 ◇ q9)) (apc6 (q8 ◇ q9) (q8 ◇ q9) (q8 ◇ q9) q8 q9)).trans (congrArg (fun t => (q8 ◇ q8) ◇ t) (apc6 (q8 ◇ q9) (q8 ◇ q9) (q8 ◇ q9) q8 q9))).symm).trans ((((apc3 q10 q8 q9).symm).trans ((h q8 q10 q9).symm)).trans (apc6 (q8 ◇ q10) (q8 ◇ q10) (q8 ◇ q10) q8 q10))
  have apc8 : forall (q11 q12 q1:G), ((q12 ◇ q11) ◇ q1) = (q11 ◇ q11):=by
    intro q11 q12 q1
    exact (((((((congrArg (fun t => ((q11 ◇ q11) ◇ (q12 ◇ q11)) ◇ t) (apc6 (q1 ◇ (q12 ◇ q11)) (q1 ◇ (q12 ◇ q11)) (q1 ◇ (q12 ◇ q11)) q1 (q12 ◇ q11))).trans (congrArg (fun t => t ◇ (q1 ◇ q1)) (apc6 ((q11 ◇ q11) ◇ (q12 ◇ q11)) ((q11 ◇ q11) ◇ (q12 ◇ q11)) ((q11 ◇ q11) ◇ (q12 ◇ q11)) (q11 ◇ q11) (q12 ◇ q11)))).trans (congrArg (fun t => t ◇ (q1 ◇ q1)) (apc7 q11 ((q11 ◇ q11) ◇ (q11 ◇ q11)) ((q11 ◇ q11) ◇ (q11 ◇ q11))))).trans (apc6 ((q11 ◇ q11) ◇ (q1 ◇ q1)) ((q11 ◇ q11) ◇ (q1 ◇ q1)) ((q11 ◇ q11) ◇ (q1 ◇ q1)) (q11 ◇ q11) (q1 ◇ q1))).trans (apc7 q11 ((q11 ◇ q11) ◇ (q11 ◇ q11)) ((q11 ◇ q11) ◇ (q11 ◇ q11)))).symm).trans (((congrArg (fun t => t ◇ (q1 ◇ (q12 ◇ q11))) (apc0 q11 q12 q11)).symm).trans ((h (q12 ◇ q11) q1 (q11 ◇ q11)).symm))).symm
  have apc9 : forall (q13 q14 q15:G), (q14 ◇ q14) = (q13 ◇ q13):=by
    intro q13 q14 q15
    exact ((apc8 q14 q14 q15).symm).trans (((congrArg (fun t => t ◇ q15) (apc6 q13 q13 q13 q14 q13)).symm).trans (apc8 q13 q14 q15))
  exact (calc
    (x ◇ y) = (x ◇ x):=apc6 x x x x y
    _ = (z ◇ z):=apc9 z x x
    _ = (z ◇ ((z ◇ (z ◇ z)) ◇ z)):=(apc6 x x x z ((z ◇ (z ◇ z)) ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3789_to_44863 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3789_to_44863
