-- Equation23998 → Equation60911
-- Recorded verdict: true
-- Premise: x = ((x * x) * x) * ((y * y) * y)
-- Conclusion: (x * x) * y = (x * (z * w)) * u
-- Original submission SHA-256: 2e14d2e6972462f773c423a0504fd92e1361061f40e1678f3ef69cd55e9621a9
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((x ◇ x) ◇ x) ◇ ((y ◇ y) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ x) ◇ y = (x ◇ (z ◇ w)) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1:G), ((q0 ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q1) ◇ q1)) = ((q0 ◇ q0) ◇ q0):=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ ((q1 ◇ q1) ◇ q1)) (congrArg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) ((h q0 q0).symm))).symm).trans ((h ((q0 ◇ q0) ◇ q0) q1).symm)
  have apc1 : forall (q2 q3:G), ((q3 ◇ ((q3 ◇ q3) ◇ q3)) ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) = ((q3 ◇ q3) ◇ q3):=by
    intro q2 q3
    exact ((congrArg (fun t => (q3 ◇ ((q3 ◇ q3) ◇ q3)) ◇ t) (congrArg (fun t => t ◇ ((q2 ◇ q2) ◇ q2)) ((h q2 q2).symm))).symm).trans (apc0 q3 ((q2 ◇ q2) ◇ q2))
  have apc2 : forall (q4 q5:G), ((q5 ◇ ((q5 ◇ q5) ◇ q5)) ◇ q4) = ((q5 ◇ q5) ◇ q5):=by
    intro q4 q5
    exact ((congrArg (fun t => (q5 ◇ ((q5 ◇ q5) ◇ q5)) ◇ t) ((h q4 ((q4 ◇ q4) ◇ q4)).symm)).symm).trans (apc1 ((q4 ◇ q4) ◇ q4) q5)
  have apc3 : forall (q0 q6:G), (((q6 ◇ q6) ◇ q6) ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) = q6:=by
    intro q0 q6
    exact ((congrArg (fun t => ((q6 ◇ q6) ◇ q6) ◇ t) (congrArg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) ((h q0 q0).symm))).symm).trans ((h q6 ((q0 ◇ q0) ◇ q0)).symm)
  have apc5 : forall (q7 q8:G), (((q8 ◇ q8) ◇ q8) ◇ q7) = q8:=by
    intro q7 q8
    exact ((congrArg (fun t => ((q8 ◇ q8) ◇ q8) ◇ t) ((h q7 ((q7 ◇ q7) ◇ q7)).symm)).symm).trans (apc3 ((q7 ◇ q7) ◇ q7) q8)
  have apc6 : forall (q9 q10:G), (q9 ◇ ((q9 ◇ q9) ◇ q9)) = (q9 ◇ q10):=by
    intro q9 q10
    exact ((((congrArg (fun t => t ◇ q10) (apc5 ((((q9 ◇ q9) ◇ q9) ◇ ((q9 ◇ q9) ◇ q9)) ◇ ((q9 ◇ q9) ◇ q9)) q9)).symm).trans (apc2 q10 ((q9 ◇ q9) ◇ q9))).trans (congrArg (fun t => t ◇ ((q9 ◇ q9) ◇ q9)) (apc5 ((q9 ◇ q9) ◇ q9) q9))).symm
  have apc7 : forall (q11 q12 q13:G), ((q13 ◇ q13) ◇ q13) = ((q13 ◇ q11) ◇ q12):=by
    intro q11 q12 q13
    exact (((congrArg (fun t => t ◇ q12) (apc6 q13 q11)).symm).trans (apc2 q12 q13)).symm
  exact ((apc7 x y x).symm).trans (apc7 (z ◇ w) u x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23998_to_60911 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_23998_to_60911
