-- Equation41939 → Equation62233
-- Recorded verdict: true
-- Premise: x * y = y * (y * (y * (z * w)))
-- Conclusion: (x * y) * z = ((x * y) * z) * w
-- Original submission SHA-256: 1182273eee4cf503be088b0f30c954e9dd7cc437b0c13d24a01642fc47bf007a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (y ◇ (y ◇ (z ◇ w)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = ((x ◇ y) ◇ z) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0 q0).trans ((h q1 q2 q0 q0).symm)).symm
  have apc2 : forall (q0 q1 q3:G), (q3 ◇ (q0 ◇ q3)) = (q1 ◇ q3):=by
    intro q0 q1 q3
    exact ((congrArg (fun t => q3 ◇ t) ((h q0 q3 q0 q0).symm)).symm).trans ((h q1 q3 q3 (q0 ◇ q0)).symm)
  have apc3 : forall (q4 q5 q6:G), ((q4 ◇ q6) ◇ (q4 ◇ q6)) = (q5 ◇ q6):=by
    intro q4 q5 q6
    exact (((apc2 q4 q5 q6).symm).trans ((apc0 q6 (q4 ◇ q6) q4 q4).symm)).symm
  have apc4 : forall (q7 q8:G), ((q7 ◇ q8) ◇ (q7 ◇ q8)) = (q8 ◇ q8):=by
    intro q7 q8
    exact (apc3 q7 q7 q8).trans ((apc0 q7 q8 q7 q7).symm)
  have apc5 : forall (x y z w:G), (y ◇ (y ◇ (y ◇ (z ◇ w)))) = (y ◇ (y ◇ (y ◇ (x ◇ x)))):=by
    intro x y z w
    exact ((h x y z w).symm).trans (h x y x x)
  have apc8 : forall (q9 q10:G), ((q9 ◇ q10) ◇ (q10 ◇ q10)) = (q10 ◇ q10):=by
    intro q9 q10
    exact ((congrArg (fun t => t ◇ (q10 ◇ q10)) (apc0 q9 q10 q9 q9)).symm).trans (apc4 q10 q10)
  have apc9 : forall (q11 q12 q13:G), ((q11 ◇ q13) ◇ (q12 ◇ q13)) = (q13 ◇ q13):=by
    intro q11 q12 q13
    exact ((congrArg (fun t => t ◇ (q12 ◇ q13)) (apc1 q11 q12 q13)).symm).trans (apc4 q12 q13)
  have apc11 : forall (q14 q15 q16 q17:G), ((q15 ◇ q16) ◇ (q14 ◇ q14)) = (q14 ◇ q14):=by
    intro q14 q15 q16 q17
    exact ((((congrArg (fun t => (q15 ◇ q16) ◇ t) (apc9 q16 q16 (q16 ◇ (q17 ◇ q14)))).trans (congrArg (fun t => (q15 ◇ q16) ◇ t) (apc9 q16 q16 (q17 ◇ q14)))).trans (congrArg (fun t => (q15 ◇ q16) ◇ t) (apc9 q17 q17 q14))).symm).trans ((((congrArg (fun t => t ◇ ((q16 ◇ (q16 ◇ (q17 ◇ q14))) ◇ (q16 ◇ (q16 ◇ (q17 ◇ q14))))) ((h q15 q16 q17 q14).symm)).symm).trans (apc8 q16 (q16 ◇ (q16 ◇ (q17 ◇ q14))))).trans (((apc9 q16 q16 (q16 ◇ (q17 ◇ q14))).trans (apc9 q16 q16 (q17 ◇ q14))).trans (apc9 q17 q17 q14)))
  have apc12 : forall (q18 q19 q20:G), (q19 ◇ q19) = (q18 ◇ q18):=by
    intro q18 q19 q20
    exact ((((congrArg (fun t => (q20 ◇ q18) ◇ t) (apc9 q20 q20 q18)).trans (apc9 q20 q18 q18)).symm).trans ((((congrArg (fun t => (q20 ◇ q18) ◇ t) (apc11 (q20 ◇ q18) q20 q18 q18)).symm).trans (apc5 q19 (q20 ◇ q18) q20 q18)).trans (((congrArg (fun t => (q20 ◇ q18) ◇ t) (congrArg (fun t => (q20 ◇ q18) ◇ t) (apc11 q19 q20 q18 ((q20 ◇ q18) ◇ (q19 ◇ q19))))).trans (congrArg (fun t => (q20 ◇ q18) ◇ t) (apc11 q19 q20 q18 ((q20 ◇ q18) ◇ (q19 ◇ q19))))).trans (apc11 q19 q20 q18 ((q20 ◇ q18) ◇ (q19 ◇ q19)))))).symm
  have apc13 : forall (q21 q22 q23:G), (q22 ◇ q23) = (q21 ◇ q21):=by
    intro q21 q22 q23
    exact (((apc12 q21 q23 q21).symm).trans (apc0 q22 q23 q21 q21)).symm
  exact (apc13 ((x ◇ y) ◇ z) (x ◇ y) z).trans ((apc13 ((x ◇ y) ◇ z) ((x ◇ y) ◇ z) w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41939_to_62233 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41939_to_62233
