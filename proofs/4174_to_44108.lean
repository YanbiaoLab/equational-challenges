-- Equation4174 → Equation44108
-- Recorded verdict: true
-- Premise: x * y = ((y * z) * x) * x
-- Conclusion: x * y = z * ((w * w) * (z * y))
-- Original submission SHA-256: 327d554c0c971c37da2a37c2bf9a72c3f93f8af1890103ca1e0bec96af6e2b74
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ z) ◇ x) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((w ◇ w) ◇ (z ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc1 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ q1)) = ((q2 ◇ q0) ◇ q2):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => t ◇ q2) ((h q2 q0 q1).symm)).symm).trans ((h q2 (q0 ◇ q1) q2).symm)).symm
  have apc2 : forall (q3 q4 q5:G), ((((q5 ◇ q3) ◇ q5) ◇ q4) ◇ q4) = (q4 ◇ q5):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => t ◇ q4) (congrArg (fun t => t ◇ q4) (apc1 q3 q3 q5))).symm).trans ((h q4 q5 (q3 ◇ q3)).symm)
  have apc3 : forall (x y z:G), (((y ◇ z) ◇ x) ◇ x) = (((y ◇ x) ◇ x) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc4 : forall (q6 q7 q8:G), ((q6 ◇ q7) ◇ q6) = (q6 ◇ q7):=by
    intro q6 q7 q8
    exact ((((apc2 q8 q6 q7).symm).trans ((h q6 (q7 ◇ q8) q7).symm)).trans (apc1 q7 q8 q6)).symm
  have apc5 : forall (q9 q10:G), (q9 ◇ q10) = (q9 ◇ q9):=by
    intro q9 q10
    exact ((apc4 q9 q10 ((q9 ◇ q10) ◇ q9)).symm).trans (((congrArg (fun t => t ◇ q9) (apc4 q9 q10 q9)).symm).trans ((h q9 q9 q10).symm))
  have apc6 : forall (q11 q12:G), ((q12 ◇ q11) ◇ (q12 ◇ q11)) = ((q12 ◇ q11) ◇ q12):=by
    intro q11 q12
    exact ((congrArg (fun t => t ◇ (q12 ◇ q11)) (apc4 q12 q11 q11)).symm).trans (apc4 (q12 ◇ q11) q12 q11)
  have apc9 : forall (q13 q14:G), (((q14 ◇ q13) ◇ q13) ◇ q13) = (q13 ◇ q13):=by
    intro q13 q14
    exact (((apc3 q13 q14 q13).symm).trans ((h q13 q14 q13).symm)).trans (apc5 q13 q14)
  have apc10 : forall (q15 q16:G), ((q16 ◇ q15) ◇ q16) = (q16 ◇ q16):=by
    intro q15 q16
    exact ((congrArg (fun t => t ◇ q16) ((h q16 q15 q15).symm)).symm).trans (apc9 q16 (q15 ◇ q15))
  have apc12 : forall (q15 q16 q11 q12:G), ((q12 ◇ q11) ◇ (q12 ◇ q11)) = (q12 ◇ q12):=by
    intro q15 q16 q11 q12
    exact (apc6 q11 q12).trans (apc10 q11 q12)
  have apc13 : forall (q17 q18 q19:G), (q18 ◇ q18) = (q17 ◇ q17):=by
    intro q17 q18 q19
    exact ((((congrArg (fun t => (q18 ◇ q17) ◇ t) (congrArg (fun t => t ◇ q18) (congrArg (fun t => t ◇ q18) (apc5 q17 q19)))).trans (apc5 (q18 ◇ q17) (((q17 ◇ q17) ◇ q18) ◇ q18))).trans (apc12 ((q18 ◇ q17) ◇ (q18 ◇ q17)) ((q18 ◇ q17) ◇ (q18 ◇ q17)) q17 q18)).symm).trans ((((congrArg (fun t => t ◇ (((q17 ◇ q19) ◇ q18) ◇ q18)) ((h q18 q17 q19).symm)).symm).trans (apc12 q17 q17 q18 ((q17 ◇ q19) ◇ q18))).trans ((((congrArg (fun t => t ◇ ((q17 ◇ q19) ◇ q18)) (congrArg (fun t => t ◇ q18) (apc5 q17 q19))).trans (congrArg (fun t => ((q17 ◇ q17) ◇ q18) ◇ t) (congrArg (fun t => t ◇ q18) (apc5 q17 q19)))).trans (apc12 (((q17 ◇ q17) ◇ q18) ◇ ((q17 ◇ q17) ◇ q18)) (((q17 ◇ q17) ◇ q18) ◇ ((q17 ◇ q17) ◇ q18)) q18 (q17 ◇ q17))).trans (apc12 ((q17 ◇ q17) ◇ (q17 ◇ q17)) ((q17 ◇ q17) ◇ (q17 ◇ q17)) q17 q17)))
  exact (calc
    (x ◇ y) = (x ◇ x):=apc5 x y
    _ = (z ◇ z):=apc13 z x w
    _ = (z ◇ ((w ◇ w) ◇ (z ◇ y))):=(apc5 z ((w ◇ w) ◇ (z ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4174_to_44108 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4174_to_44108
