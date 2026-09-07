-- Equation21675 → Equation15344
-- Recorded verdict: true
-- Premise: x = (y ◇ (x ◇ z)) ◇ (z ◇ (y ◇ z))
-- Conclusion: x = x ◇ (((y ◇ (y ◇ z)) ◇ w) ◇ u)
-- Original submission SHA-256: c6c6af71be115b577e38036ce1860fdabf57e6289555756a637683436a4ba3f0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ z)) ◇ (z ◇ (y ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = x ◇ (((y ◇ (y ◇ z)) ◇ w) ◇ u)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc4 : forall (q0 q1 q2 q3:G), ((q3 ◇ q0) ◇ ((q2 ◇ (q1 ◇ q2)) ◇ (q3 ◇ (q2 ◇ (q1 ◇ q2))))) = (q1 ◇ (q0 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ ((q2 ◇ (q1 ◇ q2)) ◇ (q3 ◇ (q2 ◇ (q1 ◇ q2))))) (congrArg (fun t => q3 ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h (q1 ◇ (q0 ◇ q2)) q3 (q2 ◇ (q1 ◇ q2))).symm)
  have apc5 : forall (q4 q5 q6:G), (q4 ◇ ((q6 ◇ (q5 ◇ (q4 ◇ q5))) ◇ q5)) = q6:=by
    intro q4 q5 q6
    exact ((apc4 (q6 ◇ (q5 ◇ (q4 ◇ q5))) q4 q5 q4).symm).trans ((h q6 q4 (q5 ◇ (q4 ◇ q5))).symm)
  have apc10 : forall (q7 q8 q9 q10:G), ((q7 ◇ (q9 ◇ (q9 ◇ q9))) ◇ (q8 ◇ q9)) = ((q10 ◇ q8) ◇ (q7 ◇ (q10 ◇ q7))):=by
    intro q7 q8 q9 q10
    exact (((congrArg (fun t => (q10 ◇ q8) ◇ t) (congrArg (fun t => q7 ◇ t) (congrArg (fun t => q10 ◇ t) (apc5 q9 q9 q7)))).symm).trans (((congrArg (fun t => (q10 ◇ q8) ◇ t) (congrArg (fun t => t ◇ (q10 ◇ (q9 ◇ ((q7 ◇ (q9 ◇ (q9 ◇ q9))) ◇ q9)))) (apc5 q9 q9 q7))).symm).trans (apc4 q8 (q7 ◇ (q9 ◇ (q9 ◇ q9))) q9 q10))).symm
  have apc12 : forall (q7 q8 q9 q10:G), ((q10 ◇ q8) ◇ (q7 ◇ (q10 ◇ q7))) = ((q7 ◇ q8) ◇ (q7 ◇ (q7 ◇ q7))):=by
    intro q7 q8 q9 q10
    exact ((apc10 q7 q8 q7 q10).symm).trans (apc10 q7 q8 q7 q7)
  have apc13 : forall (q11 q12 q13:G), (q11 ◇ (q13 ◇ (q12 ◇ q11))) = (q11 ◇ (q13 ◇ (q11 ◇ q11))):=by
    intro q11 q12 q13
    exact ((((congrArg (fun t => (q11 ◇ q13) ◇ t) (congrArg (fun t => ((q11 ◇ q11) ◇ (q11 ◇ (q11 ◇ q11))) ◇ t) (congrArg (fun t => q11 ◇ t) (apc12 q11 q11 ((q12 ◇ q11) ◇ (q11 ◇ (q12 ◇ q11))) q12)))).trans (apc4 q13 q11 (q11 ◇ q11) q11)).symm).trans (((congrArg (fun t => (q11 ◇ q13) ◇ t) (congrArg (fun t => t ◇ (q11 ◇ ((q12 ◇ q11) ◇ (q11 ◇ (q12 ◇ q11))))) (apc12 q11 q11 q11 q12))).symm).trans (apc4 q13 q11 (q12 ◇ q11) q11))).symm
  have apc14 : forall (q14 q15 q16:G), (q15 ◇ (q16 ◇ (q15 ◇ q15))) = (q15 ◇ q14):=by
    intro q14 q15 q16
    exact (((congrArg (fun t => q15 ◇ t) (apc5 q16 q15 q14)).symm).trans (apc13 q15 (q14 ◇ (q15 ◇ (q16 ◇ q15))) q16)).symm
  have apc15 : forall (q17 q18 q19:G), (q18 ◇ q17) = q19:=by
    intro q17 q18 q19
    exact ((apc14 q17 q18 (q19 ◇ ((q18 ◇ q18) ◇ (q18 ◇ (q18 ◇ q18))))).symm).trans (apc5 q18 (q18 ◇ q18) q19)
  exact ((apc15 z x x).symm).trans ((apc15 (((y ◇ (y ◇ z)) ◇ w) ◇ u) x (x ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_21675_to_15344 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_21675_to_15344
