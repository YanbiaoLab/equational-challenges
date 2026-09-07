-- Equation29470 → Equation29272
-- Recorded verdict: true
-- Premise: x = (y ◇ (x ◇ (x ◇ (y ◇ z)))) ◇ x
-- Conclusion: x = (x ◇ (x ◇ (y ◇ (x ◇ z)))) ◇ x
-- Original submission SHA-256: 59c67af260d1a2842cca18f8eb0c3cdddb261fcad300bfa6b910d686fa2f5aee
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Tactic

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ (x ◇ (y ◇ z)))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (x ◇ (y ◇ (x ◇ z)))) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((y ◇ (x ◇ (x ◇ (y ◇ z)))) ◇ x) = ((x ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), ((x ◇ (x ◇ (x ◇ (x ◇ x)))) ◇ x) = x:=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0 q1 q2 q3:G), (((q0 ◇ (q3 ◇ (q3 ◇ (q0 ◇ q1)))) ◇ (q2 ◇ (q2 ◇ q3))) ◇ q2) = q2:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ q2) (cg (fun t => (q0 ◇ (q3 ◇ (q3 ◇ (q0 ◇ q1)))) ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => q2 ◇ t) ((h q3 q0 q1).symm))))).symm).trans ((h q2 (q0 ◇ (q3 ◇ (q3 ◇ (q0 ◇ q1)))) q3).symm)
  have apc3 : forall (q4 q5 q6 q7 q8:G), ((((q4 ◇ (q6 ◇ (q6 ◇ (q4 ◇ q5)))) ◇ (q8 ◇ (q8 ◇ q6))) ◇ (q7 ◇ (q7 ◇ q8))) ◇ q7) = q7:=by
    intro q4 q5 q6 q7 q8
    exact ((cg (fun t => t ◇ q7) (cg (fun t => ((q4 ◇ (q6 ◇ (q6 ◇ (q4 ◇ q5)))) ◇ (q8 ◇ (q8 ◇ q6))) ◇ t) (cg (fun t => q7 ◇ t) (cg (fun t => q7 ◇ t) (apc2 q4 q5 q8 q6))))).symm).trans ((h q7 ((q4 ◇ (q6 ◇ (q6 ◇ (q4 ◇ q5)))) ◇ (q8 ◇ (q8 ◇ q6))) q8).symm)
  have apc4 : forall (q9:G), (q9 ◇ (q9 ◇ (q9 ◇ (q9 ◇ (q9 ◇ q9))))) = (q9 ◇ (q9 ◇ (q9 ◇ (q9 ◇ q9)))):=by
    intro q9
    exact (((cg (fun t => t ◇ (q9 ◇ (q9 ◇ (q9 ◇ (q9 ◇ q9))))) (cg (fun t => ((q9 ◇ (q9 ◇ (q9 ◇ (q9 ◇ q9)))) ◇ (q9 ◇ (q9 ◇ q9))) ◇ t) (apc1 q9 ((q9 ◇ (q9 ◇ (q9 ◇ (q9 ◇ q9)))) ◇ q9) ((q9 ◇ (q9 ◇ (q9 ◇ (q9 ◇ q9)))) ◇ q9)))).trans (cg (fun t => t ◇ (q9 ◇ (q9 ◇ (q9 ◇ (q9 ◇ q9))))) (apc2 q9 q9 q9 q9))).symm).trans (((cg (fun t => t ◇ (q9 ◇ (q9 ◇ (q9 ◇ (q9 ◇ q9))))) (cg (fun t => ((q9 ◇ (q9 ◇ (q9 ◇ (q9 ◇ q9)))) ◇ (q9 ◇ (q9 ◇ q9))) ◇ t) (cg (fun t => (q9 ◇ (q9 ◇ (q9 ◇ (q9 ◇ q9)))) ◇ t) (apc1 q9 q9 q9)))).symm).trans (apc3 q9 q9 q9 (q9 ◇ (q9 ◇ (q9 ◇ (q9 ◇ q9)))) q9))
  have apc5 : forall (q10 q11:G), ((q11 ◇ (q10 ◇ (q10 ◇ (q11 ◇ (q11 ◇ (q11 ◇ (q11 ◇ q11))))))) ◇ q10) = q10:=by
    intro q10 q11
    exact ((cg (fun t => t ◇ q10) (cg (fun t => q11 ◇ t) (cg (fun t => q10 ◇ t) (cg (fun t => q10 ◇ t) (apc4 q11))))).symm).trans ((h q10 q11 (q11 ◇ (q11 ◇ (q11 ◇ (q11 ◇ q11))))).symm)
  have apc7 : forall (q12 q13:G), (q13 ◇ (q12 ◇ (q13 ◇ (q13 ◇ (q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))))))) = (q12 ◇ (q13 ◇ (q13 ◇ (q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12))))))):=by
    intro q12 q13
    exact (((cg (fun t => t ◇ (q12 ◇ (q13 ◇ (q13 ◇ (q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))))))) (cg (fun t => ((q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))) ◇ (q13 ◇ (q13 ◇ q12))) ◇ t) (apc5 q13 q12))).trans (cg (fun t => t ◇ (q12 ◇ (q13 ◇ (q13 ◇ (q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))))))) (apc2 q12 q12 q13 q12))).symm).trans (((cg (fun t => t ◇ (q12 ◇ (q13 ◇ (q13 ◇ (q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))))))) (cg (fun t => ((q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12)))) ◇ (q13 ◇ (q13 ◇ q12))) ◇ t) (cg (fun t => (q12 ◇ (q13 ◇ (q13 ◇ (q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12))))))) ◇ t) (apc5 q13 q12)))).symm).trans (apc3 q12 q12 q12 (q12 ◇ (q13 ◇ (q13 ◇ (q12 ◇ (q12 ◇ (q12 ◇ (q12 ◇ q12))))))) q13))
  have apc8 : forall (q14 q15:G), ((q15 ◇ (q15 ◇ (q14 ◇ (q14 ◇ (q15 ◇ (q15 ◇ (q15 ◇ (q15 ◇ q15)))))))) ◇ q14) = q14:=by
    intro q14 q15
    exact ((cg (fun t => t ◇ q14) (cg (fun t => q15 ◇ t) (apc7 q15 q14))).symm).trans (((cg (fun t => t ◇ q14) (cg (fun t => q15 ◇ t) (cg (fun t => q14 ◇ t) (apc7 q15 q14)))).symm).trans ((h q14 q15 (q14 ◇ (q14 ◇ (q15 ◇ (q15 ◇ (q15 ◇ (q15 ◇ q15))))))).symm))
  have apc13 : forall (q16 q17:G), (q17 ◇ (q16 ◇ (q16 ◇ (q17 ◇ (q17 ◇ (q16 ◇ (q16 ◇ (q16 ◇ (q16 ◇ q16))))))))) = (q16 ◇ (q16 ◇ (q17 ◇ (q17 ◇ (q16 ◇ (q16 ◇ (q16 ◇ (q16 ◇ q16)))))))):=by
    intro q16 q17
    exact (((cg (fun t => t ◇ (q16 ◇ (q16 ◇ (q17 ◇ (q17 ◇ (q16 ◇ (q16 ◇ (q16 ◇ (q16 ◇ q16))))))))) (cg (fun t => ((q16 ◇ (q16 ◇ (q16 ◇ (q16 ◇ q16)))) ◇ (q17 ◇ (q17 ◇ q16))) ◇ t) (apc8 q17 q16))).trans (cg (fun t => t ◇ (q16 ◇ (q16 ◇ (q17 ◇ (q17 ◇ (q16 ◇ (q16 ◇ (q16 ◇ (q16 ◇ q16))))))))) (apc2 q16 q16 q17 q16))).symm).trans (((cg (fun t => t ◇ (q16 ◇ (q16 ◇ (q17 ◇ (q17 ◇ (q16 ◇ (q16 ◇ (q16 ◇ (q16 ◇ q16))))))))) (cg (fun t => ((q16 ◇ (q16 ◇ (q16 ◇ (q16 ◇ q16)))) ◇ (q17 ◇ (q17 ◇ q16))) ◇ t) (cg (fun t => (q16 ◇ (q16 ◇ (q17 ◇ (q17 ◇ (q16 ◇ (q16 ◇ (q16 ◇ (q16 ◇ q16)))))))) ◇ t) (apc8 q17 q16)))).symm).trans (apc3 q16 q16 q16 (q16 ◇ (q16 ◇ (q17 ◇ (q17 ◇ (q16 ◇ (q16 ◇ (q16 ◇ (q16 ◇ q16)))))))) q17))
  have apc14 : forall (q18 q19:G), ((q18 ◇ (q18 ◇ (q19 ◇ (q19 ◇ (q18 ◇ (q18 ◇ (q18 ◇ (q18 ◇ q18)))))))) ◇ q18) = q18:=by
    intro q18 q19
    exact ((cg (fun t => t ◇ q18) (apc13 q18 q19)).symm).trans ((h q18 q19 (q19 ◇ (q18 ◇ (q18 ◇ (q18 ◇ (q18 ◇ q18)))))).symm)
  have apc17 : forall (q20 q21 q22:G), (((q20 ◇ (q20 ◇ (q22 ◇ (q22 ◇ (q20 ◇ (q20 ◇ (q20 ◇ (q20 ◇ q20)))))))) ◇ (q21 ◇ (q21 ◇ q22))) ◇ q21) = q21:=by
    intro q20 q21 q22
    exact ((cg (fun t => t ◇ q21) (cg (fun t => t ◇ (q21 ◇ (q21 ◇ q22))) (cg (fun t => q20 ◇ t) (apc7 q20 q22)))).symm).trans (((cg (fun t => t ◇ q21) (cg (fun t => t ◇ (q21 ◇ (q21 ◇ q22))) (cg (fun t => q20 ◇ t) (cg (fun t => q22 ◇ t) (apc7 q20 q22))))).symm).trans (apc2 q20 (q22 ◇ (q22 ◇ (q20 ◇ (q20 ◇ (q20 ◇ (q20 ◇ q20)))))) q21 q22))
  have apc18 : forall (q23 q24:G), ((q23 ◇ (q23 ◇ q24)) ◇ q23) = q23:=by
    intro q23 q24
    exact ((cg (fun t => t ◇ q23) (apc14 (q23 ◇ (q23 ◇ q24)) q24)).symm).trans (apc17 (q23 ◇ (q23 ◇ q24)) q23 q24)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ (x ◇ (y ◇ (x ◇ z)))) ◇ x):=(apc18 x (y ◇ (x ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_29470_to_29272 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_29470_to_29272
