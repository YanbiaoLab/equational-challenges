-- Equation23381 → Equation62284
-- Recorded verdict: true
-- Premise: x = ((y ◇ x) ◇ y) ◇ (z ◇ (z ◇ y))
-- Conclusion: (x ◇ y) ◇ z = ((y ◇ x) ◇ x) ◇ z
-- Original submission SHA-256: 050177eebe481eed63e2e456144e45c645c8218edc90412e5c8ff06a83401eff
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ y) ◇ (z ◇ (z ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = ((y ◇ x) ◇ x) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc2 : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q1 ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0))))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0))))) ((h (q0 ◇ q0) q0 q0).symm)).symm).trans ((h q0 (q0 ◇ (q0 ◇ q0)) q1).symm)
  have apc3 : forall (q2 q3:G), ((q3 ◇ q3) ◇ (((q3 ◇ q2) ◇ q3) ◇ q2)) = q3:=by
    intro q2 q3
    exact ((cg (fun t => (q3 ◇ q3) ◇ t) (cg (fun t => ((q3 ◇ q2) ◇ q3) ◇ t) ((h q2 q3 q3).symm))).symm).trans (apc2 q3 ((q3 ◇ q2) ◇ q3))
  have apc4 : forall (q4 q5:G), ((q5 ◇ q5) ◇ (q4 ◇ (q4 ◇ q5))) = q5:=by
    intro q4 q5
    exact ((cg (fun t => (q5 ◇ q5) ◇ t) ((h (q4 ◇ (q4 ◇ q5)) q5 q4).symm)).symm).trans (apc3 (q4 ◇ (q4 ◇ q5)) q5)
  have apc5 : forall (q6 q7 q8 q1:G), ((q6 ◇ ((q7 ◇ q6) ◇ q7)) ◇ (q1 ◇ (q1 ◇ ((q7 ◇ q6) ◇ q7)))) = (q8 ◇ (q8 ◇ q7)):=by
    intro q6 q7 q8 q1
    exact ((cg (fun t => t ◇ (q1 ◇ (q1 ◇ ((q7 ◇ q6) ◇ q7)))) (cg (fun t => t ◇ ((q7 ◇ q6) ◇ q7)) ((h q6 q7 q8).symm))).symm).trans ((h (q8 ◇ (q8 ◇ q7)) ((q7 ◇ q6) ◇ q7) q1).symm)
  have apc6 : forall (q9:G), ((q9 ◇ q9) ◇ q9) = q9:=by
    intro q9
    exact (((cg (fun t => t ◇ q9) (cg (fun t => t ◇ ((q9 ◇ q9) ◇ (q9 ◇ (q9 ◇ q9)))) (apc4 q9 q9))).trans (cg (fun t => t ◇ q9) (cg (fun t => q9 ◇ t) (apc4 q9 q9)))).symm).trans ((((cg (fun t => (((q9 ◇ q9) ◇ (q9 ◇ (q9 ◇ q9))) ◇ ((q9 ◇ q9) ◇ (q9 ◇ (q9 ◇ q9)))) ◇ t) (apc2 q9 (q9 ◇ q9))).symm).trans (apc4 (q9 ◇ q9) ((q9 ◇ q9) ◇ (q9 ◇ (q9 ◇ q9))))).trans (apc4 q9 q9))
  have apc7 : forall (q10 q11:G), (((q11 ◇ q10) ◇ q11) ◇ q11) = q10:=by
    intro q10 q11
    exact ((cg (fun t => ((q11 ◇ q10) ◇ q11) ◇ t) (apc6 q11)).symm).trans (((cg (fun t => ((q11 ◇ q10) ◇ q11) ◇ t) (cg (fun t => (q11 ◇ q11) ◇ t) (apc6 q11))).symm).trans ((h q10 q11 (q11 ◇ q11)).symm))
  have apc8 : forall (q10 q11:G), (q10 ◇ q10) = q10:=by
    intro q10 q11
    exact (((apc7 q10 q11).symm).trans (((apc7 q10 q11).trans ((apc7 q10 q10).symm)).trans (cg (fun t => t ◇ q10) (apc6 q10)))).symm
  have apc9 : forall (q12 q13:G), (((q13 ◇ q12) ◇ q13) ◇ q12) = q13:=by
    intro q12 q13
    exact ((((((cg (fun t => t ◇ (q13 ◇ q13)) (cg (fun t => q13 ◇ t) (apc8 q13 (q13 ◇ q13)))).trans (cg (fun t => t ◇ (q13 ◇ q13)) (apc8 q13 (q13 ◇ q13)))).trans (cg (fun t => q13 ◇ t) (apc8 q13 (q13 ◇ q13)))).trans (apc8 q13 (q13 ◇ q13))).symm).trans (((cg (fun t => t ◇ (q13 ◇ q13)) (cg (fun t => t ◇ (q13 ◇ q13)) (apc3 q12 q13))).symm).trans (apc7 (((q13 ◇ q12) ◇ q13) ◇ q12) (q13 ◇ q13)))).symm
  have apc13 : forall (q14 q15 q16:G), (q14 ◇ (q16 ◇ (q16 ◇ q14))) = (q15 ◇ (q15 ◇ q14)):=by
    intro q14 q15 q16
    exact ((((cg (fun t => (q14 ◇ q14) ◇ t) (cg (fun t => q16 ◇ t) (cg (fun t => q16 ◇ t) (cg (fun t => t ◇ q14) (apc8 q14 (q14 ◇ q14)))))).trans (cg (fun t => (q14 ◇ q14) ◇ t) (cg (fun t => q16 ◇ t) (cg (fun t => q16 ◇ t) (apc8 q14 (q14 ◇ q14)))))).trans (cg (fun t => t ◇ (q16 ◇ (q16 ◇ q14))) (apc8 q14 (q14 ◇ q14)))).symm).trans (((cg (fun t => t ◇ (q16 ◇ (q16 ◇ ((q14 ◇ q14) ◇ q14)))) (cg (fun t => q14 ◇ t) (apc6 q14))).symm).trans (apc5 q14 q14 q15 q16))
  have apc14 : forall (q17 q18 q19:G), (((q17 ◇ (q18 ◇ (q18 ◇ q17))) ◇ q19) ◇ q19) = (q19 ◇ q17):=by
    intro q17 q18 q19
    exact ((cg (fun t => t ◇ q19) (cg (fun t => t ◇ q19) ((apc13 q17 q19 q18).symm))).symm).trans (apc7 (q19 ◇ q17) q19)
  have apc15 : forall (q20 q21 q22:G), ((q20 ◇ q21) ◇ q21) = (q21 ◇ q20):=by
    intro q20 q21 q22
    exact (((cg (fun t => t ◇ q21) (cg (fun t => t ◇ q21) (cg (fun t => q20 ◇ t) (apc9 q22 q20)))).trans (cg (fun t => t ◇ q21) (cg (fun t => t ◇ q21) (apc8 q20 (q20 ◇ q20))))).symm).trans (((cg (fun t => t ◇ q21) (cg (fun t => t ◇ q21) (cg (fun t => q20 ◇ t) (cg (fun t => ((q20 ◇ q22) ◇ q20) ◇ t) (apc7 q22 q20))))).symm).trans (apc14 q20 ((q20 ◇ q22) ◇ q20) q21))
  exact (calc
    ((x ◇ y) ◇ z) = ((x ◇ y) ◇ z):=rfl
    _ = (((y ◇ x) ◇ x) ◇ z):=(cg (fun t => t ◇ z) (apc15 y x ((y ◇ x) ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23381_to_62284 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_23381_to_62284
