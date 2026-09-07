-- Equation23789 → Equation57698
-- Recorded verdict: true
-- Premise: x = ((y ◇ z) ◇ z) ◇ (y ◇ (x ◇ y))
-- Conclusion: x ◇ (y ◇ y) = ((x ◇ z) ◇ z) ◇ y
-- Original submission SHA-256: 3260e2c742d9ecd358c8a82ec4ad674e0a5af0bb47994d54cc344c5f306651ea
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ z) ◇ (y ◇ (x ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ y) = ((x ◇ z) ◇ z) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), (((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1) ◇ (q0 ◇ q0)) = q0:=by
    intro q0 q1
    exact ((cg (fun t => ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q1) ◇ t) ((h (q0 ◇ q0) q0 q0).symm)).symm).trans ((h q0 ((q0 ◇ q0) ◇ q0) q1).symm)
  have apc1 : forall (q2 q3:G), ((q2 ◇ (q3 ◇ (q2 ◇ q3))) ◇ (q3 ◇ q3)) = q3:=by
    intro q2 q3
    exact ((cg (fun t => t ◇ (q3 ◇ q3)) (cg (fun t => t ◇ (q3 ◇ (q2 ◇ q3))) ((h q2 q3 q3).symm))).symm).trans (apc0 q3 (q3 ◇ (q2 ◇ q3)))
  have apc2 : forall (q4 q5:G), (((q5 ◇ q4) ◇ q4) ◇ (q5 ◇ q5)) = q5:=by
    intro q4 q5
    exact ((cg (fun t => t ◇ (q5 ◇ q5)) ((h ((q5 ◇ q4) ◇ q4) q5 q4).symm)).symm).trans (apc1 ((q5 ◇ q4) ◇ q4) q5)
  have apc3 : forall (q6:G), (q6 ◇ (q6 ◇ q6)) = q6:=by
    intro q6
    exact (((cg (fun t => q6 ◇ t) (cg (fun t => t ◇ (((q6 ◇ q6) ◇ q6) ◇ (q6 ◇ q6))) (apc2 q6 q6))).trans (cg (fun t => q6 ◇ t) (cg (fun t => q6 ◇ t) (apc2 q6 q6)))).symm).trans ((((cg (fun t => t ◇ ((((q6 ◇ q6) ◇ q6) ◇ (q6 ◇ q6)) ◇ (((q6 ◇ q6) ◇ q6) ◇ (q6 ◇ q6)))) (apc0 q6 (q6 ◇ q6))).symm).trans (apc2 (q6 ◇ q6) (((q6 ◇ q6) ◇ q6) ◇ (q6 ◇ q6)))).trans (apc2 q6 q6))
  have apc4 : forall (q7 q8:G), (((q7 ◇ q8) ◇ q8) ◇ q7) = q7:=by
    intro q7 q8
    exact ((cg (fun t => ((q7 ◇ q8) ◇ q8) ◇ t) (apc3 q7)).symm).trans ((h q7 q7 q8).symm)
  have apc6 : forall (q9 q10 q11:G), ((q10 ◇ q9) ◇ q9) = q10:=by
    intro q9 q10 q11
    exact (((apc2 q11 q10).symm).trans (((cg (fun t => ((q10 ◇ q11) ◇ q11) ◇ t) (cg (fun t => q10 ◇ t) (apc4 q10 q9))).symm).trans ((h ((q10 ◇ q9) ◇ q9) q10 q11).symm))).symm
  have apc7 : forall (q12 q13 q14:G), (q13 ◇ (q13 ◇ q12)) = (q12 ◇ q13):=by
    intro q12 q13 q14
    exact ((cg (fun t => t ◇ (q13 ◇ q12)) (apc6 q14 q13 ((q13 ◇ q14) ◇ q14))).symm).trans (((cg (fun t => ((q13 ◇ q14) ◇ q14) ◇ t) (cg (fun t => q13 ◇ t) (apc6 q13 q12 q12))).symm).trans ((h (q12 ◇ q13) q13 q14).symm))
  have apc8 : forall (q15 q16:G), (q16 ◇ (q15 ◇ q16)) = ((q16 ◇ q15) ◇ q16):=by
    intro q15 q16
    exact ((cg (fun t => q16 ◇ t) (apc7 q15 q16 q15)).symm).trans (apc7 (q16 ◇ q15) q16 q15)
  have apc9 : forall (q17 q18 q19:G), (((q18 ◇ q17) ◇ q18) ◇ q17) = (q17 ◇ q18):=by
    intro q17 q18 q19
    exact ((cg (fun t => t ◇ q17) (apc8 q17 q18)).symm).trans ((((cg (fun t => (q18 ◇ (q17 ◇ q18)) ◇ t) ((h q17 q18 q19).symm)).symm).trans (apc8 ((q18 ◇ q19) ◇ q19) (q18 ◇ (q17 ◇ q18)))).trans ((((((cg (fun t => t ◇ (q18 ◇ (q17 ◇ q18))) (cg (fun t => (q18 ◇ (q17 ◇ q18)) ◇ t) (apc6 q19 q18 ((q18 ◇ q19) ◇ q19)))).trans (cg (fun t => t ◇ (q18 ◇ (q17 ◇ q18))) (cg (fun t => t ◇ q18) (apc8 q17 q18)))).trans (cg (fun t => (((q18 ◇ q17) ◇ q18) ◇ q18) ◇ t) (apc8 q17 q18))).trans (cg (fun t => t ◇ ((q18 ◇ q17) ◇ q18)) (apc6 q18 (q18 ◇ q17) (((q18 ◇ q17) ◇ q18) ◇ q18)))).trans (apc7 q18 (q18 ◇ q17) ((q18 ◇ q17) ◇ ((q18 ◇ q17) ◇ q18)))).trans (apc7 q17 q18 (q18 ◇ (q18 ◇ q17)))))
  have apc10 : forall (q20 q21:G), (((q20 ◇ q21) ◇ q20) ◇ (q21 ◇ q20)) = (q21 ◇ ((q20 ◇ q21) ◇ q20)):=by
    intro q20 q21
    exact ((cg (fun t => ((q20 ◇ q21) ◇ q20) ◇ t) (apc9 q21 q20 q20)).symm).trans (apc7 q21 ((q20 ◇ q21) ◇ q20) q20)
  have apc13 : forall (q22:G), (q22 ◇ q22) = q22:=by
    intro q22
    exact ((((cg (fun t => t ◇ q22) (cg (fun t => q22 ◇ t) (apc6 q22 q22 ((q22 ◇ q22) ◇ q22)))).trans (apc6 q22 q22 ((q22 ◇ q22) ◇ q22))).symm).trans ((((cg (fun t => t ◇ q22) (apc10 q22 q22)).symm).trans (apc9 q22 (q22 ◇ q22) q22)).trans (apc7 q22 q22 (q22 ◇ (q22 ◇ q22))))).symm
  exact (calc
    (x ◇ (y ◇ y)) = (x ◇ y):=cg (fun t => x ◇ t) (apc13 y)
    _ = (((x ◇ z) ◇ z) ◇ y):=(cg (fun t => t ◇ y) (apc6 z x ((x ◇ z) ◇ z))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23789_to_57698 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_23789_to_57698
