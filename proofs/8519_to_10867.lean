-- Equation8519 → Equation10867
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (((z ◇ z) ◇ y) ◇ y))
-- Conclusion: x = x ◇ ((x ◇ (y ◇ y)) ◇ (z ◇ z))
-- Original submission SHA-256: a6086ca7c5a1f217f1a73dc0d05d9e78f5bdf98de7708ac6350ca5acc043ea23
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (((z ◇ z) ◇ y) ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ ((x ◇ (y ◇ y)) ◇ (z ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (y ◇ (x ◇ (((z ◇ z) ◇ y) ◇ y))) = (x ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), (x ◇ (x ◇ (((x ◇ x) ◇ x) ◇ x))) = x:=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0 q1 q2:G), ((((q0 ◇ q0) ◇ q1) ◇ q1) ◇ ((q2 ◇ q2) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => (((q0 ◇ q0) ◇ q1) ◇ q1) ◇ t) ((h ((q2 ◇ q2) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1)) q1 q0).symm)).symm).trans ((h q1 (((q0 ◇ q0) ◇ q1) ◇ q1) q2).symm)
  have apc3 : forall (q3 q4:G), ((q3 ◇ q3) ◇ ((((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3))) = ((q3 ◇ q3) ◇ ((q4 ◇ q4) ◇ (q3 ◇ q3))):=by
    intro q3 q4
    exact (((((cg (fun t => ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ ((((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)))) ◇ t) (cg (fun t => (q4 ◇ q4) ◇ t) (cg (fun t => t ◇ ((q3 ◇ q3) ◇ ((((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)))) (apc1 (q3 ◇ q3) ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ ((((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)))) ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ ((((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)))))))).trans (cg (fun t => ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ ((((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)))) ◇ t) (cg (fun t => (q4 ◇ q4) ◇ t) (apc1 (q3 ◇ q3) ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ ((((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)))) ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ ((((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)))))))).trans (cg (fun t => t ◇ ((q4 ◇ q4) ◇ (q3 ◇ q3))) (apc1 (q3 ◇ q3) ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ ((((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)))) ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ ((((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3))))))).symm).trans (((cg (fun t => t ◇ ((q4 ◇ q4) ◇ (((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ ((((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)))) ◇ ((q3 ◇ q3) ◇ ((((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)))))) (cg (fun t => t ◇ ((q3 ◇ q3) ◇ ((((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)))) (apc1 (q3 ◇ q3) q3 q3))).symm).trans (apc2 q3 ((q3 ◇ q3) ◇ ((((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3)) ◇ (q3 ◇ q3))) q4))).symm
  have apc4 : forall (q3 q4:G), ((q3 ◇ q3) ◇ ((q4 ◇ q4) ◇ (q3 ◇ q3))) = ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))):=by
    intro q3 q4
    exact ((apc3 q3 q4).symm).trans (apc3 q3 q3)
  have apc5 : forall (q5:G), ((q5 ◇ q5) ◇ ((q5 ◇ q5) ◇ ((q5 ◇ q5) ◇ (q5 ◇ q5)))) = (q5 ◇ q5):=by
    intro q5
    exact ((cg (fun t => (q5 ◇ q5) ◇ t) (apc4 q5 q5)).symm).trans (((cg (fun t => (q5 ◇ q5) ◇ t) (apc3 q5 q5)).symm).trans ((h (q5 ◇ q5) (q5 ◇ q5) (q5 ◇ q5)).symm))
  have apc6 : forall (q6 q7:G), (((q7 ◇ q7) ◇ ((q7 ◇ q7) ◇ (q7 ◇ q7))) ◇ (q6 ◇ (q7 ◇ q7))) = q6:=by
    intro q6 q7
    exact ((cg (fun t => ((q7 ◇ q7) ◇ ((q7 ◇ q7) ◇ (q7 ◇ q7))) ◇ t) (cg (fun t => q6 ◇ t) (apc5 q7))).symm).trans (((cg (fun t => ((q7 ◇ q7) ◇ ((q7 ◇ q7) ◇ (q7 ◇ q7))) ◇ t) (cg (fun t => q6 ◇ t) (cg (fun t => t ◇ ((q7 ◇ q7) ◇ ((q7 ◇ q7) ◇ (q7 ◇ q7)))) (apc5 q7)))).symm).trans ((h q6 ((q7 ◇ q7) ◇ ((q7 ◇ q7) ◇ (q7 ◇ q7))) q7).symm))
  have apc7 : forall (q8:G), ((q8 ◇ q8) ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) = ((q8 ◇ q8) ◇ (q8 ◇ q8)):=by
    intro q8
    exact (((cg (fun t => (q8 ◇ q8) ◇ t) (cg (fun t => (q8 ◇ q8) ◇ t) (apc6 (q8 ◇ q8) q8))).trans (apc4 q8 q8)).symm).trans (((cg (fun t => t ◇ ((q8 ◇ q8) ◇ (((q8 ◇ q8) ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))) ◇ ((q8 ◇ q8) ◇ (q8 ◇ q8))))) (apc6 (q8 ◇ q8) q8)).symm).trans (apc2 q8 ((q8 ◇ q8) ◇ (q8 ◇ q8)) q8))
  have apc8 : forall (q5 q8:G), ((q5 ◇ q5) ◇ (q5 ◇ q5)) = (q5 ◇ q5):=by
    intro q5 q8
    exact (((cg (fun t => (q5 ◇ q5) ◇ t) (apc7 q5)).trans (apc7 q5)).symm).trans (apc5 q5)
  have apc9 : forall (q9 q10:G), ((q10 ◇ q10) ◇ (q9 ◇ (q10 ◇ q10))) = q9:=by
    intro q9 q10
    exact ((cg (fun t => (q10 ◇ q10) ◇ t) (cg (fun t => q9 ◇ t) (apc8 q10 ((q10 ◇ q10) ◇ (q10 ◇ q10))))).symm).trans (((cg (fun t => (q10 ◇ q10) ◇ t) (cg (fun t => q9 ◇ t) (cg (fun t => t ◇ (q10 ◇ q10)) (apc8 q10 q9)))).symm).trans ((h q9 (q10 ◇ q10) q10).symm))
  have apc10 : forall (q11 q12:G), (q12 ◇ q12) = (q11 ◇ q11):=by
    intro q11 q12
    exact ((apc9 (q12 ◇ q12) q11).symm).trans (((cg (fun t => (q11 ◇ q11) ◇ t) (apc9 ((q12 ◇ q12) ◇ (q11 ◇ q11)) q11)).symm).trans ((h (q11 ◇ q11) (q11 ◇ q11) q12).symm))
  have apc11 : forall (q13 q14:G), ((q13 ◇ q13) ◇ (q14 ◇ q14)) = (q14 ◇ q14):=by
    intro q13 q14
    exact ((cg (fun t => t ◇ (q14 ◇ q14)) (apc10 q13 q14)).symm).trans (apc8 q14 q13)
  have apc12 : forall (q15 q16 q17:G), (((q17 ◇ q17) ◇ q16) ◇ q16) = (q16 ◇ (q15 ◇ q15)):=by
    intro q15 q16 q17
    exact (((cg (fun t => q16 ◇ t) (apc10 q15 (((q17 ◇ q17) ◇ q16) ◇ q16))).symm).trans ((h (((q17 ◇ q17) ◇ q16) ◇ q16) q16 q17).symm)).symm
  have apc18 : forall (q18 q19 q20:G), (q20 ◇ (q19 ◇ (q20 ◇ (q18 ◇ q18)))) = q19:=by
    intro q18 q19 q20
    exact ((cg (fun t => q20 ◇ t) (cg (fun t => q19 ◇ t) (apc12 q18 q20 q18))).symm).trans ((h q19 q20 q18).symm)
  have apc20 : forall (q21 q22 q23:G), ((q21 ◇ (q23 ◇ q23)) ◇ (q22 ◇ q22)) = (q21 ◇ (q21 ◇ (q23 ◇ q23))):=by
    intro q21 q22 q23
    exact ((((cg (fun t => q21 ◇ t) (cg (fun t => q21 ◇ t) (cg (fun t => t ◇ (q23 ◇ q23)) (apc11 q21 q23)))).trans (cg (fun t => q21 ◇ t) (cg (fun t => q21 ◇ t) (apc11 q23 q23)))).symm).trans ((((cg (fun t => t ◇ (q21 ◇ (((q21 ◇ q21) ◇ (q23 ◇ q23)) ◇ (q23 ◇ q23)))) ((h q21 (q23 ◇ q23) q21).symm)).symm).trans (apc12 q22 (q21 ◇ (((q21 ◇ q21) ◇ (q23 ◇ q23)) ◇ (q23 ◇ q23))) q23)).trans ((cg (fun t => t ◇ (q22 ◇ q22)) (cg (fun t => q21 ◇ t) (cg (fun t => t ◇ (q23 ◇ q23)) (apc11 q21 q23)))).trans (cg (fun t => t ◇ (q22 ◇ q22)) (cg (fun t => q21 ◇ t) (apc11 q23 q23)))))).symm
  exact (calc
    x = x:=rfl
    _ = (x ◇ ((x ◇ (y ◇ y)) ◇ (z ◇ z))):=((cg (fun t => x ◇ t) (apc20 x z y)).trans (apc18 y x x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_8519_to_10867 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_8519_to_10867
