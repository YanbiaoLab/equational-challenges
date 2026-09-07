-- Equation17125 → Equation45295
-- Recorded verdict: true
-- Premise: x = (x ◇ y) ◇ (z ◇ (y ◇ (z ◇ y)))
-- Conclusion: x ◇ y = x ◇ (((y ◇ y) ◇ z) ◇ z)
-- Original submission SHA-256: c46e4016391491e532ee78c381ad932abba20e10b36d75776fd2aeed1d90da96
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ (z ◇ (y ◇ (z ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ (((y ◇ y) ◇ z) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((x ◇ y) ◇ (z ◇ (y ◇ (z ◇ y)))) = ((x ◇ x) ◇ (x ◇ (x ◇ (x ◇ x)))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), ((x ◇ x) ◇ (x ◇ (x ◇ (x ◇ x)))) = x:=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0 q1 q2 q3:G), (q0 ◇ (q3 ◇ ((q2 ◇ (q1 ◇ (q2 ◇ q1))) ◇ (q3 ◇ (q2 ◇ (q1 ◇ (q2 ◇ q1))))))) = (q0 ◇ q1):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ (q3 ◇ ((q2 ◇ (q1 ◇ (q2 ◇ q1))) ◇ (q3 ◇ (q2 ◇ (q1 ◇ (q2 ◇ q1))))))) ((h q0 q1 q2).symm)).symm).trans ((h (q0 ◇ q1) (q2 ◇ (q1 ◇ (q2 ◇ q1))) q3).symm)
  have apc3 : forall (q4 q5 q6:G), ((q6 ◇ (q5 ◇ (q4 ◇ (q5 ◇ q4)))) ◇ q4) = q6:=by
    intro q4 q5 q6
    exact ((apc2 (q6 ◇ (q5 ◇ (q4 ◇ (q5 ◇ q4)))) q4 q5 q4).symm).trans ((h q6 (q5 ◇ (q4 ◇ (q5 ◇ q4))) q4).symm)
  have apc4 : forall (q7 q8 q9 q10:G), (q8 ◇ (q10 ◇ (q9 ◇ (q10 ◇ q9)))) = (q8 ◇ (q7 ◇ (q9 ◇ (q7 ◇ q9)))):=by
    intro q7 q8 q9 q10
    exact ((cg (fun t => t ◇ (q10 ◇ (q9 ◇ (q10 ◇ q9)))) (apc3 q9 q7 q8)).symm).trans ((h (q8 ◇ (q7 ◇ (q9 ◇ (q7 ◇ q9)))) q9 q10).symm)
  have apc5 : forall (q11 q12:G), ((q12 ◇ q12) ◇ (q11 ◇ (q12 ◇ (q11 ◇ q12)))) = q12:=by
    intro q11 q12
    exact ((apc4 q11 (q12 ◇ q12) q12 q12).symm).trans (apc1 q12 q11 q11)
  have apc7 : forall (q13 q14 q15 q16:G), (q14 ◇ ((q13 ◇ q15) ◇ ((q16 ◇ (q15 ◇ (q16 ◇ q15))) ◇ q13))) = (q14 ◇ q15):=by
    intro q13 q14 q15 q16
    exact ((cg (fun t => q14 ◇ t) (cg (fun t => (q13 ◇ q15) ◇ t) (cg (fun t => (q16 ◇ (q15 ◇ (q16 ◇ q15))) ◇ t) ((h q13 q15 q16).symm)))).symm).trans (apc2 q14 q15 q16 (q13 ◇ q15))
  have apc8 : forall (q17 q18 q19:G), (q17 ◇ (q18 ◇ ((q19 ◇ (q18 ◇ (q19 ◇ q18))) ◇ q18))) = (q17 ◇ q18):=by
    intro q17 q18 q19
    exact ((cg (fun t => q17 ◇ t) ((h (q18 ◇ ((q19 ◇ (q18 ◇ (q19 ◇ q18))) ◇ q18)) q18 (q19 ◇ (q18 ◇ (q19 ◇ q18)))).symm)).symm).trans (apc7 (q18 ◇ ((q19 ◇ (q18 ◇ (q19 ◇ q18))) ◇ q18)) q17 q18 q19)
  have apc9 : forall (q20 q21 q22:G), ((q21 ◇ q22) ◇ ((q20 ◇ (q22 ◇ (q20 ◇ q22))) ◇ q22)) = q21:=by
    intro q20 q21 q22
    exact ((cg (fun t => (q21 ◇ q22) ◇ t) (apc8 (q20 ◇ (q22 ◇ (q20 ◇ q22))) q22 q20)).symm).trans ((h q21 q22 (q20 ◇ (q22 ◇ (q20 ◇ q22)))).symm)
  have apc11 : forall (q23 q24 q25 q26:G), (q25 ◇ ((q23 ◇ (q26 ◇ (q23 ◇ q26))) ◇ q26)) = (q25 ◇ (q24 ◇ (q26 ◇ (q24 ◇ q26)))):=by
    intro q23 q24 q25 q26
    exact ((cg (fun t => q25 ◇ t) (apc8 (q23 ◇ (q26 ◇ (q23 ◇ q26))) q26 q23)).symm).trans (apc4 q24 q25 q26 (q23 ◇ (q26 ◇ (q23 ◇ q26))))
  have apc12 : forall (q27 q28 q29:G), (q29 ◇ (q28 ◇ (q27 ◇ (q28 ◇ (q27 ◇ q28))))) = (q29 ◇ q28):=by
    intro q27 q28 q29
    exact ((cg (fun t => q29 ◇ t) (cg (fun t => t ◇ (q27 ◇ (q28 ◇ (q27 ◇ q28)))) (apc9 q27 q28 q28))).symm).trans ((((cg (fun t => q29 ◇ t) (cg (fun t => t ◇ (q27 ◇ (q28 ◇ (q27 ◇ q28)))) (cg (fun t => (q28 ◇ q28) ◇ t) (cg (fun t => (q27 ◇ (q28 ◇ (q27 ◇ q28))) ◇ t) (apc5 q27 q28))))).symm).trans (apc11 (q28 ◇ q28) q27 q29 (q27 ◇ (q28 ◇ (q27 ◇ q28))))).trans (apc2 q29 q28 q27 q27))
  have apc22 : forall (q7 q8 q30 q9:G), ((q30 ◇ q9) ◇ ((q8 ◇ (q7 ◇ (q9 ◇ (q7 ◇ q9)))) ◇ (q9 ◇ q8))) = q30:=by
    intro q7 q8 q30 q9
    exact ((cg (fun t => (q30 ◇ q9) ◇ t) (cg (fun t => (q8 ◇ (q7 ◇ (q9 ◇ (q7 ◇ q9)))) ◇ t) (cg (fun t => q9 ◇ t) (apc3 q9 q7 q8)))).symm).trans ((h q30 q9 (q8 ◇ (q7 ◇ (q9 ◇ (q7 ◇ q9))))).symm)
  have apc23 : forall (q31 q32:G), ((q32 ◇ q31) ◇ (q31 ◇ q31)) = q32:=by
    intro q31 q32
    exact ((cg (fun t => t ◇ (q31 ◇ q31)) (cg (fun t => q32 ◇ t) (apc3 q31 q31 q31))).symm).trans (((cg (fun t => t ◇ (q31 ◇ q31)) (cg (fun t => q32 ◇ t) (cg (fun t => (q31 ◇ (q31 ◇ (q31 ◇ (q31 ◇ q31)))) ◇ t) (apc22 q31 q31 q31 q31)))).symm).trans (apc3 (q31 ◇ q31) (q31 ◇ (q31 ◇ (q31 ◇ (q31 ◇ q31)))) q32))
  have apc24 : forall (q33 q34:G), ((q34 ◇ q33) ◇ q33) = q34:=by
    intro q33 q34
    exact (((cg (fun t => (q34 ◇ q33) ◇ t) (apc12 q33 q33 (q33 ◇ (q33 ◇ (q33 ◇ (q33 ◇ q33)))))).trans (cg (fun t => (q34 ◇ q33) ◇ t) (apc3 q33 q33 q33))).symm).trans (((cg (fun t => t ◇ ((q33 ◇ (q33 ◇ (q33 ◇ (q33 ◇ q33)))) ◇ (q33 ◇ (q33 ◇ (q33 ◇ (q33 ◇ q33)))))) (apc12 q33 q33 q34)).symm).trans (apc23 (q33 ◇ (q33 ◇ (q33 ◇ (q33 ◇ q33)))) q34))
  have apc26 : forall (q35 q36:G), (q35 ◇ (q36 ◇ q36)) = (q35 ◇ q36):=by
    intro q35 q36
    exact ((cg (fun t => t ◇ (q36 ◇ q36)) (apc24 q36 q35)).symm).trans (apc23 q36 (q35 ◇ q36))
  exact (calc
    (x ◇ y) = (x ◇ y):=rfl
    _ = (x ◇ (((y ◇ y) ◇ z) ◇ z)):=((cg (fun t => x ◇ t) (apc24 z (y ◇ y))).trans (apc26 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_17125_to_45295 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_17125_to_45295
