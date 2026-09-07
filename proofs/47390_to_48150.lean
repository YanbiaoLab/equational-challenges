-- Equation47390 → Equation48150
-- Recorded verdict: true
-- Premise: x * y = (z * y) * ((y * x) * x)
-- Conclusion: x * y = (y * (z * w)) * (x * w)
-- Original submission SHA-256: db05cad9cf41be4d6a8a1b52f03d18dfdc416f9ddc95fff61f4fcd23852d352e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ y) ◇ ((y ◇ x) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (y ◇ (z ◇ w)) ◇ (x ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((z ◇ y) ◇ ((y ◇ x) ◇ x)) = ((x ◇ y) ◇ ((y ◇ x) ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (q0 q1:G), ((q0 ◇ q1) ◇ ((q1 ◇ q0) ◇ q0)) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((apc0 q0 q1 q0).symm).trans ((h q0 q1 q0).symm)
  have apc4 : forall (q2 q3 q4:G), ((q2 ◇ q3) ◇ ((((q3 ◇ q2) ◇ q2) ◇ q4) ◇ q4)) = (q4 ◇ ((q3 ◇ q2) ◇ q2)):=by
    intro q2 q3 q4
    exact ((cg (fun t => t ◇ ((((q3 ◇ q2) ◇ q2) ◇ q4) ◇ q4)) ((h q2 q3 q2).symm)).symm).trans ((h q4 ((q3 ◇ q2) ◇ q2) (q2 ◇ q3)).symm)
  have apc5 : forall (q5 q6 q7:G), (((q6 ◇ q5) ◇ q5) ◇ ((q7 ◇ q6) ◇ q6)) = ((q6 ◇ q7) ◇ (q5 ◇ q6)):=by
    intro q5 q6 q7
    exact (((cg (fun t => (q6 ◇ q7) ◇ t) (apc1 q5 q6)).symm).trans (((cg (fun t => (q6 ◇ q7) ◇ t) (cg (fun t => t ◇ ((q6 ◇ q5) ◇ q5)) ((h q5 q6 (q7 ◇ q6)).symm))).symm).trans (apc4 q6 q7 ((q6 ◇ q5) ◇ q5)))).symm
  have apc6 : forall (q8 q9:G), ((q8 ◇ q9) ◇ (q9 ◇ q8)) = (q8 ◇ q9):=by
    intro q8 q9
    exact ((apc5 q9 q8 q9).symm).trans ((h q8 q9 (q8 ◇ q9)).symm)
  have apc7 : forall (q10 q11:G), (q10 ◇ (q11 ◇ q10)) = (q10 ◇ q11):=by
    intro q10 q11
    exact ((((cg (fun t => (q10 ◇ q11) ◇ t) (apc6 (q11 ◇ q10) q10)).trans (apc1 q10 q11)).symm).trans ((((cg (fun t => (q10 ◇ q11) ◇ t) (cg (fun t => t ◇ (q10 ◇ (q11 ◇ q10))) (apc6 (q11 ◇ q10) q10))).symm).trans (apc4 q10 q11 (q10 ◇ (q11 ◇ q10)))).trans (apc6 q10 (q11 ◇ q10)))).symm
  have apc8 : forall (q12 q13:G), ((q13 ◇ q12) ◇ q12) = (q13 ◇ q12):=by
    intro q12 q13
    exact ((((cg (fun t => (q13 ◇ q12) ◇ t) (apc7 q12 q13)).trans (apc6 q13 q12)).symm).trans (((apc7 (q13 ◇ q12) (q12 ◇ (q13 ◇ q12))).symm).trans ((h (q13 ◇ q12) q12 q13).symm))).symm
  have apc9 : forall (q14 q15 q16:G), ((q14 ◇ q16) ◇ (q16 ◇ q15)) = (q15 ◇ q16):=by
    intro q14 q15 q16
    exact ((cg (fun t => (q14 ◇ q16) ◇ t) (apc8 q15 q16)).symm).trans (((cg (fun t => t ◇ ((q16 ◇ q15) ◇ q15)) (apc8 q16 q14)).symm).trans ((h q15 q16 (q14 ◇ q16)).symm))
  have apc10 : forall (q2 q3 q17 q18:G), ((q18 ◇ (q17 ◇ q3)) ◇ (q2 ◇ q3)) = ((q3 ◇ q2) ◇ (q17 ◇ q3)):=by
    intro q2 q3 q17 q18
    exact (((cg (fun t => (q18 ◇ (q17 ◇ q3)) ◇ t) (cg (fun t => (q2 ◇ q3) ◇ t) (apc8 q2 q3))).trans (cg (fun t => (q18 ◇ (q17 ◇ q3)) ◇ t) (apc9 q2 q2 q3))).symm).trans ((((cg (fun t => (q18 ◇ (q17 ◇ q3)) ◇ t) (cg (fun t => t ◇ ((q3 ◇ q2) ◇ q2)) ((h q2 q3 q17).symm))).symm).trans ((h ((q3 ◇ q2) ◇ q2) (q17 ◇ q3) q18).symm)).trans (cg (fun t => t ◇ (q17 ◇ q3)) (apc8 q2 q3)))
  have apc16 : forall (q14 q15 q19:G), (q19 ◇ (q14 ◇ q15)) = (q15 ◇ q14):=by
    intro q14 q15 q19
    exact (((cg (fun t => (q19 ◇ (q14 ◇ q15)) ◇ t) (apc8 q15 q14)).trans (apc8 (q14 ◇ q15) q19)).symm).trans ((((cg (fun t => (q19 ◇ (q14 ◇ q15)) ◇ t) (cg (fun t => t ◇ q15) (apc8 q15 q14))).symm).trans ((h q15 (q14 ◇ q15) q19).symm)).trans (apc7 q15 q14))
  have apc17 : forall (q20 q21 q22 q23:G), ((q21 ◇ q20) ◇ q22) = (q21 ◇ q20):=by
    intro q20 q21 q22 q23
    exact ((((cg (fun t => (q23 ◇ q22) ◇ t) (apc16 q21 q20 (q20 ◇ q21))).trans (apc16 q20 q21 (q23 ◇ q22))).symm).trans (((cg (fun t => (q23 ◇ q22) ◇ t) (apc10 q21 q20 q21 q22)).symm).trans ((h (q21 ◇ q20) q22 q23).symm))).symm
  have apc19 : forall (q24 q25 q26 q27:G), (q25 ◇ q26) = (q25 ◇ q24):=by
    intro q24 q25 q26 q27
    exact ((((((((cg (fun t => (q27 ◇ (q26 ◇ q25)) ◇ t) (cg (fun t => t ◇ ((q25 ◇ q24) ◇ q24)) (cg (fun t => (q24 ◇ q25) ◇ t) (apc17 q24 q25 q24 ((q25 ◇ q24) ◇ q24))))).trans (cg (fun t => (q27 ◇ (q26 ◇ q25)) ◇ t) (cg (fun t => ((q24 ◇ q25) ◇ (q25 ◇ q24)) ◇ t) (apc17 q24 q25 q24 ((q25 ◇ q24) ◇ q24))))).trans (cg (fun t => (q27 ◇ (q26 ◇ q25)) ◇ t) (cg (fun t => t ◇ (q25 ◇ q24)) (apc16 q25 q24 (q24 ◇ q25))))).trans (cg (fun t => t ◇ ((q24 ◇ q25) ◇ (q25 ◇ q24))) (apc16 q26 q25 q27))).trans (cg (fun t => (q25 ◇ q26) ◇ t) (apc16 q25 q24 (q24 ◇ q25)))).trans (apc16 q24 q25 (q25 ◇ q26))).symm).trans ((((cg (fun t => (q27 ◇ (q26 ◇ q25)) ◇ t) (cg (fun t => t ◇ ((q25 ◇ q24) ◇ q24)) (apc0 q24 q25 q26))).symm).trans ((h ((q25 ◇ q24) ◇ q24) (q26 ◇ q25) q27).symm)).trans ((cg (fun t => t ◇ (q26 ◇ q25)) (apc17 q24 q25 q24 ((q25 ◇ q24) ◇ q24))).trans (apc16 q26 q25 (q25 ◇ q24))))).symm
  have apc20 : forall (q24 q25 q26 q27:G), (q25 ◇ q25) = (q25 ◇ q24):=by
    intro q24 q25 q26 q27
    exact (((apc19 q24 q25 q26 q27).symm).trans (apc19 q25 q25 q26 q27)).symm
  have apc22 : forall (q28 q29 q30:G), (q29 ◇ q30) = (q28 ◇ q29):=by
    intro q28 q29 q30
    exact ((apc16 q30 q29 (q30 ◇ q29)).symm).trans ((apc20 ((q29 ◇ q28) ◇ q28) (q30 ◇ q29) q28 q28).trans ((h q28 q29 q30).symm))
  exact (apc22 (x ◇ w) x y).trans (apc22 (y ◇ (z ◇ w)) (x ◇ w) x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47390_to_48150 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47390_to_48150
