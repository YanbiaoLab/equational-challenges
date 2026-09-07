-- Equation21899 → Equation13441
-- Recorded verdict: true
-- Premise: x = (y ◇ (z ◇ x)) ◇ (z ◇ (x ◇ z))
-- Conclusion: x = y ◇ ((z ◇ (w ◇ (u ◇ z))) ◇ y)
-- Original submission SHA-256: 273c67f8dc2ef3251a6850aaf154ea774ec77cf7a5f6c030e5cd82914ad45fc3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ x)) ◇ (z ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = y ◇ ((z ◇ (w ◇ (u ◇ z))) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc4 : forall (q0 q1 q2 q3:G), ((q3 ◇ ((q2 ◇ (q0 ◇ q2)) ◇ (q1 ◇ (q2 ◇ q0)))) ◇ ((q2 ◇ (q0 ◇ q2)) ◇ q0)) = (q1 ◇ (q2 ◇ q0)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (q3 ◇ ((q2 ◇ (q0 ◇ q2)) ◇ (q1 ◇ (q2 ◇ q0)))) ◇ t) (cg (fun t => (q2 ◇ (q0 ◇ q2)) ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h (q1 ◇ (q2 ◇ q0)) q3 (q2 ◇ (q0 ◇ q2))).symm)
  have apc6 : forall (q4 q5 q6:G), ((q6 ◇ q5) ◇ ((q5 ◇ (q4 ◇ q5)) ◇ q4)) = (q4 ◇ (q5 ◇ q4)):=by
    intro q4 q5 q6
    exact ((cg (fun t => t ◇ ((q5 ◇ (q4 ◇ q5)) ◇ q4)) (cg (fun t => q6 ◇ t) ((h q5 q5 q4).symm))).symm).trans (apc4 q4 q4 q5 q6)
  have apc9 : forall (q0 q1 q2 q3:G), ((q3 ◇ q0) ◇ ((q1 ◇ (q2 ◇ q0)) ◇ ((q2 ◇ (q0 ◇ q2)) ◇ (q1 ◇ (q2 ◇ q0))))) = (q2 ◇ (q0 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ ((q1 ◇ (q2 ◇ q0)) ◇ ((q2 ◇ (q0 ◇ q2)) ◇ (q1 ◇ (q2 ◇ q0))))) (cg (fun t => q3 ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h (q2 ◇ (q0 ◇ q2)) q3 (q1 ◇ (q2 ◇ q0))).symm)
  have apc10 : forall (q7 q8 q9:G), (q7 ◇ (((q8 ◇ (q7 ◇ q8)) ◇ (q9 ◇ (q8 ◇ (q7 ◇ q8)))) ◇ q9)) = (q9 ◇ ((q8 ◇ (q7 ◇ q8)) ◇ q9)):=by
    intro q7 q8 q9
    exact ((cg (fun t => t ◇ (((q8 ◇ (q7 ◇ q8)) ◇ (q9 ◇ (q8 ◇ (q7 ◇ q8)))) ◇ q9)) ((h q7 q7 q8).symm)).symm).trans (apc6 q9 (q8 ◇ (q7 ◇ q8)) (q7 ◇ (q8 ◇ q7)))
  have apc15 : forall (q10 q11 q12:G), ((q10 ◇ (q12 ◇ q11)) ◇ ((q12 ◇ (q11 ◇ q12)) ◇ (q10 ◇ (q12 ◇ q11)))) = (q11 ◇ (((q12 ◇ (q11 ◇ q12)) ◇ q11) ◇ (q10 ◇ (q12 ◇ q11)))):=by
    intro q10 q11 q12
    exact (((cg (fun t => q11 ◇ t) (cg (fun t => t ◇ (q10 ◇ (q12 ◇ q11))) (cg (fun t => (q12 ◇ (q11 ◇ q12)) ◇ t) ((h q11 q10 q12).symm)))).symm).trans (apc10 q11 q12 (q10 ◇ (q12 ◇ q11)))).symm
  have apc16 : forall (q13 q14:G), (q13 ◇ (((q14 ◇ (q13 ◇ q14)) ◇ q13) ◇ (q13 ◇ (q14 ◇ q13)))) = ((q13 ◇ (q14 ◇ q13)) ◇ q14):=by
    intro q13 q14
    exact (((cg (fun t => (q13 ◇ (q14 ◇ q13)) ◇ t) ((h q14 q14 q13).symm)).symm).trans (apc15 q13 q13 q14)).symm
  have apc18 : forall (q0 q1 q2 q3 q10 q11 q12:G), ((q3 ◇ q0) ◇ (q0 ◇ (((q2 ◇ (q0 ◇ q2)) ◇ q0) ◇ (q1 ◇ (q2 ◇ q0))))) = (q2 ◇ (q0 ◇ q2)):=by
    intro q0 q1 q2 q3 q10 q11 q12
    exact ((cg (fun t => (q3 ◇ q0) ◇ t) (apc15 q1 q0 q2)).symm).trans (apc9 q0 q1 q2 q3)
  have apc19 : forall (q15 q16 q17:G), ((q17 ◇ q15) ◇ (q15 ◇ ((q16 ◇ q15) ◇ (q15 ◇ (q16 ◇ q15))))) = (q16 ◇ (q15 ◇ q16)):=by
    intro q15 q16 q17
    exact ((cg (fun t => (q17 ◇ q15) ◇ t) (cg (fun t => q15 ◇ t) (apc6 (q16 ◇ q15) q15 (q16 ◇ (q15 ◇ q16))))).symm).trans (apc18 q15 (q15 ◇ ((q16 ◇ q15) ◇ q15)) q16 q17 q15 q15 q15)
  have apc20 : forall (q18 q19 q20:G), ((q18 ◇ ((q19 ◇ q18) ◇ q18)) ◇ ((q19 ◇ q18) ◇ (q18 ◇ ((q19 ◇ q18) ◇ q18)))) = (q18 ◇ ((q19 ◇ q18) ◇ q18)):=by
    intro q18 q19 q20
    exact ((((cg (fun t => (q20 ◇ (q19 ◇ q18)) ◇ t) (apc16 (q19 ◇ q18) q18)).trans (apc6 q18 (q19 ◇ q18) q20)).symm).trans (((cg (fun t => (q20 ◇ (q19 ◇ q18)) ◇ t) (cg (fun t => (q19 ◇ q18) ◇ t) (cg (fun t => ((q18 ◇ ((q19 ◇ q18) ◇ q18)) ◇ (q19 ◇ q18)) ◇ t) (apc6 (q19 ◇ q18) q18 q19)))).symm).trans (apc19 (q19 ◇ q18) (q18 ◇ ((q19 ◇ q18) ◇ q18)) q20))).symm
  have apc23 : forall (q21 q22:G), ((q21 ◇ ((q22 ◇ q21) ◇ q21)) ◇ ((q22 ◇ q21) ◇ (q21 ◇ (q22 ◇ q21)))) = (q21 ◇ ((q22 ◇ q21) ◇ q21)):=by
    intro q21 q22
    exact ((cg (fun t => (q21 ◇ ((q22 ◇ q21) ◇ q21)) ◇ t) (apc6 (q22 ◇ q21) q21 q22)).symm).trans (((cg (fun t => t ◇ ((q22 ◇ q21) ◇ ((q21 ◇ ((q22 ◇ q21) ◇ q21)) ◇ (q22 ◇ q21)))) (apc20 q21 q22 q21)).symm).trans ((h (q21 ◇ ((q22 ◇ q21) ◇ q21)) (q21 ◇ ((q22 ◇ q21) ◇ q21)) (q22 ◇ q21)).symm))
  have apc24 : forall (q23 q24:G), (q24 ◇ ((q23 ◇ q24) ◇ q24)) = q24:=by
    intro q23 q24
    exact ((apc23 q24 q23).symm).trans ((h q24 q24 (q23 ◇ q24)).symm)
  have apc26 : forall (q25 q26:G), (q26 ◇ (q25 ◇ q26)) = q26:=by
    intro q25 q26
    exact (((apc24 ((q25 ◇ q26) ◇ (q26 ◇ (q25 ◇ q26))) q26).symm).trans ((((cg (fun t => q26 ◇ t) (cg (fun t => (((q25 ◇ q26) ◇ (q26 ◇ (q25 ◇ q26))) ◇ q26) ◇ t) (apc24 q25 q26))).symm).trans (apc16 q26 (q25 ◇ q26))).trans (cg (fun t => t ◇ (q25 ◇ q26)) (apc24 q25 q26)))).symm
  have apc27 : forall (q7 q8 q9 q25 q26:G), (q7 ◇ (q8 ◇ q9)) = q9:=by
    intro q7 q8 q9 q25 q26
    exact ((((cg (fun t => q7 ◇ t) (cg (fun t => t ◇ q9) (cg (fun t => (q8 ◇ (q7 ◇ q8)) ◇ t) (cg (fun t => q9 ◇ t) (apc26 q7 q8))))).trans (cg (fun t => q7 ◇ t) (cg (fun t => t ◇ q9) (cg (fun t => t ◇ (q9 ◇ q8)) (apc26 q7 q8))))).trans (cg (fun t => q7 ◇ t) (cg (fun t => t ◇ q9) (apc26 q9 q8)))).symm).trans ((apc10 q7 q8 q9).trans ((cg (fun t => q9 ◇ t) (cg (fun t => t ◇ q9) (apc26 q7 q8))).trans (apc26 q8 q9)))
  have apc29 : forall (q13 q14 q25 q26:G), (q13 ◇ q14) = q13:=by
    intro q13 q14 q25 q26
    exact (((((cg (fun t => q13 ◇ t) (cg (fun t => t ◇ (q13 ◇ (q14 ◇ q13))) (cg (fun t => t ◇ q13) (apc26 q13 q14)))).trans (cg (fun t => q13 ◇ t) (cg (fun t => (q14 ◇ q13) ◇ t) (apc26 q14 q13)))).trans (apc26 (q14 ◇ q13) q13)).symm).trans ((apc16 q13 q14).trans (cg (fun t => t ◇ q14) (apc26 q14 q13)))).symm
  have apc30 : forall (q27 q28 q29 q30:G), q28 = q27:=by
    intro q27 q28 q29 q30
    exact (((((((cg (fun t => t ◇ ((q29 ◇ q30) ◇ q30)) (cg (fun t => q28 ◇ t) (cg (fun t => t ◇ q27) (apc29 q29 q30 (q29 ◇ q30) (q29 ◇ q30))))).trans (cg (fun t => (q28 ◇ (q29 ◇ q27)) ◇ t) (cg (fun t => t ◇ q30) (apc29 q29 q30 (q29 ◇ q30) (q29 ◇ q30))))).trans (cg (fun t => t ◇ (q29 ◇ q30)) (cg (fun t => q28 ◇ t) (apc29 q29 q27 (q29 ◇ q27) (q29 ◇ q27))))).trans (cg (fun t => (q28 ◇ q29) ◇ t) (apc29 q29 q30 (q29 ◇ q30) (q29 ◇ q30)))).trans (cg (fun t => t ◇ q29) (apc29 q28 q29 (q28 ◇ q29) (q28 ◇ q29)))).trans (apc29 q28 q29 (q28 ◇ q29) (q28 ◇ q29))).symm).trans (((cg (fun t => (q28 ◇ ((q29 ◇ q30) ◇ q27)) ◇ t) (cg (fun t => (q29 ◇ q30) ◇ t) (apc27 q27 q29 q30 q29 q29))).symm).trans ((h q27 q28 (q29 ◇ q30)).symm))
  exact (apc30 x x x x).trans ((apc30 x (y ◇ ((z ◇ (w ◇ (u ◇ z))) ◇ y)) x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_21899_to_13441 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_21899_to_13441
