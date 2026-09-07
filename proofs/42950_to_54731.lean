-- Equation42950 → Equation54731
-- Recorded verdict: true
-- Premise: x ◇ y = z ◇ (x ◇ ((z ◇ y) ◇ y))
-- Conclusion: x ◇ (x ◇ x) = y ◇ ((z ◇ w) ◇ x)
-- Original submission SHA-256: 437c286f9e4ec869b1d2c3112f47d4494fd57cb11a405117831a6641188b5a72
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ (x ◇ ((z ◇ y) ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ x) = y ◇ ((z ◇ w) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (z ◇ (x ◇ ((z ◇ y) ◇ y))) = (x ◇ (x ◇ ((x ◇ y) ◇ y))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (x y z:G), (x ◇ (x ◇ ((x ◇ y) ◇ y))) = (x ◇ y):=by
    intro x y z
    exact ((h x y x).trans (apc0 x y x)).symm
  have apc2 : forall (q0 q1 q2:G), (q2 ◇ ((q2 ◇ ((q1 ◇ q0) ◇ q0)) ◇ q0)) = (q1 ◇ ((q1 ◇ q0) ◇ q0)):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) ((h (q2 ◇ ((q1 ◇ q0) ◇ q0)) q0 q1).symm)).symm).trans ((h q1 ((q1 ◇ q0) ◇ q0) q2).symm)
  have apc4 : forall (q3 q0 q1 q2:G), (q2 ◇ (q1 ◇ ((q3 ◇ q0) ◇ (q3 ◇ ((q2 ◇ q0) ◇ q0))))) = (q1 ◇ (q3 ◇ ((q2 ◇ q0) ◇ q0))):=by
    intro q3 q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q3 ◇ ((q2 ◇ q0) ◇ q0))) ((h q3 q0 q2).symm)))).symm).trans ((h q1 (q3 ◇ ((q2 ◇ q0) ◇ q0)) q2).symm)
  have apc5 : forall (q4 q5 q6:G), (q6 ◇ (q4 ◇ (((q4 ◇ q5) ◇ q5) ◇ q5))) = ((q4 ◇ q5) ◇ (q6 ◇ (q4 ◇ q5))):=by
    intro q4 q5 q6
    exact (((cg (fun t => (q4 ◇ q5) ◇ t) (cg (fun t => q6 ◇ t) ((h q4 q5 (q4 ◇ q5)).symm))).symm).trans (apc4 q4 q5 q6 (q4 ◇ q5))).symm
  have apc6 : forall (q7 q8:G), ((q7 ◇ q8) ◇ ((q7 ◇ q8) ◇ (q7 ◇ q8))) = (q7 ◇ q8):=by
    intro q7 q8
    exact ((apc5 q7 q8 (q7 ◇ q8)).symm).trans ((h q7 q8 (q7 ◇ q8)).symm)
  have apc7 : forall (q9 q10 q11:G), (q11 ◇ ((q9 ◇ q10) ◇ (q9 ◇ q10))) = ((q9 ◇ q10) ◇ (q11 ◇ (q9 ◇ q10))):=by
    intro q9 q10 q11
    exact (((cg (fun t => (q9 ◇ q10) ◇ t) (cg (fun t => q11 ◇ t) (apc6 q9 q10))).symm).trans (((cg (fun t => (q9 ◇ q10) ◇ t) (cg (fun t => q11 ◇ t) (cg (fun t => t ◇ ((q9 ◇ q10) ◇ (q9 ◇ q10))) (apc6 q9 q10)))).symm).trans ((h q11 ((q9 ◇ q10) ◇ (q9 ◇ q10)) (q9 ◇ q10)).symm))).symm
  have apc8 : forall (q12 q13:G), (((q13 ◇ q12) ◇ q12) ◇ (q13 ◇ ((q13 ◇ q12) ◇ q12))) = (((q13 ◇ q12) ◇ q12) ◇ q12):=by
    intro q12 q13
    exact ((apc7 (q13 ◇ q12) q12 q13).symm).trans ((h ((q13 ◇ q12) ◇ q12) q12 q13).symm)
  have apc9 : forall (q14 q15 q16:G), (q16 ◇ ((q16 ◇ (q14 ◇ q15)) ◇ ((q14 ◇ q15) ◇ (q14 ◇ q15)))) = ((q14 ◇ q15) ◇ (q14 ◇ q15)):=by
    intro q14 q15 q16
    exact ((cg (fun t => q16 ◇ t) (cg (fun t => t ◇ ((q14 ◇ q15) ◇ (q14 ◇ q15))) (cg (fun t => q16 ◇ t) (apc6 q14 q15)))).symm).trans ((((cg (fun t => q16 ◇ t) (cg (fun t => t ◇ ((q14 ◇ q15) ◇ (q14 ◇ q15))) (cg (fun t => q16 ◇ t) (cg (fun t => t ◇ ((q14 ◇ q15) ◇ (q14 ◇ q15))) (apc6 q14 q15))))).symm).trans (apc2 ((q14 ◇ q15) ◇ (q14 ◇ q15)) (q14 ◇ q15) q16)).trans ((cg (fun t => (q14 ◇ q15) ◇ t) (cg (fun t => t ◇ ((q14 ◇ q15) ◇ (q14 ◇ q15))) (apc6 q14 q15))).trans (cg (fun t => (q14 ◇ q15) ◇ t) (apc6 q14 q15))))
  have apc10 : forall (q17 q18:G), (((q17 ◇ q18) ◇ (q17 ◇ q18)) ◇ (q17 ◇ q18)) = ((q17 ◇ q18) ◇ (q17 ◇ q18)):=by
    intro q17 q18
    exact ((((apc9 q17 q18 (q17 ◇ q18)).symm).trans (apc7 (q17 ◇ q18) (q17 ◇ q18) (q17 ◇ q18))).trans (cg (fun t => ((q17 ◇ q18) ◇ (q17 ◇ q18)) ◇ t) (apc6 q17 q18))).symm
  have apc16 : forall (q19 q20 q21:G), (q21 ◇ (((q19 ◇ q20) ◇ (q21 ◇ (q19 ◇ q20))) ◇ (q19 ◇ q20))) = (q19 ◇ q20):=by
    intro q19 q20 q21
    exact ((cg (fun t => q21 ◇ t) (cg (fun t => t ◇ (q19 ◇ q20)) (apc7 q19 q20 q21))).symm).trans ((((cg (fun t => q21 ◇ t) (cg (fun t => t ◇ (q19 ◇ q20)) (cg (fun t => q21 ◇ t) (apc10 q19 q20)))).symm).trans (apc2 (q19 ◇ q20) (q19 ◇ q20) q21)).trans ((cg (fun t => (q19 ◇ q20) ◇ t) (apc10 q19 q20)).trans (apc6 q19 q20)))
  have apc17 : forall (q22 q23:G), ((((q23 ◇ q22) ◇ q22) ◇ q22) ◇ q22) = ((q23 ◇ q22) ◇ q22):=by
    intro q22 q23
    exact ((((apc16 (q23 ◇ q22) q22 q23).symm).trans ((h (((q23 ◇ q22) ◇ q22) ◇ (q23 ◇ ((q23 ◇ q22) ◇ q22))) q22 q23).symm)).trans (cg (fun t => t ◇ q22) (apc8 q22 q23))).symm
  have apc18 : forall (q24 q25:G), (((q24 ◇ q25) ◇ q25) ◇ q25) = ((q24 ◇ q25) ◇ q25):=by
    intro q24 q25
    exact (((apc6 (q24 ◇ q25) q25).symm).trans (((cg (fun t => ((q24 ◇ q25) ◇ q25) ◇ t) (cg (fun t => ((q24 ◇ q25) ◇ q25) ◇ t) (apc17 q25 q24))).symm).trans (apc1 ((q24 ◇ q25) ◇ q25) q25 q24))).symm
  have apc19 : forall (q26 q27:G), ((q26 ◇ q27) ◇ ((q26 ◇ q27) ◇ q27)) = (q26 ◇ ((q26 ◇ q27) ◇ q27)):=by
    intro q26 q27
    exact (((apc2 q27 q26 q26).symm).trans ((((cg (fun t => q26 ◇ t) (cg (fun t => t ◇ q27) (cg (fun t => q26 ◇ t) (apc18 q26 q27)))).symm).trans (apc2 q27 (q26 ◇ q27) q26)).trans (cg (fun t => (q26 ◇ q27) ◇ t) (apc18 q26 q27)))).symm
  have apc20 : forall (q28 q29:G), ((q29 ◇ q28) ◇ q28) = (q29 ◇ q28):=by
    intro q28 q29
    exact (((apc1 q29 q28 (q29 ◇ (q29 ◇ ((q29 ◇ q28) ◇ q28)))).symm).trans (((cg (fun t => q29 ◇ t) (apc19 q29 q28)).symm).trans ((h (q29 ◇ q28) q28 q29).symm))).symm
  have apc21 : forall (x y z q28 q29:G), (z ◇ (x ◇ (z ◇ y))) = (x ◇ y):=by
    intro x y z q28 q29
    exact ((h x y z).trans (cg (fun t => z ◇ t) (cg (fun t => x ◇ t) (apc20 y z)))).symm
  have apc22 : forall (q30 q31 q32:G), (q32 ◇ (q32 ◇ q30)) = (q31 ◇ (q31 ◇ q30)):=by
    intro q30 q31 q32
    exact (((cg (fun t => q32 ◇ t) ((h q32 q30 q31).symm)).symm).trans (apc21 q31 ((q31 ◇ q30) ◇ q30) q32 q30 q30)).trans (cg (fun t => q31 ◇ t) (apc20 q30 q31))
  have apc23 : forall (q30 q31 q32:G), (q31 ◇ (q31 ◇ q30)) = (q30 ◇ (q30 ◇ q30)):=by
    intro q30 q31 q32
    exact ((apc22 q30 q31 q30).symm).trans (apc22 q30 q30 q30)
  have apc24 : forall (q33 q34 q35:G), (q35 ◇ (q33 ◇ q34)) = (q33 ◇ (q35 ◇ q34)):=by
    intro q33 q34 q35
    exact (((cg (fun t => q35 ◇ t) ((h q33 q34 q35).symm)).symm).trans (apc23 (q33 ◇ ((q35 ◇ q34) ◇ q34)) q35 q33)).trans ((((cg (fun t => (q33 ◇ ((q35 ◇ q34) ◇ q34)) ◇ t) (cg (fun t => t ◇ (q33 ◇ ((q35 ◇ q34) ◇ q34))) (cg (fun t => q33 ◇ t) (apc20 q34 q35)))).trans (cg (fun t => (q33 ◇ ((q35 ◇ q34) ◇ q34)) ◇ t) (cg (fun t => (q33 ◇ (q35 ◇ q34)) ◇ t) (cg (fun t => q33 ◇ t) (apc20 q34 q35))))).trans (cg (fun t => t ◇ ((q33 ◇ (q35 ◇ q34)) ◇ (q33 ◇ (q35 ◇ q34)))) (cg (fun t => q33 ◇ t) (apc20 q34 q35)))).trans (apc6 q33 (q35 ◇ q34)))
  have apc25 : forall (q26 q27 q28 q29:G), ((q26 ◇ q27) ◇ (q26 ◇ q27)) = (q26 ◇ (q26 ◇ q27)):=by
    intro q26 q27 q28 q29
    exact ((cg (fun t => (q26 ◇ q27) ◇ t) (apc20 q27 q26)).symm).trans ((apc19 q26 q27).trans (cg (fun t => q26 ◇ t) (apc20 q27 q26)))
  have apc26 : forall (q36 q37 q38:G), ((q36 ◇ (q38 ◇ q37)) ◇ q37) = (q36 ◇ (q37 ◇ (q37 ◇ q37))):=by
    intro q36 q37 q38
    exact ((((apc24 q36 (q38 ◇ q37) q38).trans (cg (fun t => q36 ◇ t) (apc23 q37 q38 (q38 ◇ (q38 ◇ q37))))).symm).trans (((cg (fun t => q38 ◇ t) (apc20 (q38 ◇ q37) q36)).symm).trans (apc21 (q36 ◇ (q38 ◇ q37)) q37 q38 q36 q36))).symm
  have apc28 : forall (q39 q40 q41:G), (q39 ◇ (q39 ◇ (q40 ◇ q41))) = (q40 ◇ q41):=by
    intro q39 q40 q41
    exact ((cg (fun t => q39 ◇ t) (cg (fun t => q39 ◇ t) (apc20 q41 q40))).symm).trans (((apc22 ((q40 ◇ q41) ◇ q41) q39 q40).symm).trans ((h q40 q41 q40).symm))
  have apc29 : forall (x y z q28 q29:G), (x ◇ (y ◇ (y ◇ y))) = (x ◇ y):=by
    intro x y z q28 q29
    exact (((apc24 x (z ◇ y) z).trans (cg (fun t => x ◇ t) (apc23 y z (z ◇ (z ◇ y))))).symm).trans (((apc21 x y z x x).trans ((apc21 x y x x x).symm)).trans (apc28 x x y))
  have apc30 : forall (x y z q28 q29 q36 q37 q38:G), ((q36 ◇ (q38 ◇ q37)) ◇ q37) = (q36 ◇ q37):=by
    intro x y z q28 q29 q36 q37 q38
    exact (apc26 q36 q37 q38).trans (apc29 q36 q37 (q36 ◇ (q37 ◇ (q37 ◇ q37))) (q36 ◇ (q37 ◇ (q37 ◇ q37))) (q36 ◇ (q37 ◇ (q37 ◇ q37))))
  have apc32 : forall (q42 q43:G), (q43 ◇ q42) = (q42 ◇ q42):=by
    intro q42 q43
    exact (((apc30 ((q42 ◇ (q42 ◇ q42)) ◇ q42) ((q42 ◇ (q42 ◇ q42)) ◇ q42) ((q42 ◇ (q42 ◇ q42)) ◇ q42) ((q42 ◇ (q42 ◇ q42)) ◇ q42) ((q42 ◇ (q42 ◇ q42)) ◇ q42) q42 q42 q42).symm).trans (((cg (fun t => t ◇ q42) (apc23 q42 q43 q42)).symm).trans (apc30 q42 q42 q42 q42 q42 q43 q42 q43))).symm
  have apc33 : forall (q44 q45 q46:G), (q46 ◇ (q44 ◇ q45)) = (q44 ◇ (q44 ◇ q45)):=by
    intro q44 q45 q46
    exact (((apc25 q44 q45 ((q44 ◇ q45) ◇ (q44 ◇ q45)) ((q44 ◇ q45) ◇ (q44 ◇ q45))).symm).trans (((cg (fun t => t ◇ (q44 ◇ q45)) (apc28 q46 q44 q45)).symm).trans (apc30 q44 q44 q44 q44 q44 q46 (q44 ◇ q45) q46))).symm
  exact (calc
    (x ◇ (x ◇ x)) = (x ◇ (x ◇ x)):=rfl
    _ = (y ◇ ((z ◇ w) ◇ x)):=(((cg (fun t => y ◇ t) (cg (fun t => t ◇ x) (apc32 w z))).trans (cg (fun t => y ◇ t) (apc32 x (w ◇ w)))).trans (apc33 x x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42950_to_54731 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42950_to_54731
