-- Equation49071 → Equation4521
-- Recorded verdict: true
-- Premise: x * y = ((z * x) * y) * (y * x)
-- Conclusion: x * (y * z) = (x * w) * w
-- Original submission SHA-256: 0e346921ad88d30ace36e7edb49a3a18c9f3622c902a14de77579513596c640d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ x) ◇ y) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (x ◇ w) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), ((q0 ◇ q1) ◇ ((q1 ◇ q0) ◇ q1)) = (q1 ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ ((q1 ◇ q0) ◇ q1)) ((h q0 q1 q0).symm)).symm).trans ((h q1 (q1 ◇ q0) (q0 ◇ q0)).symm)
  have apc1 : forall (x y z:G), (((z ◇ x) ◇ y) ◇ (y ◇ x)) = (((x ◇ x) ◇ y) ◇ (y ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc2 : forall (x y z:G), (((x ◇ x) ◇ y) ◇ (y ◇ x)) = (x ◇ y):=by
    intro x y z
    exact ((h x y x).trans (apc1 x y x)).symm
  have apc3 : forall (q2:G), ((q2 ◇ (q2 ◇ q2)) ◇ (q2 ◇ q2)) = (q2 ◇ (q2 ◇ q2)):=by
    intro q2
    exact (((cg (fun t => (q2 ◇ (q2 ◇ q2)) ◇ t) (apc2 q2 q2 q2)).symm).trans (apc0 q2 (q2 ◇ q2))).trans (apc0 q2 q2)
  have apc4 : forall (q3 q4:G), ((q4 ◇ (q4 ◇ q3)) ◇ (q3 ◇ q4)) = ((q4 ◇ q3) ◇ ((q4 ◇ q3) ◇ q4)):=by
    intro q3 q4
    exact ((cg (fun t => (q4 ◇ (q4 ◇ q3)) ◇ t) ((h q3 q4 q4).symm)).symm).trans (apc0 q4 (q4 ◇ q3))
  have apc5 : forall (q0 q5 q6:G), (((q0 ◇ q5) ◇ q6) ◇ (q6 ◇ (q5 ◇ q0))) = ((q5 ◇ q0) ◇ q6):=by
    intro q0 q5 q6
    exact ((cg (fun t => t ◇ (q6 ◇ (q5 ◇ q0))) (cg (fun t => t ◇ q6) ((h q0 q5 q0).symm))).symm).trans ((h (q5 ◇ q0) q6 ((q0 ◇ q0) ◇ q5)).symm)
  have apc6 : forall (q7:G), ((q7 ◇ (q7 ◇ q7)) ◇ (q7 ◇ (q7 ◇ q7))) = (q7 ◇ q7):=by
    intro q7
    exact (((cg (fun t => t ◇ (q7 ◇ (q7 ◇ q7))) (apc0 q7 q7)).symm).trans (apc4 q7 (q7 ◇ q7))).trans ((cg (fun t => ((q7 ◇ q7) ◇ q7) ◇ t) (apc2 q7 q7 (((q7 ◇ q7) ◇ q7) ◇ (q7 ◇ q7)))).trans (apc2 q7 q7 (((q7 ◇ q7) ◇ q7) ◇ (q7 ◇ q7))))
  have apc11 : forall (q8 q9 q10:G), (((q9 ◇ q10) ◇ ((q8 ◇ q9) ◇ q10)) ◇ (q9 ◇ q10)) = ((q10 ◇ q9) ◇ ((q8 ◇ q9) ◇ q10)):=by
    intro q8 q9 q10
    exact ((cg (fun t => ((q9 ◇ q10) ◇ ((q8 ◇ q9) ◇ q10)) ◇ t) ((h q9 q10 q8).symm)).symm).trans (apc5 q9 q10 ((q8 ◇ q9) ◇ q10))
  have apc13 : forall (q11:G), ((q11 ◇ (q11 ◇ q11)) ◇ ((q11 ◇ q11) ◇ (q11 ◇ q11))) = ((q11 ◇ q11) ◇ (q11 ◇ q11)):=by
    intro q11
    exact ((cg (fun t => t ◇ ((q11 ◇ q11) ◇ (q11 ◇ q11))) (apc3 q11)).symm).trans ((h (q11 ◇ q11) (q11 ◇ q11) q11).symm)
  have apc14 : forall (q12:G), ((q12 ◇ q12) ◇ ((q12 ◇ q12) ◇ (q12 ◇ q12))) = ((q12 ◇ q12) ◇ (q12 ◇ q12)):=by
    intro q12
    exact ((apc3 (q12 ◇ q12)).symm).trans ((((cg (fun t => ((q12 ◇ q12) ◇ ((q12 ◇ q12) ◇ (q12 ◇ q12))) ◇ t) (apc5 q12 q12 (q12 ◇ q12))).symm).trans (apc13 (q12 ◇ q12))).trans (apc5 q12 q12 (q12 ◇ q12)))
  have apc15 : forall (q13:G), (((q13 ◇ q13) ◇ (q13 ◇ q13)) ◇ (q13 ◇ q13)) = ((q13 ◇ q13) ◇ (q13 ◇ q13)):=by
    intro q13
    exact ((((cg (fun t => t ◇ ((q13 ◇ q13) ◇ (q13 ◇ q13))) (cg (fun t => t ◇ (q13 ◇ q13)) (apc5 q13 q13 (q13 ◇ q13)))).trans (apc2 (q13 ◇ q13) (q13 ◇ q13) ((((q13 ◇ q13) ◇ (q13 ◇ q13)) ◇ (q13 ◇ q13)) ◇ ((q13 ◇ q13) ◇ (q13 ◇ q13))))).symm).trans (((cg (fun t => ((((q13 ◇ q13) ◇ (q13 ◇ q13)) ◇ ((q13 ◇ q13) ◇ (q13 ◇ q13))) ◇ (q13 ◇ q13)) ◇ t) (apc14 q13)).symm).trans (apc2 ((q13 ◇ q13) ◇ (q13 ◇ q13)) (q13 ◇ q13) q13))).symm
  have apc29 : forall (q14 q15 q16 q17:G), ((((q16 ◇ q15) ◇ ((q14 ◇ q15) ◇ q16)) ◇ q17) ◇ (q17 ◇ (q15 ◇ q16))) = ((q15 ◇ q16) ◇ q17):=by
    intro q14 q15 q16 q17
    exact ((cg (fun t => t ◇ (q17 ◇ (q15 ◇ q16))) (cg (fun t => t ◇ q17) (apc11 q14 q15 q16))).symm).trans ((h (q15 ◇ q16) q17 ((q15 ◇ q16) ◇ ((q14 ◇ q15) ◇ q16))).symm)
  have apc30 : forall (q18 q19:G), (((q19 ◇ (q18 ◇ (q18 ◇ q18))) ◇ (q18 ◇ (q18 ◇ q18))) ◇ (q18 ◇ q18)) = (q18 ◇ q18):=by
    intro q18 q19
    exact (((cg (fun t => ((q19 ◇ (q18 ◇ (q18 ◇ q18))) ◇ (q18 ◇ (q18 ◇ q18))) ◇ t) (apc6 q18)).symm).trans ((h (q18 ◇ (q18 ◇ q18)) (q18 ◇ (q18 ◇ q18)) q19).symm)).trans (apc6 q18)
  have apc34 : forall (q20 q21:G), (((q21 ◇ q20) ◇ ((q21 ◇ q20) ◇ q21)) ◇ ((q20 ◇ q21) ◇ (q21 ◇ q20))) = ((q21 ◇ q20) ◇ (q20 ◇ q21)):=by
    intro q20 q21
    exact ((cg (fun t => t ◇ ((q20 ◇ q21) ◇ (q21 ◇ q20))) (apc4 q20 q21)).symm).trans ((h (q21 ◇ q20) (q20 ◇ q21) q21).symm)
  have apc65 : forall (q22 q23:G), (((q23 ◇ q23) ◇ ((q22 ◇ q23) ◇ q23)) ◇ ((q23 ◇ q23) ◇ (q23 ◇ q23))) = ((q23 ◇ q23) ◇ (q23 ◇ q23)):=by
    intro q22 q23
    exact ((cg (fun t => t ◇ ((q23 ◇ q23) ◇ (q23 ◇ q23))) (apc11 q22 q23 q23)).symm).trans (apc29 q22 q23 q23 (q23 ◇ q23))
  have apc79 : forall (q24 q25:G), (((q24 ◇ q24) ◇ (q24 ◇ q24)) ◇ ((q25 ◇ (q24 ◇ q24)) ◇ (q24 ◇ q24))) = ((q24 ◇ q24) ◇ (q24 ◇ q24)):=by
    intro q24 q25
    exact ((apc11 q25 (q24 ◇ q24) (q24 ◇ q24)).symm).trans ((((cg (fun t => (((q24 ◇ q24) ◇ (q24 ◇ q24)) ◇ ((q25 ◇ (q24 ◇ q24)) ◇ (q24 ◇ q24))) ◇ t) (apc5 q24 q24 (q24 ◇ q24))).symm).trans (apc65 q25 (q24 ◇ q24))).trans (apc5 q24 q24 (q24 ◇ q24)))
  have apc80 : forall (q26:G), (((q26 ◇ q26) ◇ (q26 ◇ q26)) ◇ (q26 ◇ (q26 ◇ q26))) = ((q26 ◇ q26) ◇ (q26 ◇ q26)):=by
    intro q26
    exact ((cg (fun t => ((q26 ◇ q26) ◇ (q26 ◇ q26)) ◇ t) (apc3 q26)).symm).trans (apc79 q26 q26)
  have apc81 : forall (q27:G), ((q27 ◇ q27) ◇ (q27 ◇ q27)) = (q27 ◇ q27):=by
    intro q27
    exact (((cg (fun t => t ◇ (q27 ◇ q27)) (apc80 q27)).trans (apc15 q27)).symm).trans (((cg (fun t => t ◇ (q27 ◇ q27)) (cg (fun t => t ◇ (q27 ◇ (q27 ◇ q27))) (apc80 q27))).symm).trans (apc30 q27 ((q27 ◇ q27) ◇ (q27 ◇ q27))))
  have apc82 : forall (q28:G), (q28 ◇ (q28 ◇ q28)) = (q28 ◇ q28):=by
    intro q28
    exact (((cg (fun t => t ◇ (q28 ◇ q28)) (apc0 q28 q28)).trans (apc3 q28)).symm).trans ((((cg (fun t => ((q28 ◇ q28) ◇ ((q28 ◇ q28) ◇ q28)) ◇ t) (apc81 q28)).symm).trans (apc34 q28 q28)).trans (apc81 q28))
  have apc83 : forall (q29:G), ((q29 ◇ q29) ◇ q29) = (q29 ◇ q29):=by
    intro q29
    exact ((((cg (fun t => t ◇ (q29 ◇ q29)) (cg (fun t => t ◇ q29) (apc81 q29))).trans (apc2 q29 q29 (((q29 ◇ q29) ◇ q29) ◇ (q29 ◇ q29)))).symm).trans (((cg (fun t => (((q29 ◇ q29) ◇ (q29 ◇ q29)) ◇ q29) ◇ t) (apc82 q29)).symm).trans (apc2 (q29 ◇ q29) q29 q29))).symm
  have apc84 : forall (q30 q31:G), ((q31 ◇ q31) ◇ ((q30 ◇ q31) ◇ q31)) = (q31 ◇ q31):=by
    intro q30 q31
    exact (((cg (fun t => t ◇ (q31 ◇ q31)) (apc11 q30 q31 q31)).trans (apc11 q30 q31 q31)).symm).trans ((((cg (fun t => (((q31 ◇ q31) ◇ ((q30 ◇ q31) ◇ q31)) ◇ (q31 ◇ q31)) ◇ t) (apc81 q31)).symm).trans (apc29 q30 q31 q31 (q31 ◇ q31))).trans (apc81 q31))
  have apc85 : forall (q32 q33:G), (q33 ◇ ((q32 ◇ q33) ◇ q33)) = (q33 ◇ q33):=by
    intro q32 q33
    exact (((apc84 (q32 ◇ q33) q33).symm).trans (((cg (fun t => t ◇ (((q32 ◇ q33) ◇ q33) ◇ q33)) (apc84 q32 q33)).symm).trans ((h q33 ((q32 ◇ q33) ◇ q33) q33).symm))).symm
  have apc92 : forall (q34 q35:G), (((q35 ◇ (q34 ◇ q35)) ◇ q35) ◇ (q35 ◇ q35)) = (((q34 ◇ q35) ◇ q35) ◇ q35):=by
    intro q34 q35
    exact ((cg (fun t => ((q35 ◇ (q34 ◇ q35)) ◇ q35) ◇ t) (apc85 q34 q35)).symm).trans (apc5 q35 (q34 ◇ q35) q35)
  have apc93 : forall (q36 q37:G), ((((q36 ◇ q37) ◇ q37) ◇ q37) ◇ q37) = (q37 ◇ q37):=by
    intro q36 q37
    exact ((((cg (fun t => t ◇ (q37 ◇ q37)) (apc83 q37)).trans (apc81 q37)).symm).trans (((cg (fun t => t ◇ (q37 ◇ q37)) (cg (fun t => t ◇ q37) (apc85 q36 q37))).symm).trans (apc92 (q36 ◇ q37) q37))).symm
  have apc94 : forall (q38 q39:G), (((q38 ◇ q39) ◇ q39) ◇ ((q38 ◇ q39) ◇ q39)) = (q39 ◇ q39):=by
    intro q38 q39
    exact (((((cg (fun t => t ◇ ((q38 ◇ q39) ◇ q39)) (cg (fun t => t ◇ ((q38 ◇ q39) ◇ q39)) (apc84 q38 q39))).trans (cg (fun t => t ◇ ((q38 ◇ q39) ◇ q39)) (apc84 q38 q39))).trans (apc84 q38 q39)).symm).trans (((cg (fun t => t ◇ ((q38 ◇ q39) ◇ q39)) (cg (fun t => t ◇ ((q38 ◇ q39) ◇ q39)) (cg (fun t => t ◇ ((q38 ◇ q39) ◇ q39)) (apc85 q38 q39)))).symm).trans (apc93 q39 ((q38 ◇ q39) ◇ q39)))).symm
  have apc98 : forall (q32 q40 q41:G), (((q40 ◇ q40) ◇ q41) ◇ (q41 ◇ ((q32 ◇ q40) ◇ q40))) = (((q32 ◇ q40) ◇ q40) ◇ q41):=by
    intro q32 q40 q41
    exact ((cg (fun t => t ◇ (q41 ◇ ((q32 ◇ q40) ◇ q40))) (cg (fun t => t ◇ q41) (apc84 q32 q40))).symm).trans ((h ((q32 ◇ q40) ◇ q40) q41 (q40 ◇ q40)).symm)
  have apc99 : forall (q42 q43:G), (((q42 ◇ q43) ◇ q43) ◇ q43) = (q43 ◇ q43):=by
    intro q42 q43
    exact ((((cg (fun t => (q43 ◇ q43) ◇ t) (apc85 q42 q43)).trans (apc81 q43)).symm).trans (((cg (fun t => t ◇ (q43 ◇ ((q42 ◇ q43) ◇ q43))) (apc83 q43)).symm).trans (apc98 q42 q43 q43))).symm
  have apc101 : forall (q44 q45:G), (((q44 ◇ q45) ◇ (q45 ◇ q44)) ◇ (q45 ◇ q44)) = ((q45 ◇ q44) ◇ (q45 ◇ q44)):=by
    intro q44 q45
    exact ((cg (fun t => t ◇ (q45 ◇ q44)) (cg (fun t => t ◇ (q45 ◇ q44)) ((h q44 q45 q44).symm))).symm).trans (apc99 ((q44 ◇ q44) ◇ q45) (q45 ◇ q44))
  have apc103 : forall (q46 q47:G), ((q47 ◇ (q46 ◇ q46)) ◇ (q47 ◇ (q46 ◇ q46))) = ((q46 ◇ q46) ◇ q47):=by
    intro q46 q47
    exact (((apc5 q46 q46 q47).symm).trans (((cg (fun t => t ◇ (q47 ◇ (q46 ◇ q46))) (apc5 q46 q46 q47)).symm).trans (apc101 (q46 ◇ q46) q47))).symm
  have apc104 : forall (q48 q49:G), ((q48 ◇ q48) ◇ (q49 ◇ (q48 ◇ q48))) = (q48 ◇ q48):=by
    intro q48 q49
    exact (((apc103 q48 (q49 ◇ (q48 ◇ q48))).symm).trans (apc94 q49 (q48 ◇ q48))).trans (apc81 q48)
  have apc105 : forall (q50 q51:G), ((q50 ◇ q50) ◇ q51) = (q50 ◇ q50):=by
    intro q50 q51
    exact ((((cg (fun t => t ◇ (q51 ◇ (q50 ◇ q50))) (apc104 q50 q51)).trans (apc104 q50 q51)).symm).trans ((((cg (fun t => t ◇ (q51 ◇ (q50 ◇ q50))) (cg (fun t => t ◇ (q51 ◇ (q50 ◇ q50))) (apc104 q50 q51))).symm).trans (apc99 (q50 ◇ q50) (q51 ◇ (q50 ◇ q50)))).trans (apc103 q50 q51))).symm
  have apc106 : forall (x y z q50 q51:G), (x ◇ y) = (x ◇ x):=by
    intro x y z q50 q51
    exact ((((cg (fun t => t ◇ (y ◇ x)) (apc105 x y)).trans (apc105 x (y ◇ x))).symm).trans (apc2 x y x)).symm
  have apc108 : forall (q52 q53:G), ((q53 ◇ q52) ◇ (q53 ◇ q52)) = (q52 ◇ q52):=by
    intro q52 q53
    exact (((apc105 (q53 ◇ q52) ((q53 ◇ q52) ◇ q52)).symm).trans ((h q52 (q53 ◇ q52) q53).symm)).trans (apc106 q52 (q53 ◇ q52) (q52 ◇ (q53 ◇ q52)) (q52 ◇ (q53 ◇ q52)) (q52 ◇ (q53 ◇ q52)))
  have apc109 : forall (q54 q55 q56:G), ((q55 ◇ q54) ◇ q56) = (q54 ◇ q54):=by
    intro q54 q55 q56
    exact (((((cg (fun t => t ◇ (q56 ◇ (q55 ◇ q54))) (apc105 q54 q56)).trans (cg (fun t => (q54 ◇ q54) ◇ t) (apc106 q56 (q55 ◇ q54) (q56 ◇ (q55 ◇ q54)) (q56 ◇ (q55 ◇ q54)) (q56 ◇ (q55 ◇ q54))))).trans (apc105 q54 (q56 ◇ q56))).symm).trans (((cg (fun t => t ◇ (q56 ◇ (q55 ◇ q54))) (cg (fun t => t ◇ q56) (apc108 q54 q55))).symm).trans ((h (q55 ◇ q54) q56 (q55 ◇ q54)).symm))).symm
  exact (calc
    (x ◇ (y ◇ z)) = (x ◇ x):=apc106 x (y ◇ z) w w w
    _ = ((x ◇ x) ◇ w):=(apc109 x x w).symm
    _ = ((x ◇ w) ◇ w):=(cg (fun t => t ◇ w) (apc106 x w w w w)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49071_to_4521 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49071_to_4521
