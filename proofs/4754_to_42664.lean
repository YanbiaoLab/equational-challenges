-- Equation4754 → Equation42664
-- Recorded verdict: true
-- Premise: x = x ◇ (y ◇ (x ◇ (x ◇ (z ◇ y))))
-- Conclusion: x ◇ y = x ◇ (y ◇ ((y ◇ z) ◇ z))
-- Original submission SHA-256: 10c33a42f0fa08c5a7481f483fc96867e7ba1ead572d2ed0c2471870549f2746
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ (x ◇ (x ◇ (z ◇ y))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = x ◇ (y ◇ ((y ◇ z) ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1:G), (q1 ◇ ((q1 ◇ (q0 ◇ q1)) ◇ q1)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) ((h q1 q1 q0).symm))).symm).trans ((h q1 (q1 ◇ (q0 ◇ q1)) q1).symm)
  have apc1 : forall (q2:G), (q2 ◇ (q2 ◇ q2)) = q2:=by
    intro q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q2) (apc0 q2 q2))).symm).trans (apc0 (q2 ◇ (q2 ◇ q2)) q2)
  have apc2 : forall (q3:G), (q3 ◇ q3) = q3:=by
    intro q3
    exact ((cg (fun t => q3 ◇ t) (apc1 q3)).symm).trans (((cg (fun t => q3 ◇ t) (cg (fun t => q3 ◇ t) (cg (fun t => q3 ◇ t) (apc1 q3)))).symm).trans ((h q3 q3 q3).symm))
  have apc3 : forall (q3 q4:G), ((q4 ◇ q3) ◇ (q3 ◇ (q4 ◇ q3))) = (q4 ◇ q3):=by
    intro q3 q4
    exact ((cg (fun t => (q4 ◇ q3) ◇ t) (cg (fun t => q3 ◇ t) (apc1 (q4 ◇ q3)))).symm).trans ((h (q4 ◇ q3) q3 q4).symm)
  have apc4 : forall (q5 q6:G), (q5 ◇ (q6 ◇ (q5 ◇ (q5 ◇ q6)))) = q5:=by
    intro q5 q6
    exact ((cg (fun t => q5 ◇ t) (cg (fun t => q6 ◇ t) (cg (fun t => q5 ◇ t) (cg (fun t => q5 ◇ t) (apc2 q6))))).symm).trans ((h q5 q6 q6).symm)
  have apc6 : forall (q7 q8:G), ((q8 ◇ (q7 ◇ q8)) ◇ (q7 ◇ q8)) = (q8 ◇ (q7 ◇ q8)):=by
    intro q7 q8
    exact ((cg (fun t => (q8 ◇ (q7 ◇ q8)) ◇ t) (apc3 q8 q7)).symm).trans (apc3 (q7 ◇ q8) q8)
  have apc8 : forall (q9 q0 q10 q1:G), (q10 ◇ ((q9 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q9)))) ◇ (q10 ◇ (q10 ◇ q1)))) = q10:=by
    intro q9 q0 q10 q1
    exact ((cg (fun t => q10 ◇ t) (cg (fun t => (q9 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q9)))) ◇ t) (cg (fun t => q10 ◇ t) (cg (fun t => q10 ◇ t) ((h q1 q9 q0).symm))))).symm).trans ((h q10 (q9 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q9)))) q1).symm)
  have apc15 : forall (q11 q12:G), ((q11 ◇ (q12 ◇ q11)) ◇ (q11 ◇ (q11 ◇ (q12 ◇ q11)))) = (q11 ◇ (q12 ◇ q11)):=by
    intro q11 q12
    exact ((cg (fun t => (q11 ◇ (q12 ◇ q11)) ◇ t) (cg (fun t => q11 ◇ t) (apc2 (q11 ◇ (q12 ◇ q11))))).symm).trans (((cg (fun t => (q11 ◇ (q12 ◇ q11)) ◇ t) (cg (fun t => q11 ◇ t) (cg (fun t => (q11 ◇ (q12 ◇ q11)) ◇ t) (apc6 q12 q11)))).symm).trans ((h (q11 ◇ (q12 ◇ q11)) q11 q12).symm))
  have apc18 : forall (q13 q14 q15:G), (q15 ◇ ((q13 ◇ (q14 ◇ q13)) ◇ (q15 ◇ (q15 ◇ (q14 ◇ q13))))) = q15:=by
    intro q13 q14 q15
    exact ((cg (fun t => q15 ◇ t) (cg (fun t => (q13 ◇ (q14 ◇ q13)) ◇ t) (cg (fun t => q15 ◇ t) (cg (fun t => q15 ◇ t) (apc3 q13 q14))))).symm).trans ((h q15 (q13 ◇ (q14 ◇ q13)) (q14 ◇ q13)).symm)
  have apc19 : forall (q16 q17:G), (q17 ◇ (q17 ◇ (q16 ◇ q17))) = q17:=by
    intro q16 q17
    exact ((cg (fun t => q17 ◇ t) (apc15 q17 q16)).symm).trans (apc18 q17 q16 q17)
  have apc20 : forall (q18 q19:G), (q19 ◇ ((q18 ◇ q19) ◇ q19)) = q19:=by
    intro q18 q19
    exact ((cg (fun t => q19 ◇ t) (cg (fun t => (q18 ◇ q19) ◇ t) (apc2 q19))).symm).trans (((cg (fun t => q19 ◇ t) (cg (fun t => (q18 ◇ q19) ◇ t) (cg (fun t => q19 ◇ t) (apc19 q18 q19)))).symm).trans ((h q19 (q18 ◇ q19) q19).symm))
  have apc26 : forall (q20 q21 q22:G), (q22 ◇ (((q20 ◇ q21) ◇ q21) ◇ (q22 ◇ (q22 ◇ q21)))) = q22:=by
    intro q20 q21 q22
    exact ((cg (fun t => q22 ◇ t) (cg (fun t => t ◇ (q22 ◇ (q22 ◇ q21))) (cg (fun t => (q20 ◇ q21) ◇ t) (apc2 q21)))).symm).trans (((cg (fun t => q22 ◇ t) (cg (fun t => t ◇ (q22 ◇ (q22 ◇ q21))) (cg (fun t => (q20 ◇ q21) ◇ t) (cg (fun t => q21 ◇ t) (apc19 q20 q21))))).symm).trans (apc8 (q20 ◇ q21) q21 q22 q21))
  have apc28 : forall (q23 q24 q25:G), (q25 ◇ (((q24 ◇ (q23 ◇ q25)) ◇ (q23 ◇ q25)) ◇ q25)) = q25:=by
    intro q23 q24 q25
    exact ((cg (fun t => q25 ◇ t) (cg (fun t => ((q24 ◇ (q23 ◇ q25)) ◇ (q23 ◇ q25)) ◇ t) (apc19 q23 q25))).symm).trans (apc26 q24 (q23 ◇ q25) q25)
  have apc42 : forall (q26 q27:G), ((q27 ◇ (q27 ◇ q26)) ◇ (q27 ◇ (q27 ◇ (q27 ◇ q26)))) = (q27 ◇ (q27 ◇ q26)):=by
    intro q26 q27
    exact ((cg (fun t => (q27 ◇ (q27 ◇ q26)) ◇ t) (cg (fun t => t ◇ (q27 ◇ (q27 ◇ q26))) (apc4 q27 q26))).symm).trans (((cg (fun t => (q27 ◇ (q27 ◇ q26)) ◇ t) (cg (fun t => t ◇ (q27 ◇ (q27 ◇ q26))) (cg (fun t => t ◇ (q26 ◇ (q27 ◇ (q27 ◇ q26)))) (apc4 q27 q26)))).symm).trans (apc28 q26 q27 (q27 ◇ (q27 ◇ q26))))
  have apc49 : forall (q28 q29 q30:G), ((((q28 ◇ q29) ◇ q29) ◇ (q30 ◇ (q30 ◇ q29))) ◇ q30) = (((q28 ◇ q29) ◇ q29) ◇ (q30 ◇ (q30 ◇ q29))):=by
    intro q28 q29 q30
    exact ((cg (fun t => (((q28 ◇ q29) ◇ q29) ◇ (q30 ◇ (q30 ◇ q29))) ◇ t) (apc26 q28 q29 q30)).symm).trans (((cg (fun t => (((q28 ◇ q29) ◇ q29) ◇ (q30 ◇ (q30 ◇ q29))) ◇ t) (cg (fun t => t ◇ (((q28 ◇ q29) ◇ q29) ◇ (q30 ◇ (q30 ◇ q29)))) (apc26 q28 q29 q30))).symm).trans (apc20 q30 (((q28 ◇ q29) ◇ q29) ◇ (q30 ◇ (q30 ◇ q29)))))
  have apc69 : forall (q23 q24 q25:G), (q25 ◇ (((q24 ◇ (q25 ◇ (q23 ◇ q25))) ◇ (q25 ◇ (q23 ◇ q25))) ◇ q25)) = q25:=by
    intro q23 q24 q25
    exact ((cg (fun t => q25 ◇ t) (cg (fun t => ((q24 ◇ (q25 ◇ (q23 ◇ q25))) ◇ (q25 ◇ (q23 ◇ q25))) ◇ t) (apc2 q25))).symm).trans (((cg (fun t => q25 ◇ t) (cg (fun t => ((q24 ◇ (q25 ◇ (q23 ◇ q25))) ◇ (q25 ◇ (q23 ◇ q25))) ◇ t) (cg (fun t => q25 ◇ t) (apc19 q23 q25)))).symm).trans (apc26 q24 (q25 ◇ (q23 ◇ q25)) q25))
  have apc114 : forall (q31 q32 q33:G), ((q32 ◇ (q33 ◇ (q33 ◇ (q31 ◇ (q32 ◇ (q32 ◇ q31)))))) ◇ q33) = (q32 ◇ (q33 ◇ (q33 ◇ (q31 ◇ (q32 ◇ (q32 ◇ q31)))))):=by
    intro q31 q32 q33
    exact ((cg (fun t => t ◇ q33) (cg (fun t => t ◇ (q33 ◇ (q33 ◇ (q31 ◇ (q32 ◇ (q32 ◇ q31)))))) (apc4 q32 q31))).symm).trans ((((cg (fun t => t ◇ q33) (cg (fun t => t ◇ (q33 ◇ (q33 ◇ (q31 ◇ (q32 ◇ (q32 ◇ q31)))))) (cg (fun t => t ◇ (q31 ◇ (q32 ◇ (q32 ◇ q31)))) (apc4 q32 q31)))).symm).trans (apc49 q32 (q31 ◇ (q32 ◇ (q32 ◇ q31))) q33)).trans ((cg (fun t => t ◇ (q33 ◇ (q33 ◇ (q31 ◇ (q32 ◇ (q32 ◇ q31)))))) (cg (fun t => t ◇ (q31 ◇ (q32 ◇ (q32 ◇ q31)))) (apc4 q32 q31))).trans (cg (fun t => t ◇ (q33 ◇ (q33 ◇ (q31 ◇ (q32 ◇ (q32 ◇ q31)))))) (apc4 q32 q31))))
  have apc163 : forall (q34 q35 q36:G), (q36 ◇ ((q35 ◇ (q35 ◇ (q35 ◇ q34))) ◇ (q36 ◇ (q36 ◇ (q35 ◇ (q35 ◇ q34)))))) = q36:=by
    intro q34 q35 q36
    exact ((cg (fun t => q36 ◇ t) (cg (fun t => (q35 ◇ (q35 ◇ (q35 ◇ q34))) ◇ t) (cg (fun t => q36 ◇ t) (cg (fun t => q36 ◇ t) (apc42 q34 q35))))).symm).trans ((h q36 (q35 ◇ (q35 ◇ (q35 ◇ q34))) (q35 ◇ (q35 ◇ q34))).symm)
  have apc164 : forall (q37 q38:G), (q38 ◇ (q38 ◇ (q38 ◇ (q38 ◇ q37)))) = q38:=by
    intro q37 q38
    exact ((cg (fun t => q38 ◇ t) (apc42 (q38 ◇ q37) q38)).symm).trans (apc163 q37 q38 q38)
  have apc167 : forall (q39 q40 q41:G), (q41 ◇ (((q40 ◇ q39) ◇ q40) ◇ (q41 ◇ (q41 ◇ q40)))) = q41:=by
    intro q39 q40 q41
    exact ((cg (fun t => q41 ◇ t) (cg (fun t => t ◇ (q41 ◇ (q41 ◇ q40))) (cg (fun t => (q40 ◇ q39) ◇ t) (apc164 q39 q40)))).symm).trans (apc8 (q40 ◇ q39) q40 q41 q40)
  have apc188 : forall (q42 q43:G), (((q43 ◇ q42) ◇ q43) ◇ ((q43 ◇ q42) ◇ ((q43 ◇ q42) ◇ q43))) = ((q43 ◇ q42) ◇ q43):=by
    intro q42 q43
    exact ((cg (fun t => ((q43 ◇ q42) ◇ q43) ◇ t) (cg (fun t => t ◇ ((q43 ◇ q42) ◇ q43)) (apc167 q42 q43 (q43 ◇ q42)))).symm).trans (((cg (fun t => ((q43 ◇ q42) ◇ q43) ◇ t) (cg (fun t => t ◇ ((q43 ◇ q42) ◇ q43)) (cg (fun t => t ◇ (((q43 ◇ q42) ◇ q43) ◇ ((q43 ◇ q42) ◇ ((q43 ◇ q42) ◇ q43)))) (apc167 q42 q43 (q43 ◇ q42))))).symm).trans (apc69 (q43 ◇ q42) (q43 ◇ q42) ((q43 ◇ q42) ◇ q43)))
  have apc189 : forall (q44 q45:G), ((q45 ◇ q44) ◇ ((q45 ◇ q44) ◇ q45)) = (q45 ◇ q44):=by
    intro q44 q45
    exact ((cg (fun t => (q45 ◇ q44) ◇ t) (apc188 q44 q45)).symm).trans (apc167 q44 q45 (q45 ◇ q44))
  have apc191 : forall (q46 q47:G), ((q47 ◇ q46) ◇ (q47 ◇ (q47 ◇ q46))) = (q47 ◇ q46):=by
    intro q46 q47
    exact ((cg (fun t => (q47 ◇ q46) ◇ t) (cg (fun t => q47 ◇ t) (apc2 (q47 ◇ q46)))).symm).trans (((cg (fun t => (q47 ◇ q46) ◇ t) (cg (fun t => q47 ◇ t) (cg (fun t => (q47 ◇ q46) ◇ t) (apc189 q46 q47)))).symm).trans ((h (q47 ◇ q46) q47 (q47 ◇ q46)).symm))
  have apc214 : forall (q48 q49 q50:G), (q50 ◇ ((q49 ◇ (q49 ◇ q48)) ◇ (q50 ◇ (q50 ◇ (q49 ◇ q48))))) = q50:=by
    intro q48 q49 q50
    exact ((cg (fun t => q50 ◇ t) (cg (fun t => t ◇ (q50 ◇ (q50 ◇ (q49 ◇ q48)))) (cg (fun t => q49 ◇ t) (apc2 (q49 ◇ q48))))).symm).trans (((cg (fun t => q50 ◇ t) (cg (fun t => t ◇ (q50 ◇ (q50 ◇ (q49 ◇ q48)))) (cg (fun t => q49 ◇ t) (cg (fun t => (q49 ◇ q48) ◇ t) (apc189 q48 q49))))).symm).trans (apc8 q49 (q49 ◇ q48) q50 (q49 ◇ q48)))
  have apc215 : forall (q51 q52:G), (q52 ◇ (q52 ◇ (q52 ◇ q51))) = q52:=by
    intro q51 q52
    exact ((cg (fun t => q52 ◇ t) (apc191 (q52 ◇ q51) q52)).symm).trans (apc214 q51 q52 q52)
  have apc216 : forall (q53 q54:G), (q54 ◇ (q53 ◇ q54)) = q54:=by
    intro q53 q54
    exact ((cg (fun t => q54 ◇ t) (cg (fun t => q53 ◇ t) (apc215 q53 q54))).symm).trans ((h q54 q53 q54).symm)
  have apc217 : forall (q55 q56:G), ((q56 ◇ q55) ◇ q55) = (q56 ◇ q55):=by
    intro q55 q56
    exact (((cg (fun t => t ◇ q55) (cg (fun t => q56 ◇ t) (apc215 (q56 ◇ (q56 ◇ q55)) q55))).symm).trans (apc114 q55 q56 q55)).trans (cg (fun t => q56 ◇ t) (apc215 (q56 ◇ (q56 ◇ q55)) q55))
  have apc219 : forall (q57 q58 q59:G), (q59 ◇ ((q57 ◇ q58) ◇ (q59 ◇ (q59 ◇ q58)))) = q59:=by
    intro q57 q58 q59
    exact ((cg (fun t => q59 ◇ t) (cg (fun t => t ◇ (q59 ◇ (q59 ◇ q58))) (cg (fun t => q57 ◇ t) (apc215 q57 q58)))).symm).trans (apc8 q57 q58 q59 q58)
  have apc221 : forall (q60 q61:G), (q61 ◇ (q61 ◇ q60)) = q61:=by
    intro q60 q61
    exact ((cg (fun t => q61 ◇ t) (apc216 q61 (q61 ◇ q60))).symm).trans (apc219 q61 q60 q61)
  exact (calc
    (x ◇ y) = (x ◇ y):=rfl
    _ = (x ◇ (y ◇ ((y ◇ z) ◇ z))):=((cg (fun t => x ◇ t) (cg (fun t => y ◇ t) (apc217 z y))).trans (cg (fun t => x ◇ t) (apc221 z y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4754_to_42664 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4754_to_42664
