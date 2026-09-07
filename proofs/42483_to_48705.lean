-- Equation42483 → Equation48705
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ ((z ◇ y) ◇ y))
-- Conclusion: x ◇ x = ((y ◇ z) ◇ z) ◇ (x ◇ x)
-- Original submission SHA-256: cb58faccb61d0b84c536a555493a829fb3d61be61443db6fccdec3bf8f334130
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (x ◇ ((z ◇ y) ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = ((y ◇ z) ◇ z) ◇ (x ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q0 q1 q2:G), (((q0 ◇ q1) ◇ q1) ◇ ((q2 ◇ ((q0 ◇ q1) ◇ q1)) ◇ (q2 ◇ ((q0 ◇ q1) ◇ q1)))) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q0 ◇ q1) ◇ q1) ◇ t) ((h (q2 ◇ ((q0 ◇ q1) ◇ q1)) q1 q0).symm)).symm).trans ((h q1 ((q0 ◇ q1) ◇ q1) q2).symm)
  have p1 : forall (q3 q4 q5:G), (((q5 ◇ ((q3 ◇ q4) ◇ q4)) ◇ ((q3 ◇ q4) ◇ q4)) ◇ ((q5 ◇ ((q3 ◇ q4) ◇ q4)) ◇ ((q3 ◇ q4) ◇ q4))) = (q4 ◇ q4):=by
    intro q3 q4 q5
    exact (((p0 q3 q4 (q5 ◇ ((q3 ◇ q4) ◇ q4))).symm).trans ((h ((q5 ◇ ((q3 ◇ q4) ◇ q4)) ◇ ((q3 ◇ q4) ◇ q4)) ((q3 ◇ q4) ◇ q4) q5).symm)).symm
  have p2 : forall (q6 q7:G), (((q6 ◇ q7) ◇ q7) ◇ (q7 ◇ q7)) = (q7 ◇ q7):=by
    intro q6 q7
    exact ((cg (fun t => ((q6 ◇ q7) ◇ q7) ◇ t) (p1 q6 q7 q6)).symm).trans (p0 q6 q7 (q6 ◇ ((q6 ◇ q7) ◇ q7)))
  have p3 : forall (q8 q0 q1 q2:G), ((q8 ◇ ((q0 ◇ q2) ◇ q2)) ◇ (q1 ◇ ((q8 ◇ q8) ◇ (q8 ◇ ((q0 ◇ q2) ◇ q2))))) = (q1 ◇ q1):=by
    intro q8 q0 q1 q2
    exact ((cg (fun t => (q8 ◇ ((q0 ◇ q2) ◇ q2)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q8 ◇ ((q0 ◇ q2) ◇ q2))) ((h q8 q2 q0).symm)))).symm).trans ((h q1 (q8 ◇ ((q0 ◇ q2) ◇ q2)) q2).symm)
  have p4 : forall (q9:G), (((q9 ◇ q9) ◇ (q9 ◇ q9)) ◇ ((q9 ◇ q9) ◇ (q9 ◇ q9))) = ((q9 ◇ q9) ◇ (q9 ◇ q9)):=by
    intro q9
    exact ((cg (fun t => t ◇ ((q9 ◇ q9) ◇ (q9 ◇ q9))) (cg (fun t => t ◇ (q9 ◇ q9)) (p2 q9 q9))).symm).trans (p2 ((q9 ◇ q9) ◇ q9) (q9 ◇ q9))
  have p5 : forall (q10 q11:G), ((q10 ◇ q10) ◇ (q11 ◇ ((q10 ◇ q10) ◇ (q10 ◇ q10)))) = (q11 ◇ q11):=by
    intro q10 q11
    exact ((cg (fun t => (q10 ◇ q10) ◇ t) (cg (fun t => q11 ◇ t) (cg (fun t => t ◇ (q10 ◇ q10)) (p2 q10 q10)))).symm).trans ((h q11 (q10 ◇ q10) ((q10 ◇ q10) ◇ q10)).symm)
  have p6 : forall (q12:G), ((q12 ◇ q12) ◇ ((q12 ◇ q12) ◇ (q12 ◇ q12))) = ((q12 ◇ q12) ◇ (q12 ◇ q12)):=by
    intro q12
    exact (((cg (fun t => (q12 ◇ q12) ◇ t) (p4 q12)).symm).trans (p5 q12 ((q12 ◇ q12) ◇ (q12 ◇ q12)))).trans (p4 q12)
  have p7 : forall (q13 q14:G), (((q13 ◇ (q14 ◇ q14)) ◇ (q14 ◇ q14)) ◇ ((q13 ◇ (q14 ◇ q14)) ◇ (q14 ◇ q14))) = ((q14 ◇ q14) ◇ (q14 ◇ q14)):=by
    intro q13 q14
    exact (((p6 q14).symm).trans (((cg (fun t => (q14 ◇ q14) ◇ t) (p2 q13 (q14 ◇ q14))).symm).trans (p5 q14 ((q13 ◇ (q14 ◇ q14)) ◇ (q14 ◇ q14))))).symm
  have p8 : forall (q15 q16:G), ((((q15 ◇ q16) ◇ q16) ◇ ((q15 ◇ q16) ◇ q16)) ◇ (q16 ◇ q16)) = (((q15 ◇ q16) ◇ q16) ◇ ((q15 ◇ q16) ◇ q16)):=by
    intro q15 q16
    exact ((cg (fun t => (((q15 ◇ q16) ◇ q16) ◇ ((q15 ◇ q16) ◇ q16)) ◇ t) (p0 q15 q16 ((q15 ◇ q16) ◇ q16))).symm).trans (p3 ((q15 ◇ q16) ◇ q16) q15 ((q15 ◇ q16) ◇ q16) q16)
  have p9 : forall (q17 q18 q19:G), ((q17 ◇ ((q18 ◇ (q17 ◇ q17)) ◇ (q17 ◇ q17))) ◇ (q19 ◇ (q17 ◇ q17))) = (q19 ◇ q19):=by
    intro q17 q18 q19
    exact ((cg (fun t => (q17 ◇ ((q18 ◇ (q17 ◇ q17)) ◇ (q17 ◇ q17))) ◇ t) (cg (fun t => q19 ◇ t) ((h q17 (q17 ◇ q17) q18).symm))).symm).trans (p3 q17 q18 q19 (q17 ◇ q17))
  have pa : forall (q20 q21:G), ((q20 ◇ ((q20 ◇ q20) ◇ (q20 ◇ q20))) ◇ (q21 ◇ (q20 ◇ q20))) = (q21 ◇ q21):=by
    intro q20 q21
    exact ((cg (fun t => t ◇ (q21 ◇ (q20 ◇ q20))) (cg (fun t => q20 ◇ t) (cg (fun t => t ◇ (q20 ◇ q20)) (p2 q20 q20)))).symm).trans (p9 q20 ((q20 ◇ q20) ◇ q20) q21)
  have pb : forall (q22 q23 q24:G), (((q22 ◇ (q24 ◇ q24)) ◇ (q24 ◇ q24)) ◇ (q23 ◇ ((q22 ◇ (q24 ◇ q24)) ◇ (q22 ◇ (q24 ◇ q24))))) = (q23 ◇ q23):=by
    intro q22 q23 q24
    exact ((cg (fun t => ((q22 ◇ (q24 ◇ q24)) ◇ (q24 ◇ q24)) ◇ t) (cg (fun t => q23 ◇ t) (p9 q24 q22 (q22 ◇ (q24 ◇ q24))))).symm).trans ((h q23 ((q22 ◇ (q24 ◇ q24)) ◇ (q24 ◇ q24)) q24).symm)
  have pc : forall (q25 q26 q27:G), ((q26 ◇ q26) ◇ (((q25 ◇ q26) ◇ q26) ◇ ((q25 ◇ q26) ◇ q26))) = (q26 ◇ q26):=by
    intro q25 q26 q27
    exact (((cg (fun t => t ◇ (((q25 ◇ q26) ◇ q26) ◇ ((q25 ◇ q26) ◇ q26))) (p1 q25 q26 q27)).symm).trans (p8 q27 ((q25 ◇ q26) ◇ q26))).trans (p1 q25 q26 q27)
  have pd : forall (q28 q29:G), (((q28 ◇ (q29 ◇ q29)) ◇ (q28 ◇ (q29 ◇ q29))) ◇ ((q28 ◇ (q29 ◇ q29)) ◇ (q28 ◇ (q29 ◇ q29)))) = ((q29 ◇ q29) ◇ (q29 ◇ q29)):=by
    intro q28 q29
    exact ((p6 (q28 ◇ (q29 ◇ q29))).symm).trans ((((cg (fun t => ((q28 ◇ (q29 ◇ q29)) ◇ (q28 ◇ (q29 ◇ q29))) ◇ t) (pb q28 ((q28 ◇ (q29 ◇ q29)) ◇ (q28 ◇ (q29 ◇ q29))) q29)).symm).trans (p5 (q28 ◇ (q29 ◇ q29)) ((q28 ◇ (q29 ◇ q29)) ◇ (q29 ◇ q29)))).trans (p7 q28 q29))
  have pe : forall (q30 q31 q32:G), ((q31 ◇ q31) ◇ (q32 ◇ (((q30 ◇ q31) ◇ q31) ◇ ((q30 ◇ q31) ◇ q31)))) = (q32 ◇ q32):=by
    intro q30 q31 q32
    exact ((cg (fun t => t ◇ (q32 ◇ (((q30 ◇ q31) ◇ q31) ◇ ((q30 ◇ q31) ◇ q31)))) (p0 q30 q31 ((q30 ◇ q31) ◇ q31))).symm).trans (pa ((q30 ◇ q31) ◇ q31) q32)
  have pf : forall (q33 q34:G), ((((q33 ◇ q34) ◇ q34) ◇ ((q33 ◇ q34) ◇ q34)) ◇ (((q33 ◇ q34) ◇ q34) ◇ ((q33 ◇ q34) ◇ q34))) = ((q34 ◇ q34) ◇ (q34 ◇ q34)):=by
    intro q33 q34
    exact ((p6 ((q33 ◇ q34) ◇ q34)).symm).trans (((cg (fun t => (((q33 ◇ q34) ◇ q34) ◇ ((q33 ◇ q34) ◇ q34)) ◇ t) (pe q33 q34 (((q33 ◇ q34) ◇ q34) ◇ ((q33 ◇ q34) ◇ q34)))).symm).trans (p5 ((q33 ◇ q34) ◇ q34) (q34 ◇ q34)))
  have pg : forall (q35 q36:G), (((q35 ◇ q36) ◇ q36) ◇ ((q36 ◇ q36) ◇ (q36 ◇ q36))) = (q36 ◇ q36):=by
    intro q35 q36
    exact ((cg (fun t => ((q35 ◇ q36) ◇ q36) ◇ t) (pf q35 q36)).symm).trans (p0 q35 q36 ((q35 ◇ q36) ◇ q36))
  have ph : forall (q37 q38:G), (((q37 ◇ q38) ◇ q38) ◇ ((q37 ◇ q38) ◇ q38)) = ((q38 ◇ q38) ◇ (q38 ◇ q38)):=by
    intro q37 q38
    exact (((cg (fun t => (q38 ◇ q38) ◇ t) (pg q37 q38)).symm).trans (p5 q38 ((q37 ◇ q38) ◇ q38))).symm
  have pi : forall (q26 q25 q27:G), ((q26 ◇ q26) ◇ (q26 ◇ q26)) = (q26 ◇ q26):=by
    intro q26 q25 q27
    exact ((p6 q26).symm).trans (((cg (fun t => (q26 ◇ q26) ◇ t) (ph q25 q26)).symm).trans (pc q25 q26 q27))
  have pj : forall (q10 q11:G), ((q10 ◇ q10) ◇ (q11 ◇ (q10 ◇ q10))) = (q11 ◇ q11):=by
    intro q10 q11
    exact ((cg (fun t => (q10 ◇ q10) ◇ t) (cg (fun t => q11 ◇ t) (pi q10 ((q10 ◇ q10) ◇ (q10 ◇ q10)) ((q10 ◇ q10) ◇ (q10 ◇ q10))))).symm).trans (p5 q10 q11)
  have pk : forall (q28 q29:G), ((q28 ◇ (q29 ◇ q29)) ◇ (q28 ◇ (q29 ◇ q29))) = (q29 ◇ q29):=by
    intro q28 q29
    exact ((pi (q28 ◇ (q29 ◇ q29)) (((q28 ◇ (q29 ◇ q29)) ◇ (q28 ◇ (q29 ◇ q29))) ◇ ((q28 ◇ (q29 ◇ q29)) ◇ (q28 ◇ (q29 ◇ q29)))) (((q28 ◇ (q29 ◇ q29)) ◇ (q28 ◇ (q29 ◇ q29))) ◇ ((q28 ◇ (q29 ◇ q29)) ◇ (q28 ◇ (q29 ◇ q29))))).symm).trans ((pd q28 q29).trans (pi q29 ((q29 ◇ q29) ◇ (q29 ◇ q29)) ((q29 ◇ q29) ◇ (q29 ◇ q29))))
  have pl : forall (q39 q40 q41:G), ((q39 ◇ (q40 ◇ q40)) ◇ (q41 ◇ (q39 ◇ q39))) = (q41 ◇ q41):=by
    intro q39 q40 q41
    exact ((cg (fun t => (q39 ◇ (q40 ◇ q40)) ◇ t) (cg (fun t => q41 ◇ t) (pj q40 q39))).symm).trans (((cg (fun t => (q39 ◇ (q40 ◇ q40)) ◇ t) (cg (fun t => q41 ◇ t) (cg (fun t => t ◇ (q39 ◇ (q40 ◇ q40))) (pk q39 q40)))).symm).trans ((h q41 (q39 ◇ (q40 ◇ q40)) (q39 ◇ (q40 ◇ q40))).symm))
  have pm : forall (q42 q43:G), (q43 ◇ q43) = (q42 ◇ q42):=by
    intro q42 q43
    exact (((((cg (fun t => t ◇ ((q42 ◇ q42) ◇ (q42 ◇ q42))) (pi q42 ((q42 ◇ q42) ◇ (q42 ◇ q42)) ((q42 ◇ q42) ◇ (q42 ◇ q42)))).trans (cg (fun t => (q42 ◇ q42) ◇ t) (pi q42 ((q42 ◇ q42) ◇ (q42 ◇ q42)) ((q42 ◇ q42) ◇ (q42 ◇ q42))))).trans (pi q42 ((q42 ◇ q42) ◇ (q42 ◇ q42)) ((q42 ◇ q42) ◇ (q42 ◇ q42)))).symm).trans ((((cg (fun t => ((q42 ◇ q42) ◇ (q42 ◇ q42)) ◇ t) (pl q42 q43 (q42 ◇ q42))).symm).trans (pj (q42 ◇ q42) (q42 ◇ (q43 ◇ q43)))).trans (pk q42 q43))).symm
  have pn : forall (q44 q45 q46:G), (((q45 ◇ q46) ◇ q46) ◇ (q44 ◇ q44)) = (q46 ◇ q46):=by
    intro q44 q45 q46
    exact ((cg (fun t => ((q45 ◇ q46) ◇ q46) ◇ t) (pm q44 q46)).symm).trans (p2 q45 q46)
  exact (pm z x).trans ((pn x y z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42483_to_48705 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42483_to_48705
