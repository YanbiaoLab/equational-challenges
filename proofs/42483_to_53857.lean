-- Equation42483 → Equation53857
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ ((z ◇ y) ◇ y))
-- Conclusion: x ◇ (x ◇ x) = y ◇ (z ◇ (w ◇ w))
-- Original submission SHA-256: 0ebf771ee4e735a836602bea07e4b17fba937b604a048320267a01d3fe57a0b0
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
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ x) = y ◇ (z ◇ (w ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
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
  have pb : forall (q22 q23:G), ((q23 ◇ ((q23 ◇ q23) ◇ (q23 ◇ q23))) ◇ (q23 ◇ q23)) = (((q22 ◇ q23) ◇ q23) ◇ ((q22 ◇ q23) ◇ q23)):=by
    intro q22 q23
    exact ((cg (fun t => (q23 ◇ ((q23 ◇ q23) ◇ (q23 ◇ q23))) ◇ t) (p2 q22 q23)).symm).trans (pa q23 ((q22 ◇ q23) ◇ q23))
  have pc : forall (q22 q23:G), (((q23 ◇ q23) ◇ q23) ◇ ((q23 ◇ q23) ◇ q23)) = (((q22 ◇ q23) ◇ q23) ◇ ((q22 ◇ q23) ◇ q23)):=by
    intro q22 q23
    exact (((pb q22 q23).symm).trans (pb q23 q23)).symm
  have pd : forall (q24 q25:G), (q25 ◇ (((q24 ◇ q25) ◇ q25) ◇ ((q24 ◇ q25) ◇ q25))) = (((q25 ◇ q25) ◇ q25) ◇ ((q25 ◇ q25) ◇ q25)):=by
    intro q24 q25
    exact ((cg (fun t => q25 ◇ t) (pc q24 q25)).symm).trans ((h ((q25 ◇ q25) ◇ q25) q25 q25).symm)
  have pe : forall (q26 q27 q28:G), (((q26 ◇ (q28 ◇ q28)) ◇ (q28 ◇ q28)) ◇ (q27 ◇ ((q26 ◇ (q28 ◇ q28)) ◇ (q26 ◇ (q28 ◇ q28))))) = (q27 ◇ q27):=by
    intro q26 q27 q28
    exact ((cg (fun t => ((q26 ◇ (q28 ◇ q28)) ◇ (q28 ◇ q28)) ◇ t) (cg (fun t => q27 ◇ t) (p9 q28 q26 (q26 ◇ (q28 ◇ q28))))).symm).trans ((h q27 ((q26 ◇ (q28 ◇ q28)) ◇ (q28 ◇ q28)) q28).symm)
  have pf : forall (q29 q30 q31:G), ((q30 ◇ q30) ◇ (((q29 ◇ q30) ◇ q30) ◇ ((q29 ◇ q30) ◇ q30))) = (q30 ◇ q30):=by
    intro q29 q30 q31
    exact (((cg (fun t => t ◇ (((q29 ◇ q30) ◇ q30) ◇ ((q29 ◇ q30) ◇ q30))) (p1 q29 q30 q31)).symm).trans (p8 q31 ((q29 ◇ q30) ◇ q30))).trans (p1 q29 q30 q31)
  have pg : forall (q32 q33:G), (((q32 ◇ (q33 ◇ q33)) ◇ (q32 ◇ (q33 ◇ q33))) ◇ ((q32 ◇ (q33 ◇ q33)) ◇ (q32 ◇ (q33 ◇ q33)))) = ((q33 ◇ q33) ◇ (q33 ◇ q33)):=by
    intro q32 q33
    exact ((p6 (q32 ◇ (q33 ◇ q33))).symm).trans ((((cg (fun t => ((q32 ◇ (q33 ◇ q33)) ◇ (q32 ◇ (q33 ◇ q33))) ◇ t) (pe q32 ((q32 ◇ (q33 ◇ q33)) ◇ (q32 ◇ (q33 ◇ q33))) q33)).symm).trans (p5 (q32 ◇ (q33 ◇ q33)) ((q32 ◇ (q33 ◇ q33)) ◇ (q33 ◇ q33)))).trans (p7 q32 q33))
  have ph : forall (q34 q35 q36:G), ((q35 ◇ q35) ◇ (q36 ◇ (((q34 ◇ q35) ◇ q35) ◇ ((q34 ◇ q35) ◇ q35)))) = (q36 ◇ q36):=by
    intro q34 q35 q36
    exact ((cg (fun t => t ◇ (q36 ◇ (((q34 ◇ q35) ◇ q35) ◇ ((q34 ◇ q35) ◇ q35)))) (p0 q34 q35 ((q34 ◇ q35) ◇ q35))).symm).trans (pa ((q34 ◇ q35) ◇ q35) q36)
  have pi : forall (q37 q38:G), ((((q37 ◇ q38) ◇ q38) ◇ ((q37 ◇ q38) ◇ q38)) ◇ (((q37 ◇ q38) ◇ q38) ◇ ((q37 ◇ q38) ◇ q38))) = ((q38 ◇ q38) ◇ (q38 ◇ q38)):=by
    intro q37 q38
    exact ((p6 ((q37 ◇ q38) ◇ q38)).symm).trans (((cg (fun t => (((q37 ◇ q38) ◇ q38) ◇ ((q37 ◇ q38) ◇ q38)) ◇ t) (ph q37 q38 (((q37 ◇ q38) ◇ q38) ◇ ((q37 ◇ q38) ◇ q38)))).symm).trans (p5 ((q37 ◇ q38) ◇ q38) (q38 ◇ q38)))
  have pj : forall (q39 q40:G), (((q39 ◇ q40) ◇ q40) ◇ ((q40 ◇ q40) ◇ (q40 ◇ q40))) = (q40 ◇ q40):=by
    intro q39 q40
    exact ((cg (fun t => ((q39 ◇ q40) ◇ q40) ◇ t) (pi q39 q40)).symm).trans (p0 q39 q40 ((q39 ◇ q40) ◇ q40))
  have pk : forall (q41 q42:G), (((q41 ◇ q42) ◇ q42) ◇ ((q41 ◇ q42) ◇ q42)) = ((q42 ◇ q42) ◇ (q42 ◇ q42)):=by
    intro q41 q42
    exact (((cg (fun t => (q42 ◇ q42) ◇ t) (pj q41 q42)).symm).trans (p5 q42 ((q41 ◇ q42) ◇ q42))).symm
  have pl : forall (q30 q29 q31:G), ((q30 ◇ q30) ◇ (q30 ◇ q30)) = (q30 ◇ q30):=by
    intro q30 q29 q31
    exact ((p6 q30).symm).trans (((cg (fun t => (q30 ◇ q30) ◇ t) (pk q29 q30)).symm).trans (pf q29 q30 q31))
  have pm : forall (q10 q11:G), ((q10 ◇ q10) ◇ (q11 ◇ (q10 ◇ q10))) = (q11 ◇ q11):=by
    intro q10 q11
    exact ((cg (fun t => (q10 ◇ q10) ◇ t) (cg (fun t => q11 ◇ t) (pl q10 ((q10 ◇ q10) ◇ (q10 ◇ q10)) ((q10 ◇ q10) ◇ (q10 ◇ q10))))).symm).trans (p5 q10 q11)
  have pn : forall (q32 q33:G), ((q32 ◇ (q33 ◇ q33)) ◇ (q32 ◇ (q33 ◇ q33))) = (q33 ◇ q33):=by
    intro q32 q33
    exact ((pl (q32 ◇ (q33 ◇ q33)) (((q32 ◇ (q33 ◇ q33)) ◇ (q32 ◇ (q33 ◇ q33))) ◇ ((q32 ◇ (q33 ◇ q33)) ◇ (q32 ◇ (q33 ◇ q33)))) (((q32 ◇ (q33 ◇ q33)) ◇ (q32 ◇ (q33 ◇ q33))) ◇ ((q32 ◇ (q33 ◇ q33)) ◇ (q32 ◇ (q33 ◇ q33))))).symm).trans ((pg q32 q33).trans (pl q33 ((q33 ◇ q33) ◇ (q33 ◇ q33)) ((q33 ◇ q33) ◇ (q33 ◇ q33))))
  have po : forall (q25 q24:G), (q25 ◇ (q25 ◇ q25)) = (q25 ◇ q25):=by
    intro q25 q24
    exact ((cg (fun t => q25 ◇ t) (pl q25 ((q25 ◇ q25) ◇ (q25 ◇ q25)) ((q25 ◇ q25) ◇ (q25 ◇ q25)))).symm).trans ((((cg (fun t => q25 ◇ t) (pk q24 q25)).symm).trans ((pd q24 q25).trans (pk q25 q25))).trans (pl q25 ((q25 ◇ q25) ◇ (q25 ◇ q25)) ((q25 ◇ q25) ◇ (q25 ◇ q25))))
  have pp : forall (q43 q44 q45:G), ((q43 ◇ (q44 ◇ q44)) ◇ (q45 ◇ (q43 ◇ q43))) = (q45 ◇ q45):=by
    intro q43 q44 q45
    exact ((cg (fun t => (q43 ◇ (q44 ◇ q44)) ◇ t) (cg (fun t => q45 ◇ t) (pm q44 q43))).symm).trans (((cg (fun t => (q43 ◇ (q44 ◇ q44)) ◇ t) (cg (fun t => q45 ◇ t) (cg (fun t => t ◇ (q43 ◇ (q44 ◇ q44))) (pn q43 q44)))).symm).trans ((h q45 (q43 ◇ (q44 ◇ q44)) (q43 ◇ (q44 ◇ q44))).symm))
  have pq : forall (q46 q47:G), (q47 ◇ q47) = (q46 ◇ q46):=by
    intro q46 q47
    exact (((((cg (fun t => t ◇ ((q46 ◇ q46) ◇ (q46 ◇ q46))) (pl q46 ((q46 ◇ q46) ◇ (q46 ◇ q46)) ((q46 ◇ q46) ◇ (q46 ◇ q46)))).trans (cg (fun t => (q46 ◇ q46) ◇ t) (pl q46 ((q46 ◇ q46) ◇ (q46 ◇ q46)) ((q46 ◇ q46) ◇ (q46 ◇ q46))))).trans (pl q46 ((q46 ◇ q46) ◇ (q46 ◇ q46)) ((q46 ◇ q46) ◇ (q46 ◇ q46)))).symm).trans ((((cg (fun t => ((q46 ◇ q46) ◇ (q46 ◇ q46)) ◇ t) (pp q46 q47 (q46 ◇ q46))).symm).trans (pm (q46 ◇ q46) (q46 ◇ (q47 ◇ q47)))).trans (pn q46 q47))).symm
  have pr : forall (q48 q49:G), (q49 ◇ (q48 ◇ q48)) = (q49 ◇ q49):=by
    intro q48 q49
    exact ((cg (fun t => q49 ◇ t) (pq q48 q49)).symm).trans (po q49 q48)
  exact (pr x x).trans ((((cg (fun t => y ◇ t) (pr w z)).trans (pr z y)).trans (pq x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42483_to_53857 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42483_to_53857
