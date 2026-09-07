-- Equation45486 → Equation46755
-- Recorded verdict: true
-- Premise: x * y = y * (((z * y) * y) * x)
-- Conclusion: x * y = (z * w) * (u * (x * y))
-- Original submission SHA-256: d7fef0a4d3e803711e5e85196d935f0091ad3a91965f176a079355de78ef15c4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (((z ◇ y) ◇ y) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ w) ◇ (u ◇ (x ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f : G → G) {a b : G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc2 : forall (q0 q1 q2 q3 q4 : G), ((q1 ◇ (((q2 ◇ q1) ◇ q1) ◇ q0)) ◇ q3)=(q3 ◇ (((q4 ◇ q3) ◇ q3) ◇ (q0 ◇ q1))):=by
    intro q0 q1 q2 q3 q4
    exact (((rfl).symm).trans ((((cg (fun t => q3 ◇ t) (cg (fun t => ((q4 ◇ q3) ◇ q3) ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h (q1 ◇ (((q2 ◇ q1) ◇ q1) ◇ q0)) q3 q4).symm)).trans (rfl))).symm
  have apc3 : forall (q5 q6 q7 q8 : G), (q7 ◇ (((q8 ◇ q7) ◇ q7) ◇ (q5 ◇ q6)))=((q5 ◇ q6) ◇ q7):=by
    intro q5 q6 q7 q8
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ q7) ((h q5 q6 q5).symm)).symm).trans (apc2 q5 q6 q5 q7 q8)).trans (rfl))).symm
  have apc4 : forall (q9 q10 q11 q12 : G), ((q10 ◇ (((q11 ◇ q10) ◇ q10) ◇ q9)) ◇ q12)=((q9 ◇ q10) ◇ q12):=by
    intro q9 q10 q11 q12
    exact ((rfl).symm).trans (((((apc2 q9 q10 q11 q12 q9).symm).symm).trans ((h (q9 ◇ q10) q12 q9).symm)).trans (rfl))
  have apc5 : forall (q13 q14 q15 q16 : G), (q16 ◇ ((((q13 ◇ q14) ◇ q16) ◇ q16) ◇ q15))=(q15 ◇ q16):=by
    intro q13 q14 q15 q16
    exact ((rfl).symm).trans ((((cg (fun t => q16 ◇ t) (cg (fun t => t ◇ q15) (cg (fun t => t ◇ q16) (apc4 q13 q14 q13 q16)))).symm).trans ((h q15 q16 (q14 ◇ (((q13 ◇ q14) ◇ q14) ◇ q13))).symm)).trans (rfl))
  have apc6 : forall (q17 q18 q19 q20 q21 q22 : G), ((q20 ◇ q21) ◇ (q18 ◇ (((q19 ◇ q18) ◇ q18) ◇ q17)))=((q20 ◇ q21) ◇ (q17 ◇ q18)):=by
    intro q17 q18 q19 q20 q21 q22
    exact (((apc4 q20 q21 q22 (q17 ◇ q18)).symm).trans ((((cg (fun t => (q21 ◇ (((q22 ◇ q21) ◇ q21) ◇ q20)) ◇ t) ((h q17 q18 q19).symm)).symm).trans (apc4 q20 q21 q22 (q18 ◇ (((q19 ◇ q18) ◇ q18) ◇ q17)))).trans (rfl))).symm
  have apc7 : forall (q23 q24 q25 q26 : G), ((((q24 ◇ ((q26 ◇ q25) ◇ q25)) ◇ ((q26 ◇ q25) ◇ q25)) ◇ q23) ◇ q25)=(q25 ◇ (q23 ◇ ((q26 ◇ q25) ◇ q25))):=by
    intro q23 q24 q25 q26
    exact (((rfl).symm).trans ((((cg (fun t => q25 ◇ t) ((h q23 ((q26 ◇ q25) ◇ q25) q24).symm)).symm).trans ((h (((q24 ◇ ((q26 ◇ q25) ◇ q25)) ◇ ((q26 ◇ q25) ◇ q25)) ◇ q23) q25 q26).symm)).trans (rfl))).symm
  have apc8 : forall (q27 q28 q29 : G), (q29 ◇ ((q29 ◇ (q29 ◇ ((q27 ◇ q29) ◇ q29))) ◇ q28))=(q28 ◇ q29):=by
    intro q27 q28 q29
    exact ((rfl).symm).trans ((((cg (fun t => q29 ◇ t) (cg (fun t => t ◇ q28) (apc7 q29 q27 q29 q27))).symm).trans ((h q28 q29 ((q27 ◇ ((q27 ◇ q29) ◇ q29)) ◇ ((q27 ◇ q29) ◇ q29))).symm)).trans (rfl))
  have apc9 : forall (q30 q31 : G), (q31 ◇ ((q31 ◇ (q31 ◇ q31)) ◇ q30))=(q30 ◇ q31):=by
    intro q30 q31
    exact ((rfl).symm).trans ((((cg (fun t => q31 ◇ t) (cg (fun t => t ◇ q30) (cg (fun t => q31 ◇ t) ((h q31 q31 q30).symm)))).symm).trans (apc8 (q30 ◇ q31) q30 q31)).trans (rfl))
  have apc10 : forall (q23 q24 q32 q26 : G), ((((q24 ◇ q26) ◇ q26) ◇ q23) ◇ (((q23 ◇ q26) ◇ (((q24 ◇ q26) ◇ q26) ◇ q23)) ◇ q32))=(q32 ◇ (((q24 ◇ q26) ◇ q26) ◇ q23)):=by
    intro q23 q24 q32 q26
    exact ((rfl).symm).trans ((((cg (fun t => (((q24 ◇ q26) ◇ q26) ◇ q23) ◇ t) (cg (fun t => t ◇ q32) (cg (fun t => t ◇ (((q24 ◇ q26) ◇ q26) ◇ q23)) ((h q23 q26 q24).symm)))).symm).trans ((h q32 (((q24 ◇ q26) ◇ q26) ◇ q23) q26).symm)).trans (rfl))
  have apc15 : forall (q27 q28 : G), (((q27 ◇ q28) ◇ q28) ◇ (((q27 ◇ q28) ◇ q28) ◇ q28))=(q28 ◇ ((q27 ◇ q28) ◇ q28)):=by
    intro q27 q28
    exact ((cg (fun t => ((q27 ◇ q28) ◇ q28) ◇ t) (apc3 (q27 ◇ q28) q28 q28 q27)).symm).trans ((((cg (fun t => ((q27 ◇ q28) ◇ q28) ◇ t) (apc7 ((q27 ◇ q28) ◇ q28) q27 q28 q27)).symm).trans ((h q28 ((q27 ◇ q28) ◇ q28) (q27 ◇ ((q27 ◇ q28) ◇ q28))).symm)).trans (rfl))
  have apc16 : forall (q33 q34 : G), (q33 ◇ (q33 ◇ ((q34 ◇ q33) ◇ q33)))=((((q34 ◇ q33) ◇ q33) ◇ q33) ◇ q33):=by
    intro q33 q34
    exact ((rfl).symm).trans ((((cg (fun t => q33 ◇ t) (apc15 q34 q33)).symm).trans ((h (((q34 ◇ q33) ◇ q33) ◇ q33) q33 q34).symm)).trans (rfl))
  have apc17 : forall (q35 q36 : G), (((((q35 ◇ q36) ◇ q36) ◇ q36) ◇ q36) ◇ q36)=(q36 ◇ (q36 ◇ q36)):=by
    intro q35 q36
    exact (((rfl).symm).trans ((((cg (fun t => q36 ◇ t) ((h q36 q36 q35).symm)).symm).trans (apc16 q36 (q35 ◇ q36))).trans (rfl))).symm
  have apc18 : forall (q37 : G), (q37 ◇ (q37 ◇ (q37 ◇ q37)))=(q37 ◇ q37):=by
    intro q37
    exact ((rfl).symm).trans ((((cg (fun t => q37 ◇ t) (apc17 q37 q37)).symm).trans ((h q37 q37 ((q37 ◇ q37) ◇ q37)).symm)).trans (rfl))
  have apc19 : forall (q38 : G), ((q38 ◇ (q38 ◇ q38)) ◇ q38)=(q38 ◇ (q38 ◇ q38)):=by
    intro q38
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q38) (apc17 q38 q38)).symm).trans (apc17 (q38 ◇ q38) q38)).trans (rfl))
  have apc22 : forall (q39 q40 : G), (((((q39 ◇ q40) ◇ q40) ◇ q40) ◇ q40) ◇ (q40 ◇ (q40 ◇ q40)))=(q40 ◇ q40):=by
    intro q39 q40
    exact ((rfl).symm).trans ((((cg (fun t => ((((q39 ◇ q40) ◇ q40) ◇ q40) ◇ q40) ◇ t) (apc17 q39 q40)).symm).trans (apc15 ((q39 ◇ q40) ◇ q40) q40)).trans (apc5 q39 q40 q40 q40))
  have apc23 : forall (q41 : G), ((q41 ◇ (q41 ◇ q41)) ◇ (q41 ◇ (q41 ◇ q41)))=(q41 ◇ q41):=by
    intro q41
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q41 ◇ (q41 ◇ q41))) (apc17 q41 q41)).symm).trans (apc22 (q41 ◇ q41) q41)).trans (rfl))
  have apc24 : forall (q0 q1 q2 q42 q4 : G), ((q0 ◇ q1) ◇ (((q4 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)) ◇ q42))=(q42 ◇ (q1 ◇ (((q2 ◇ q1) ◇ q1) ◇ q0))):=by
    intro q0 q1 q2 q42 q4
    exact (((cg (fun t => (q1 ◇ (((q2 ◇ q1) ◇ q1) ◇ q0)) ◇ t) (cg (fun t => t ◇ q42) (apc6 q0 q1 q2 q4 (q0 ◇ q1) ((q4 ◇ (q0 ◇ q1)) ◇ (q1 ◇ (((q2 ◇ q1) ◇ q1) ◇ q0)))))).trans (apc4 q0 q1 q2 (((q4 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)) ◇ q42))).symm).trans ((((cg (fun t => (q1 ◇ (((q2 ◇ q1) ◇ q1) ◇ q0)) ◇ t) (cg (fun t => t ◇ q42) (cg (fun t => t ◇ (q1 ◇ (((q2 ◇ q1) ◇ q1) ◇ q0))) (cg (fun t => q4 ◇ t) ((h q0 q1 q2).symm))))).symm).trans ((h q42 (q1 ◇ (((q2 ◇ q1) ◇ q1) ◇ q0)) q4).symm)).trans (rfl))
  have apc25 : forall (q43 q44 q45 q46 : G), (q46 ◇ (q44 ◇ (((q45 ◇ q44) ◇ q44) ◇ q43)))=(q46 ◇ (q43 ◇ q44)):=by
    intro q43 q44 q45 q46
    exact ((rfl).symm).trans ((((apc24 q43 q44 q45 q46 q43).symm).trans ((h q46 (q43 ◇ q44) q43).symm)).trans (rfl))
  have apc29 : forall (q47 : G), ((q47 ◇ (q47 ◇ q47)) ◇ ((q47 ◇ (q47 ◇ q47)) ◇ (q47 ◇ q47)))=(q47 ◇ q47):=by
    intro q47
    exact ((rfl).symm).trans ((((cg (fun t => (q47 ◇ (q47 ◇ q47)) ◇ t) (cg (fun t => (q47 ◇ (q47 ◇ q47)) ◇ t) (apc23 q47))).symm).trans (apc18 (q47 ◇ (q47 ◇ q47)))).trans (apc23 q47))
  have apc30 : forall (q48 : G), (((q48 ◇ (q48 ◇ q48)) ◇ (q48 ◇ q48)) ◇ q48)=(q48 ◇ (q48 ◇ q48)):=by
    intro q48
    exact (((rfl).symm).trans ((((cg (fun t => q48 ◇ t) (apc29 q48)).symm).trans (apc9 ((q48 ◇ (q48 ◇ q48)) ◇ (q48 ◇ q48)) q48)).trans (rfl))).symm
  have apc31 : forall (q49 : G), ((q49 ◇ q49) ◇ (q49 ◇ (q49 ◇ q49)))=(q49 ◇ (q49 ◇ q49)):=by
    intro q49
    exact ((rfl).symm).trans ((((cg (fun t => (q49 ◇ q49) ◇ t) (apc30 q49)).symm).trans ((h q49 (q49 ◇ q49) q49).symm)).trans (rfl))
  have apc34 : forall (q50 q51 q52 : G), ((q52 ◇ (q52 ◇ q52)) ◇ ((q52 ◇ (q52 ◇ q52)) ◇ (q50 ◇ q51)))=((q50 ◇ q51) ◇ (q52 ◇ (q52 ◇ q52))):=by
    intro q50 q51 q52
    exact ((cg (fun t => (q52 ◇ (q52 ◇ q52)) ◇ t) (cg (fun t => t ◇ (q50 ◇ q51)) (apc31 q52))).symm).trans ((((cg (fun t => (q52 ◇ (q52 ◇ q52)) ◇ t) (cg (fun t => t ◇ (q50 ◇ q51)) (cg (fun t => t ◇ (q52 ◇ (q52 ◇ q52))) (apc18 q52)))).symm).trans (apc3 q50 q51 (q52 ◇ (q52 ◇ q52)) q52)).trans (rfl))
  have apc35 : forall (q50 q51 q52 q47 : G), (q47 ◇ (q47 ◇ q47))=(q47 ◇ q47):=by
    intro q50 q51 q52 q47
    exact ((apc31 q47).symm).trans ((((apc34 q47 q47 q47).symm).trans ((apc29 q47).trans (rfl))).trans (rfl))
  have apc36 : forall (q41 q50 q51 q52 q47 : G), ((q41 ◇ q41) ◇ (q41 ◇ q41))=(q41 ◇ q41):=by
    intro q41 q50 q51 q52 q47
    exact ((rfl).symm).trans (((((cg (fun t => t ◇ (q41 ◇ (q41 ◇ q41))) (apc35 (q41 ◇ (q41 ◇ q41)) (q41 ◇ (q41 ◇ q41)) (q41 ◇ (q41 ◇ q41)) q41)).trans (cg (fun t => (q41 ◇ q41) ◇ t) (apc35 (q41 ◇ (q41 ◇ q41)) (q41 ◇ (q41 ◇ q41)) (q41 ◇ (q41 ◇ q41)) q41))).symm).trans ((apc23 q41).trans (rfl))).trans (rfl))
  have apc37 : forall (q38 q50 q51 q52 q47 : G), ((q38 ◇ q38) ◇ q38)=(q38 ◇ q38):=by
    intro q38 q50 q51 q52 q47
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q38) (apc35 (q38 ◇ (q38 ◇ q38)) (q38 ◇ (q38 ◇ q38)) (q38 ◇ (q38 ◇ q38)) q38)).symm).trans ((apc19 q38).trans (apc35 (q38 ◇ (q38 ◇ q38)) (q38 ◇ (q38 ◇ q38)) (q38 ◇ (q38 ◇ q38)) q38))).trans (rfl))
  have apc38 : forall (q30 q31 q50 q51 q52 q47 : G), (q31 ◇ ((q31 ◇ q31) ◇ q30))=(q30 ◇ q31):=by
    intro q30 q31 q50 q51 q52 q47
    exact ((rfl).symm).trans ((((cg (fun t => q31 ◇ t) (cg (fun t => t ◇ q30) (apc35 (q31 ◇ (q31 ◇ q31)) (q31 ◇ (q31 ◇ q31)) (q31 ◇ (q31 ◇ q31)) q31))).symm).trans ((apc9 q30 q31).trans (rfl))).trans (rfl))
  have apc39 : forall (q53 q54 : G), ((q53 ◇ q53) ◇ ((q53 ◇ q53) ◇ q54))=(q54 ◇ (q53 ◇ q53)):=by
    intro q53 q54
    exact ((rfl).symm).trans ((((cg (fun t => (q53 ◇ q53) ◇ t) (cg (fun t => t ◇ q54) (apc36 q53 q53 q53 q53 q53))).symm).trans (apc38 q54 (q53 ◇ q53) q53 q53 q53 q53)).trans (rfl))
  have apc40 : forall (q55 q56 : G), (q56 ◇ (q55 ◇ (q56 ◇ q56)))=(((q56 ◇ q56) ◇ q55) ◇ q56):=by
    intro q55 q56
    exact ((rfl).symm).trans ((((cg (fun t => q56 ◇ t) (apc39 q56 q55)).symm).trans (apc38 ((q56 ◇ q56) ◇ q55) q56 q55 q55 q55 q55)).trans (rfl))
  have apc41 : forall (q57 q58 : G), ((q58 ◇ q58) ◇ (q57 ◇ (q58 ◇ q58)))=(((q58 ◇ q58) ◇ q57) ◇ (q58 ◇ q58)):=by
    intro q57 q58
    exact ((rfl).symm).trans ((((cg (fun t => (q58 ◇ q58) ◇ t) (apc39 q58 q57)).symm).trans (apc39 q58 ((q58 ◇ q58) ◇ q57))).trans (rfl))
  have apc44 : forall (q59 q60 : G), (((q59 ◇ q59) ◇ ((q60 ◇ q59) ◇ q59)) ◇ q59)=(q59 ◇ q59):=by
    intro q59 q60
    exact ((rfl).symm).trans ((((apc40 ((q60 ◇ q59) ◇ q59) q59).symm).trans ((h (q59 ◇ q59) q59 q60).symm)).trans (apc37 q59 ((q59 ◇ q59) ◇ q59) ((q59 ◇ q59) ◇ q59) ((q59 ◇ q59) ◇ q59) ((q59 ◇ q59) ◇ q59)))
  have apc45 : forall (q61 q62 : G), ((((q61 ◇ q62) ◇ q62) ◇ q62) ◇ (q62 ◇ q62))=(q62 ◇ (((q61 ◇ q62) ◇ q62) ◇ q62)):=by
    intro q61 q62
    exact ((rfl).symm).trans ((((cg (fun t => (((q61 ◇ q62) ◇ q62) ◇ q62) ◇ t) (apc44 q62 (q61 ◇ q62))).symm).trans (apc10 q62 q61 q62 q62)).trans (rfl))
  have apc50 : forall (q63 q64 q65 : G), (((((q65 ◇ q64) ◇ q64) ◇ ((q65 ◇ q64) ◇ q64)) ◇ q63) ◇ q64)=(q64 ◇ (q63 ◇ ((q65 ◇ q64) ◇ q64))):=by
    intro q63 q64 q65
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q64) (cg (fun t => t ◇ q63) (apc37 ((q65 ◇ q64) ◇ q64) q63 q63 q63 q63))).symm).trans (apc7 q63 ((q65 ◇ q64) ◇ q64) q64 q65)).trans (rfl))
  have apc54 : forall (q66 q67 q68 : G), (((q68 ◇ q68) ◇ q66) ◇ (((q66 ◇ q68) ◇ ((q68 ◇ q68) ◇ q66)) ◇ q67))=(q67 ◇ ((q68 ◇ q68) ◇ q66)):=by
    intro q66 q67 q68
    exact ((rfl).symm).trans ((((cg (fun t => ((q68 ◇ q68) ◇ q66) ◇ t) (cg (fun t => t ◇ q67) (cg (fun t => t ◇ ((q68 ◇ q68) ◇ q66)) (apc38 q66 q68 q66 q66 q66 q66)))).symm).trans ((h q67 ((q68 ◇ q68) ◇ q66) q68).symm)).trans (rfl))
  have apc56 : forall (q69 q70 q71 : G), ((((q71 ◇ q71) ◇ (((q69 ◇ q71) ◇ q71) ◇ q71)) ◇ q70) ◇ q71)=(q71 ◇ (q70 ◇ (((q69 ◇ q71) ◇ q71) ◇ q71))):=by
    intro q69 q70 q71
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q71) (cg (fun t => t ◇ q70) (cg (fun t => t ◇ (((q69 ◇ q71) ◇ q71) ◇ q71)) ((h q71 q71 q69).symm)))).symm).trans (apc7 q70 q71 q71 (q69 ◇ q71))).trans (rfl))
  have apc58 : forall (q72 q73 : G), (((q73 ◇ q73) ◇ (((q72 ◇ q73) ◇ q73) ◇ q73)) ◇ (q73 ◇ q73))=(q73 ◇ q73):=by
    intro q72 q73
    exact ((((apc25 q73 q73 q72 (q73 ◇ q73)).trans (apc36 q73 ((q73 ◇ q73) ◇ (q73 ◇ q73)) ((q73 ◇ q73) ◇ (q73 ◇ q73)) ((q73 ◇ q73) ◇ (q73 ◇ q73)) ((q73 ◇ q73) ◇ (q73 ◇ q73)))).symm).trans ((((cg (fun t => (q73 ◇ q73) ◇ t) (apc45 q72 q73)).symm).trans (apc41 (((q72 ◇ q73) ◇ q73) ◇ q73) q73)).trans (rfl))).symm
  have apc59 : forall (q74 q75 : G), ((((q74 ◇ q75) ◇ q75) ◇ q75) ◇ q75)=(q75 ◇ q75):=by
    intro q74 q75
    exact (((apc37 q75 ((q75 ◇ q75) ◇ q75) ((q75 ◇ q75) ◇ q75) ((q75 ◇ q75) ◇ q75) ((q75 ◇ q75) ◇ q75)).symm).trans ((((cg (fun t => t ◇ q75) (apc58 q74 q75)).symm).trans (apc56 q74 (q75 ◇ q75) q75)).trans (apc38 (((q74 ◇ q75) ◇ q75) ◇ q75) q75 (q75 ◇ ((q75 ◇ q75) ◇ (((q74 ◇ q75) ◇ q75) ◇ q75))) (q75 ◇ ((q75 ◇ q75) ◇ (((q74 ◇ q75) ◇ q75) ◇ q75))) (q75 ◇ ((q75 ◇ q75) ◇ (((q74 ◇ q75) ◇ q75) ◇ q75))) (q75 ◇ ((q75 ◇ q75) ◇ (((q74 ◇ q75) ◇ q75) ◇ q75)))))).symm
  have apc60 : forall (q33 q34 q74 q75 : G), (q33 ◇ (q33 ◇ ((q34 ◇ q33) ◇ q33)))=(q33 ◇ q33):=by
    intro q33 q34 q74 q75
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc16 q33 q34).trans (apc59 q34 q33))).trans (rfl))
  have apc63 : forall (q76 q77 : G), (((q76 ◇ (q77 ◇ q77)) ◇ (q77 ◇ q77)) ◇ (q77 ◇ q77))=(q77 ◇ q77):=by
    intro q76 q77
    exact (((apc36 q77 ((q77 ◇ q77) ◇ (q77 ◇ q77)) ((q77 ◇ q77) ◇ (q77 ◇ q77)) ((q77 ◇ q77) ◇ (q77 ◇ q77)) ((q77 ◇ q77) ◇ (q77 ◇ q77))).symm).trans ((((apc60 (q77 ◇ q77) q76 q76 q76).symm).trans (apc39 q77 ((q76 ◇ (q77 ◇ q77)) ◇ (q77 ◇ q77)))).trans (rfl))).symm
  have apc74 : forall (q78 q79 : G), ((((q78 ◇ q78) ◇ q79) ◇ (q78 ◇ q78)) ◇ (q78 ◇ q78))=(q78 ◇ q78):=by
    intro q78 q79
    exact (((apc63 q79 q78).symm).trans ((((cg (fun t => ((q79 ◇ (q78 ◇ q78)) ◇ (q78 ◇ q78)) ◇ t) (apc63 q79 q78)).symm).trans (apc15 q79 (q78 ◇ q78))).trans ((apc41 (q79 ◇ (q78 ◇ q78)) q78).trans (cg (fun t => t ◇ (q78 ◇ q78)) (apc41 q79 q78))))).symm
  have apc79 : forall (q80 q81 : G), ((((q81 ◇ q80) ◇ q80) ◇ ((q81 ◇ q80) ◇ q80)) ◇ q80)=(((q81 ◇ q80) ◇ q80) ◇ q80):=by
    intro q80 q81
    exact (((apc3 (q81 ◇ q80) q80 q80 q81).symm).trans ((((cg (fun t => q80 ◇ t) (apc35 q80 q80 q80 ((q81 ◇ q80) ◇ q80))).symm).trans ((h (((q81 ◇ q80) ◇ q80) ◇ ((q81 ◇ q80) ◇ q80)) q80 q81).symm)).trans (rfl))).symm
  have apc88 : forall (q82 q83 q60 : G), ((q82 ◇ (q60 ◇ q60)) ◇ (((((q60 ◇ q60) ◇ q82) ◇ q60) ◇ (q82 ◇ (q60 ◇ q60))) ◇ q83))=(q83 ◇ (q82 ◇ (q60 ◇ q60))):=by
    intro q82 q83 q60
    exact ((rfl).symm).trans ((((cg (fun t => (q82 ◇ (q60 ◇ q60)) ◇ t) (cg (fun t => t ◇ q83) (cg (fun t => t ◇ (q82 ◇ (q60 ◇ q60))) (apc40 q82 q60)))).symm).trans ((h q83 (q82 ◇ (q60 ◇ q60)) q60).symm)).trans (rfl))
  have apc97 : forall (q84 q85 q86 : G), ((q84 ◇ (q85 ◇ q85)) ◇ (((((q85 ◇ q85) ◇ q84) ◇ (q85 ◇ q85)) ◇ (q84 ◇ (q85 ◇ q85))) ◇ q86))=(q86 ◇ (q84 ◇ (q85 ◇ q85))):=by
    intro q84 q85 q86
    exact ((rfl).symm).trans ((((cg (fun t => (q84 ◇ (q85 ◇ q85)) ◇ t) (cg (fun t => t ◇ q86) (cg (fun t => t ◇ (q84 ◇ (q85 ◇ q85))) (apc41 q84 q85)))).symm).trans ((h q86 (q84 ◇ (q85 ◇ q85)) (q85 ◇ q85)).symm)).trans (rfl))
  have apc119 : forall (q87 q88 : G), ((((q87 ◇ q88) ◇ q88) ◇ ((q87 ◇ q88) ◇ q88)) ◇ (((q87 ◇ q88) ◇ q88) ◇ q88))=(((q87 ◇ q88) ◇ q88) ◇ q88):=by
    intro q87 q88
    exact ((rfl).symm).trans ((((cg (fun t => (((q87 ◇ q88) ◇ q88) ◇ ((q87 ◇ q88) ◇ q88)) ◇ t) (apc79 q88 q87)).symm).trans (apc39 ((q87 ◇ q88) ◇ q88) q88)).trans (apc3 (q87 ◇ q88) q88 q88 q87))
  have apc120 : forall (q89 q90 : G), (((q90 ◇ q89) ◇ q89) ◇ q89)=(q89 ◇ q89):=by
    intro q89 q90
    exact (((apc59 q90 q89).symm).trans ((((cg (fun t => t ◇ q89) (apc119 q90 q89)).symm).trans (apc50 (((q90 ◇ q89) ◇ q89) ◇ q89) q89 q90)).trans (apc3 (q90 ◇ q89) q89 q89 (q90 ◇ q89)))).symm
  have apc121 : forall (q89 q90 q27 q28 : G), (((q27 ◇ q28) ◇ q28) ◇ (q28 ◇ q28))=(q28 ◇ ((q27 ◇ q28) ◇ q28)):=by
    intro q89 q90 q27 q28
    exact ((rfl).symm).trans ((((cg (fun t => ((q27 ◇ q28) ◇ q28) ◇ t) (apc120 q28 q27)).symm).trans ((apc15 q27 q28).trans (rfl))).trans (rfl))
  have apc123 : forall (q89 q90 q87 q88 : G), ((((q87 ◇ q88) ◇ q88) ◇ ((q87 ◇ q88) ◇ q88)) ◇ (q88 ◇ q88))=(q88 ◇ q88):=by
    intro q89 q90 q87 q88
    exact ((rfl).symm).trans ((((cg (fun t => (((q87 ◇ q88) ◇ q88) ◇ ((q87 ◇ q88) ◇ q88)) ◇ t) (apc120 q88 q87)).symm).trans ((apc119 q87 q88).trans (apc120 q88 q87))).trans (rfl))
  have apc124 : forall (q91 q92 : G), ((q92 ◇ q92) ◇ ((q91 ◇ q92) ◇ q92))=(q92 ◇ ((q91 ◇ q92) ◇ q92)):=by
    intro q91 q92
    exact (((apc121 (((q91 ◇ q92) ◇ q92) ◇ (q92 ◇ q92)) (((q91 ◇ q92) ◇ q92) ◇ (q92 ◇ q92)) q91 q92).symm).trans ((((cg (fun t => ((q91 ◇ q92) ◇ q92) ◇ t) (apc123 q91 q91 q91 q92)).symm).trans (apc38 (q92 ◇ q92) ((q91 ◇ q92) ◇ q92) q91 q91 q91 q91)).trans (rfl))).symm
  have apc126 : forall (q93 q94 : G), ((q94 ◇ q94) ◇ (q94 ◇ ((q93 ◇ q94) ◇ q94)))=(q94 ◇ ((q93 ◇ q94) ◇ q94)):=by
    intro q93 q94
    exact ((rfl).symm).trans ((((cg (fun t => (q94 ◇ q94) ◇ t) (apc124 q93 q94)).symm).trans (apc39 q94 ((q93 ◇ q94) ◇ q94))).trans (apc121 (((q93 ◇ q94) ◇ q94) ◇ (q94 ◇ q94)) (((q93 ◇ q94) ◇ q94) ◇ (q94 ◇ q94)) q93 q94))
  have apc127 : forall (q95 q96 : G), (((q96 ◇ ((q95 ◇ q96) ◇ q96)) ◇ (q96 ◇ q96)) ◇ (q96 ◇ q96))=(q96 ◇ q96):=by
    intro q95 q96
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q96 ◇ q96)) (cg (fun t => t ◇ (q96 ◇ q96)) (apc124 q95 q96))).symm).trans (apc74 q96 ((q95 ◇ q96) ◇ q96))).trans (rfl))
  have apc130 : forall (q97 q98 : G), ((q98 ◇ ((q97 ◇ q98) ◇ q98)) ◇ (q98 ◇ q98))=(q98 ◇ ((q97 ◇ q98) ◇ q98)):=by
    intro q97 q98
    exact (((apc126 q97 q98).symm).trans ((((cg (fun t => (q98 ◇ q98) ◇ t) (apc126 q97 q98)).symm).trans (apc39 q98 (q98 ◇ ((q97 ◇ q98) ◇ q98)))).trans (rfl))).symm
  have apc131 : forall (q95 q96 q97 q98 : G), (q96 ◇ ((q95 ◇ q96) ◇ q96))=(q96 ◇ q96):=by
    intro q95 q96 q97 q98
    exact ((rfl).symm).trans (((((cg (fun t => t ◇ (q96 ◇ q96)) (apc130 q95 q96)).trans (apc130 q95 q96)).symm).trans ((apc127 q95 q96).trans (rfl))).trans (rfl))
  have apc132 : forall (q89 q90 q95 q96 q97 q98 q27 q28 : G), (((q27 ◇ q28) ◇ q28) ◇ (q28 ◇ q28))=(q28 ◇ q28):=by
    intro q89 q90 q95 q96 q97 q98 q27 q28
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc121 q27 q27 q27 q28).trans (apc131 q27 q28 (q28 ◇ ((q27 ◇ q28) ◇ q28)) (q28 ◇ ((q27 ◇ q28) ◇ q28))))).trans (rfl))
  have apc133 : forall (q91 q92 q95 q96 q97 q98 : G), ((q92 ◇ q92) ◇ ((q91 ◇ q92) ◇ q92))=(q92 ◇ q92):=by
    intro q91 q92 q95 q96 q97 q98
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc124 q91 q92).trans (apc131 q91 q92 (q92 ◇ ((q91 ◇ q92) ◇ q92)) (q92 ◇ ((q91 ◇ q92) ◇ q92))))).trans (rfl))
  have apc137 : forall (q99 q100 q101 : G), (q100 ◇ (q99 ◇ ((q101 ◇ q100) ◇ q100)))=(((q100 ◇ q100) ◇ q99) ◇ q100):=by
    intro q99 q100 q101
    exact (((cg (fun t => t ◇ q100) (cg (fun t => t ◇ q99) (apc133 q101 q100 ((q100 ◇ q100) ◇ ((q101 ◇ q100) ◇ q100)) ((q100 ◇ q100) ◇ ((q101 ◇ q100) ◇ q100)) ((q100 ◇ q100) ◇ ((q101 ◇ q100) ◇ q100)) ((q100 ◇ q100) ◇ ((q101 ◇ q100) ◇ q100))))).symm).trans ((((cg (fun t => t ◇ q100) (cg (fun t => t ◇ q99) (cg (fun t => t ◇ ((q101 ◇ q100) ◇ q100)) (apc131 q101 q100 q99 q99)))).symm).trans (apc7 q99 q100 q100 q101)).trans (rfl))).symm
  have apc140 : forall (q102 q103 q104 : G), (((q102 ◇ q104) ◇ q104) ◇ ((q104 ◇ q104) ◇ q103))=(q103 ◇ ((q102 ◇ q104) ◇ q104)):=by
    intro q102 q103 q104
    exact ((cg (fun t => ((q102 ◇ q104) ◇ q104) ◇ t) (cg (fun t => t ◇ q103) (apc133 q102 q104 ((q104 ◇ q104) ◇ ((q102 ◇ q104) ◇ q104)) ((q104 ◇ q104) ◇ ((q102 ◇ q104) ◇ q104)) ((q104 ◇ q104) ◇ ((q102 ◇ q104) ◇ q104)) ((q104 ◇ q104) ◇ ((q102 ◇ q104) ◇ q104))))).symm).trans ((((cg (fun t => ((q102 ◇ q104) ◇ q104) ◇ t) (cg (fun t => t ◇ q103) (cg (fun t => t ◇ ((q102 ◇ q104) ◇ q104)) (apc131 q102 q104 q102 q102)))).symm).trans ((h q103 ((q102 ◇ q104) ◇ q104) q104).symm)).trans (rfl))
  have apc141 : forall (q105 q106 q107 : G), (((q107 ◇ q107) ◇ q105) ◇ ((q106 ◇ q107) ◇ q107))=(((q106 ◇ q107) ◇ q107) ◇ (q105 ◇ (q107 ◇ q107))):=by
    intro q105 q106 q107
    exact (((rfl).symm).trans ((((cg (fun t => ((q106 ◇ q107) ◇ q107) ◇ t) (apc39 q107 q105)).symm).trans (apc140 q106 ((q107 ◇ q107) ◇ q105) q107)).trans (rfl))).symm
  have apc142 : forall (q108 q109 q110 : G), (((q108 ◇ q110) ◇ q110) ◇ ((q109 ◇ q110) ◇ q110))=(q110 ◇ q110):=by
    intro q108 q109 q110
    exact (((apc132 (((q109 ◇ q110) ◇ q110) ◇ (q110 ◇ q110)) (((q109 ◇ q110) ◇ q110) ◇ (q110 ◇ q110)) (((q109 ◇ q110) ◇ q110) ◇ (q110 ◇ q110)) (((q109 ◇ q110) ◇ q110) ◇ (q110 ◇ q110)) (((q109 ◇ q110) ◇ q110) ◇ (q110 ◇ q110)) (((q109 ◇ q110) ◇ q110) ◇ (q110 ◇ q110)) q109 q110).symm).trans ((((cg (fun t => ((q109 ◇ q110) ◇ q110) ◇ t) (apc133 q108 q110 q108 q108 q108 q108)).symm).trans (apc140 q109 ((q108 ◇ q110) ◇ q110) q110)).trans (rfl))).symm
  have apc147 : forall (q111 q112 q113 : G), (((q111 ◇ (q113 ◇ q113)) ◇ (q113 ◇ q113)) ◇ ((q112 ◇ q113) ◇ q113))=(q113 ◇ q113):=by
    intro q111 q112 q113
    exact ((((cg (fun t => ((q112 ◇ q113) ◇ q113) ◇ t) (apc36 q113 ((q113 ◇ q113) ◇ (q113 ◇ q113)) ((q113 ◇ q113) ◇ (q113 ◇ q113)) ((q113 ◇ q113) ◇ (q113 ◇ q113)) ((q113 ◇ q113) ◇ (q113 ◇ q113)))).trans (apc132 (((q112 ◇ q113) ◇ q113) ◇ (q113 ◇ q113)) (((q112 ◇ q113) ◇ q113) ◇ (q113 ◇ q113)) (((q112 ◇ q113) ◇ q113) ◇ (q113 ◇ q113)) (((q112 ◇ q113) ◇ q113) ◇ (q113 ◇ q113)) (((q112 ◇ q113) ◇ q113) ◇ (q113 ◇ q113)) (((q112 ◇ q113) ◇ q113) ◇ (q113 ◇ q113)) q112 q113)).symm).trans ((((cg (fun t => ((q112 ◇ q113) ◇ q113) ◇ t) (apc131 q111 (q113 ◇ q113) q111 q111)).symm).trans (apc140 q112 ((q111 ◇ (q113 ◇ q113)) ◇ (q113 ◇ q113)) q113)).trans (rfl))).symm
  have apc155 : forall (q23 q24 q25 q26 q99 q100 q101 : G), ((((q24 ◇ ((q26 ◇ q25) ◇ q25)) ◇ ((q26 ◇ q25) ◇ q25)) ◇ q23) ◇ q25)=(((q25 ◇ q25) ◇ q23) ◇ q25):=by
    intro q23 q24 q25 q26 q99 q100 q101
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc7 q23 q24 q25 q26).trans (apc137 q23 q25 q26))).trans (rfl))
  have apc159 : forall (q114 q115 q116 : G), (((q115 ◇ (q114 ◇ q114)) ◇ (q114 ◇ q114)) ◇ ((q114 ◇ q114) ◇ q116))=(q116 ◇ ((q115 ◇ (q114 ◇ q114)) ◇ (q114 ◇ q114))):=by
    intro q114 q115 q116
    exact ((rfl).symm).trans ((((cg (fun t => ((q115 ◇ (q114 ◇ q114)) ◇ (q114 ◇ q114)) ◇ t) (cg (fun t => t ◇ q116) (apc36 q114 q114 q114 q114 q114))).symm).trans (apc140 q115 q116 (q114 ◇ q114))).trans (rfl))
  have apc160 : forall (q117 q118 : G), ((((q118 ◇ q118) ◇ q117) ◇ (q118 ◇ q118)) ◇ q118)=(q118 ◇ q118):=by
    intro q117 q118
    exact (((apc40 (q117 ◇ (q118 ◇ q118)) q118).trans (cg (fun t => t ◇ q118) (apc41 q117 q118))).symm).trans ((((apc159 q118 q117 q118).symm).trans (apc147 q117 q118 q118)).trans (rfl))
  have apc172 : forall (q119 q120 q121 : G), (((q121 ◇ q121) ◇ (q119 ◇ q121)) ◇ (((q119 ◇ q121) ◇ ((q119 ◇ q121) ◇ q121)) ◇ q120))=(q120 ◇ ((q121 ◇ q121) ◇ (q119 ◇ q121))):=by
    intro q119 q120 q121
    exact ((rfl).symm).trans ((((cg (fun t => ((q121 ◇ q121) ◇ (q119 ◇ q121)) ◇ t) (cg (fun t => t ◇ q120) (apc140 q119 (q119 ◇ q121) q121))).symm).trans (apc54 (q119 ◇ q121) q120 q121)).trans (rfl))
  have apc189 : forall (q122 q69 q123 q71 q124 : G), ((q122 ◇ ((q123 ◇ ((q124 ◇ q71) ◇ q71)) ◇ ((q124 ◇ q71) ◇ q71))) ◇ q71)=((q122 ◇ (q71 ◇ q71)) ◇ q71):=by
    intro q122 q69 q123 q71 q124
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q71) ((h q122 ((q123 ◇ ((q124 ◇ q71) ◇ q71)) ◇ ((q124 ◇ q71) ◇ q71)) q69).symm)).symm).trans (apc7 (((q69 ◇ ((q123 ◇ ((q124 ◇ q71) ◇ q71)) ◇ ((q124 ◇ q71) ◇ q71))) ◇ ((q123 ◇ ((q124 ◇ q71) ◇ q71)) ◇ ((q124 ◇ q71) ◇ q71))) ◇ q122) q123 q71 q124)).trans ((((cg (fun t => q71 ◇ t) (apc155 q122 q69 ((q124 ◇ q71) ◇ q71) q123 ((((q69 ◇ ((q123 ◇ ((q124 ◇ q71) ◇ q71)) ◇ ((q124 ◇ q71) ◇ q71))) ◇ ((q123 ◇ ((q124 ◇ q71) ◇ q71)) ◇ ((q124 ◇ q71) ◇ q71))) ◇ q122) ◇ ((q124 ◇ q71) ◇ q71)) ((((q69 ◇ ((q123 ◇ ((q124 ◇ q71) ◇ q71)) ◇ ((q124 ◇ q71) ◇ q71))) ◇ ((q123 ◇ ((q124 ◇ q71) ◇ q71)) ◇ ((q124 ◇ q71) ◇ q71))) ◇ q122) ◇ ((q124 ◇ q71) ◇ q71)) ((((q69 ◇ ((q123 ◇ ((q124 ◇ q71) ◇ q71)) ◇ ((q124 ◇ q71) ◇ q71))) ◇ ((q123 ◇ ((q124 ◇ q71) ◇ q71)) ◇ ((q124 ◇ q71) ◇ q71))) ◇ q122) ◇ ((q124 ◇ q71) ◇ q71)))).trans (cg (fun t => q71 ◇ t) (cg (fun t => t ◇ ((q124 ◇ q71) ◇ q71)) (cg (fun t => t ◇ q122) (apc142 q124 q124 q71))))).trans (apc137 ((q71 ◇ q71) ◇ q122) q71 q124)).trans (cg (fun t => t ◇ q71) (apc39 q71 q122))))
  have apc193 : forall (q125 q126 q127 q128 : G), ((q126 ◇ ((((q128 ◇ q127) ◇ q127) ◇ (q125 ◇ (q127 ◇ q127))) ◇ ((q128 ◇ q127) ◇ q127))) ◇ q127)=((q126 ◇ (q127 ◇ q127)) ◇ q127):=by
    intro q125 q126 q127 q128
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q127) (cg (fun t => q126 ◇ t) (cg (fun t => t ◇ ((q128 ◇ q127) ◇ q127)) (apc141 q125 q128 q127)))).symm).trans (apc189 q126 q125 ((q127 ◇ q127) ◇ q125) q127 q128)).trans (rfl))
  have apc194 : forall (q129 q130 : G), (((q130 ◇ q129) ◇ ((q130 ◇ q129) ◇ q129)) ◇ q129)=(q129 ◇ q129):=by
    intro q129 q130
    exact ((cg (fun t => t ◇ q129) (apc140 q130 (q130 ◇ q129) q129)).symm).trans ((((cg (fun t => t ◇ q129) (apc172 q130 ((q130 ◇ q129) ◇ q129) q129)).symm).trans (apc189 ((q129 ◇ q129) ◇ (q130 ◇ q129)) q129 (q130 ◇ q129) q129 q130)).trans (apc160 (q130 ◇ q129) q129))
  have apc195 : forall (q131 q132 : G), (((q132 ◇ q132) ◇ (q131 ◇ q132)) ◇ (q132 ◇ q132))=((q131 ◇ q132) ◇ q132):=by
    intro q131 q132
    exact ((rfl).symm).trans ((((cg (fun t => ((q132 ◇ q132) ◇ (q131 ◇ q132)) ◇ t) (apc194 q132 q131)).symm).trans (apc172 q131 q132 q132)).trans (apc38 (q131 ◇ q132) q132 (q132 ◇ ((q132 ◇ q132) ◇ (q131 ◇ q132))) (q132 ◇ ((q132 ◇ q132) ◇ (q131 ◇ q132))) (q132 ◇ ((q132 ◇ q132) ◇ (q131 ◇ q132))) (q132 ◇ ((q132 ◇ q132) ◇ (q131 ◇ q132)))))
  have apc198 : forall (q133 q134 : G), ((q134 ◇ (q133 ◇ q133)) ◇ (q133 ◇ q133))=(q133 ◇ q133):=by
    intro q133 q134
    exact (((((cg (fun t => ((q133 ◇ q133) ◇ (q134 ◇ (q133 ◇ q133))) ◇ t) (apc36 q133 ((q133 ◇ q133) ◇ (q133 ◇ q133)) ((q133 ◇ q133) ◇ (q133 ◇ q133)) ((q133 ◇ q133) ◇ (q133 ◇ q133)) ((q133 ◇ q133) ◇ (q133 ◇ q133)))).trans (cg (fun t => t ◇ (q133 ◇ q133)) (apc41 q134 q133))).trans (apc74 q133 q134)).symm).trans ((((cg (fun t => t ◇ ((q133 ◇ q133) ◇ (q133 ◇ q133))) (cg (fun t => t ◇ (q134 ◇ (q133 ◇ q133))) (apc36 q133 q133 q133 q133 q133))).symm).trans (apc195 q134 (q133 ◇ q133))).trans (rfl))).symm
  have apc202 : forall (q135 q136 q137 : G), (((q135 ◇ q136) ◇ (q136 ◇ q136)) ◇ ((((q135 ◇ q136) ◇ q136) ◇ ((q135 ◇ q136) ◇ (q136 ◇ q136))) ◇ q137))=(q137 ◇ ((q135 ◇ q136) ◇ (q136 ◇ q136))):=by
    intro q135 q136 q137
    exact ((rfl).symm).trans ((((cg (fun t => ((q135 ◇ q136) ◇ (q136 ◇ q136)) ◇ t) (cg (fun t => t ◇ q137) (cg (fun t => t ◇ ((q135 ◇ q136) ◇ (q136 ◇ q136))) (apc195 q135 q136)))).symm).trans (apc97 (q135 ◇ q136) q136 q137)).trans (rfl))
  have apc203 : forall (q138 q139 : G), ((((q139 ◇ q138) ◇ q138) ◇ ((q139 ◇ q138) ◇ (q138 ◇ q138))) ◇ q138)=(q138 ◇ q138):=by
    intro q138 q139
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q138) (apc202 q139 q138 ((q139 ◇ q138) ◇ q138))).symm).trans (apc193 (q139 ◇ q138) ((q139 ◇ q138) ◇ (q138 ◇ q138)) q138 q139)).trans ((cg (fun t => t ◇ q138) (apc198 q138 (q139 ◇ q138))).trans (apc37 q138 ((q138 ◇ q138) ◇ q138) ((q138 ◇ q138) ◇ q138) ((q138 ◇ q138) ◇ q138) ((q138 ◇ q138) ◇ q138))))
  have apc204 : forall (q140 q141 : G), (((q141 ◇ q141) ◇ (q140 ◇ q141)) ◇ q141)=(q141 ◇ q141):=by
    intro q140 q141
    exact (((apc198 q141 (q140 ◇ q141)).symm).trans ((((cg (fun t => ((q140 ◇ q141) ◇ (q141 ◇ q141)) ◇ t) (apc203 q141 q140)).symm).trans (apc202 q140 q141 q141)).trans (apc40 (q140 ◇ q141) q141))).symm
  have apc209 : forall (q142 q143 q144 : G), (((q142 ◇ q144) ◇ (q144 ◇ q144)) ◇ (((q142 ◇ q144) ◇ q144) ◇ q143))=(q143 ◇ ((q142 ◇ q144) ◇ (q144 ◇ q144))):=by
    intro q142 q143 q144
    exact (((cg (fun t => ((q142 ◇ q144) ◇ (q144 ◇ q144)) ◇ t) (cg (fun t => t ◇ q143) (apc41 (q142 ◇ q144) q144))).trans (cg (fun t => ((q142 ◇ q144) ◇ (q144 ◇ q144)) ◇ t) (cg (fun t => t ◇ q143) (apc195 q142 q144)))).symm).trans ((((cg (fun t => ((q142 ◇ q144) ◇ (q144 ◇ q144)) ◇ t) (cg (fun t => t ◇ q143) (cg (fun t => t ◇ ((q142 ◇ q144) ◇ (q144 ◇ q144))) (apc204 q142 q144)))).symm).trans (apc88 (q142 ◇ q144) q143 q144)).trans (rfl))
  have apc210 : forall (q145 q146 : G), ((q145 ◇ q146) ◇ q146)=(q146 ◇ q146):=by
    intro q145 q146
    exact (((apc198 q146 (q145 ◇ q146)).symm).trans ((((cg (fun t => ((q145 ◇ q146) ◇ (q146 ◇ q146)) ◇ t) (apc132 q145 q145 q145 q145 q145 q145 q145 q146)).symm).trans (apc209 q145 (q146 ◇ q146) q146)).trans ((apc41 (q145 ◇ q146) q146).trans (apc195 q145 q146)))).symm
  have apc212 : forall (q147 q148 : G), (((q148 ◇ q148) ◇ q147) ◇ ((q148 ◇ q148) ◇ q147))=((q147 ◇ q148) ◇ ((q148 ◇ q148) ◇ q147)):=by
    intro q147 q148
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ ((q148 ◇ q148) ◇ q147)) (apc38 q147 q148 q147 q147 q147 q147)).symm).trans (apc210 q148 ((q148 ◇ q148) ◇ q147))).trans (rfl))).symm
  have apc214 : forall (q149 q150 : G), ((((q150 ◇ q150) ◇ q149) ◇ (q150 ◇ q150)) ◇ (q149 ◇ (q150 ◇ q150)))=((q149 ◇ (q150 ◇ q150)) ◇ (q149 ◇ (q150 ◇ q150))):=by
    intro q149 q150
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q149 ◇ (q150 ◇ q150))) (apc41 q149 q150)).symm).trans (apc210 (q150 ◇ q150) (q149 ◇ (q150 ◇ q150)))).trans (rfl))
  have apc218 : forall (q151 q152 : G), ((q152 ◇ (q151 ◇ q151)) ◇ ((q151 ◇ q151) ◇ q152))=((q152 ◇ q151) ◇ ((q151 ◇ q151) ◇ q152)):=by
    intro q151 q152
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q151 ◇ q151) ◇ q152)) (apc39 q151 q152)).symm).trans (apc210 (q151 ◇ q151) ((q151 ◇ q151) ◇ q152))).trans (apc212 q152 q151))
  have apc221 : forall (q153 q154 q155 : G), (((q155 ◇ q155) ◇ (q153 ◇ q155)) ◇ (((q153 ◇ q155) ◇ (q155 ◇ q155)) ◇ q154))=(q154 ◇ ((q155 ◇ q155) ◇ (q153 ◇ q155))):=by
    intro q153 q154 q155
    exact ((rfl).symm).trans ((((cg (fun t => ((q155 ◇ q155) ◇ (q153 ◇ q155)) ◇ t) (cg (fun t => t ◇ q154) (cg (fun t => (q153 ◇ q155) ◇ t) (apc210 q153 q155)))).symm).trans (apc172 q153 q154 q155)).trans (rfl))
  have apc222 : forall (q156 q157 : G), ((q156 ◇ q157) ◇ (q157 ◇ q157))=(q157 ◇ q157):=by
    intro q156 q157
    exact (((((cg (fun t => ((q157 ◇ q157) ◇ (q156 ◇ q157)) ◇ t) (apc36 q157 ((q157 ◇ q157) ◇ (q157 ◇ q157)) ((q157 ◇ q157) ◇ (q157 ◇ q157)) ((q157 ◇ q157) ◇ (q157 ◇ q157)) ((q157 ◇ q157) ◇ (q157 ◇ q157)))).trans (apc195 q156 q157)).trans (apc210 q156 q157)).symm).trans ((((cg (fun t => ((q157 ◇ q157) ◇ (q156 ◇ q157)) ◇ t) (apc210 (q156 ◇ q157) (q157 ◇ q157))).symm).trans (apc221 q156 (q157 ◇ q157) q157)).trans (apc39 q157 (q156 ◇ q157)))).symm
  have apc223 : forall (q153 q154 q155 q156 q157 : G), (((q155 ◇ q155) ◇ (q153 ◇ q155)) ◇ ((q155 ◇ q155) ◇ q154))=(q154 ◇ ((q155 ◇ q155) ◇ (q153 ◇ q155))):=by
    intro q153 q154 q155 q156 q157
    exact ((rfl).symm).trans ((((cg (fun t => ((q155 ◇ q155) ◇ (q153 ◇ q155)) ◇ t) (cg (fun t => t ◇ q154) (apc222 q153 q155))).symm).trans ((apc221 q153 q154 q155).trans (rfl))).trans (rfl))
  have apc227 : forall (q158 q159 q160 : G), (((q160 ◇ q160) ◇ q158) ◇ ((q160 ◇ q160) ◇ (q159 ◇ q160)))=(((q160 ◇ q160) ◇ (q159 ◇ q160)) ◇ (q158 ◇ (q160 ◇ q160))):=by
    intro q158 q159 q160
    exact (((rfl).symm).trans ((((cg (fun t => ((q160 ◇ q160) ◇ (q159 ◇ q160)) ◇ t) (apc39 q160 q158)).symm).trans (apc223 q159 ((q160 ◇ q160) ◇ q158) q160 q158 q158)).trans (rfl))).symm
  have apc229 : forall (q161 q162 q163 : G), ((q161 ◇ q163) ◇ ((q163 ◇ q163) ◇ (q162 ◇ q163)))=(q163 ◇ q163):=by
    intro q161 q162 q163
    exact (((((cg (fun t => ((q163 ◇ q163) ◇ (q161 ◇ q163)) ◇ t) (apc222 q162 q163)).trans (apc195 q161 q163)).trans (apc210 q161 q163)).symm).trans ((((apc227 (q162 ◇ q163) q161 q163).symm).trans (apc223 q162 (q161 ◇ q163) q163 q161 q161)).trans (rfl))).symm
  have apc230 : forall (q164 q165 q166 : G), ((q165 ◇ (q164 ◇ q164)) ◇ (((q164 ◇ q164) ◇ q166) ◇ (q164 ◇ q164)))=(q164 ◇ q164):=by
    intro q164 q165 q166
    exact ((cg (fun t => (q165 ◇ (q164 ◇ q164)) ◇ t) (apc41 q166 q164)).symm).trans ((((cg (fun t => (q165 ◇ (q164 ◇ q164)) ◇ t) (cg (fun t => t ◇ (q166 ◇ (q164 ◇ q164))) (apc222 q164 q164))).symm).trans (apc229 q165 q166 (q164 ◇ q164))).trans (apc222 q164 q164))
  have apc232 : forall (q167 q168 q169 : G), ((q169 ◇ ((q168 ◇ q168) ◇ q167)) ◇ ((q167 ◇ q168) ◇ ((q168 ◇ q168) ◇ q167)))=((q167 ◇ q168) ◇ ((q168 ◇ q168) ◇ q167)):=by
    intro q167 q168 q169
    exact ((rfl).symm).trans ((((cg (fun t => (q169 ◇ ((q168 ◇ q168) ◇ q167)) ◇ t) (apc212 q167 q168)).symm).trans (apc222 q169 ((q168 ◇ q168) ◇ q167))).trans (apc212 q167 q168))
  have apc233 : forall (q170 q171 q172 : G), ((q172 ◇ ((q171 ◇ q171) ◇ (q170 ◇ q171))) ◇ (q171 ◇ q171))=(q171 ◇ q171):=by
    intro q170 q171 q172
    exact ((rfl).symm).trans ((((cg (fun t => (q172 ◇ ((q171 ◇ q171) ◇ (q170 ◇ q171))) ◇ t) (apc229 (q170 ◇ q171) q170 q171)).symm).trans (apc232 (q170 ◇ q171) q171 q172)).trans (((cg (fun t => t ◇ ((q171 ◇ q171) ◇ (q170 ◇ q171))) (apc210 q170 q171)).trans (apc39 q171 (q170 ◇ q171))).trans (apc222 q170 q171)))
  have apc237 : forall (q173 q174 q175 : G), ((q175 ◇ (((q173 ◇ q173) ◇ q174) ◇ (q173 ◇ q173))) ◇ (q173 ◇ q173))=(q173 ◇ q173):=by
    intro q173 q174 q175
    exact (((cg (fun t => t ◇ ((q173 ◇ q173) ◇ (q173 ◇ q173))) (cg (fun t => q175 ◇ t) (apc41 q174 q173))).trans (cg (fun t => (q175 ◇ (((q173 ◇ q173) ◇ q174) ◇ (q173 ◇ q173))) ◇ t) (apc222 q173 q173))).symm).trans ((((cg (fun t => t ◇ ((q173 ◇ q173) ◇ (q173 ◇ q173))) (cg (fun t => q175 ◇ t) (cg (fun t => t ◇ (q174 ◇ (q173 ◇ q173))) (apc222 q173 q173)))).symm).trans (apc233 q174 (q173 ◇ q173) q175)).trans (apc222 q173 q173))
  have apc244 : forall (q176 q177 q178 : G), ((((q176 ◇ q176) ◇ q177) ◇ (q176 ◇ q176)) ◇ ((q176 ◇ q176) ◇ q178))=(q178 ◇ (((q176 ◇ q176) ◇ q177) ◇ (q176 ◇ q176))):=by
    intro q176 q177 q178
    exact ((rfl).symm).trans ((((cg (fun t => (((q176 ◇ q176) ◇ q177) ◇ (q176 ◇ q176)) ◇ t) (cg (fun t => t ◇ q178) (apc230 q176 ((q176 ◇ q176) ◇ q177) q177))).symm).trans (apc38 q178 (((q176 ◇ q176) ◇ q177) ◇ (q176 ◇ q176)) q176 q176 q176 q176)).trans (rfl))
  have apc251 : forall (q179 q180 q181 : G), (((q180 ◇ q180) ◇ q179) ◇ (((q180 ◇ q180) ◇ q181) ◇ (q180 ◇ q180)))=((((q180 ◇ q180) ◇ q181) ◇ (q180 ◇ q180)) ◇ (q179 ◇ (q180 ◇ q180))):=by
    intro q179 q180 q181
    exact (((rfl).symm).trans ((((cg (fun t => (((q180 ◇ q180) ◇ q181) ◇ (q180 ◇ q180)) ◇ t) (apc39 q180 q179)).symm).trans (apc244 q180 q181 ((q180 ◇ q180) ◇ q179))).trans (rfl))).symm
  have apc252 : forall (q182 q183 q184 : G), (((((q183 ◇ q183) ◇ q184) ◇ (q183 ◇ q183)) ◇ (q182 ◇ (q183 ◇ q183))) ◇ (q183 ◇ q183))=(q183 ◇ q183):=by
    intro q182 q183 q184
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q183 ◇ q183)) (apc251 q182 q183 q184)).symm).trans (apc237 q183 q184 ((q183 ◇ q183) ◇ q182))).trans (rfl))
  have apc253 : forall (q185 q186 : G), (((q185 ◇ (q186 ◇ q186)) ◇ (q185 ◇ (q186 ◇ q186))) ◇ (q186 ◇ q186))=(q186 ◇ q186):=by
    intro q185 q186
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q186 ◇ q186)) (apc214 q185 q186)).symm).trans (apc252 q185 q186 q185)).trans (rfl))
  have apc254 : forall (q187 q188 : G), (((q188 ◇ q188) ◇ q187) ◇ (q188 ◇ q188))=(q188 ◇ q188):=by
    intro q187 q188
    exact ((((apc210 q187 (q188 ◇ q188)).trans (apc222 q188 q188)).symm).trans ((((cg (fun t => (q187 ◇ (q188 ◇ q188)) ◇ t) (apc253 q187 q188)).symm).trans (apc38 (q188 ◇ q188) (q187 ◇ (q188 ◇ q188)) q187 q187 q187 q187)).trans (apc41 q187 q188))).symm
  have apc255 : forall (q187 q188 q57 q58 : G), ((q58 ◇ q58) ◇ (q57 ◇ (q58 ◇ q58)))=(q58 ◇ q58):=by
    intro q187 q188 q57 q58
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc41 q57 q58).trans (apc254 q57 q58))).trans (rfl))
  have apc256 : forall (q187 q188 q149 q150 : G), ((q149 ◇ (q150 ◇ q150)) ◇ (q149 ◇ (q150 ◇ q150)))=(q150 ◇ q150):=by
    intro q187 q188 q149 q150
    exact (((apc255 ((q150 ◇ q150) ◇ (q149 ◇ (q150 ◇ q150))) ((q150 ◇ q150) ◇ (q149 ◇ (q150 ◇ q150))) q149 q150).symm).trans ((((cg (fun t => t ◇ (q149 ◇ (q150 ◇ q150))) (apc254 q149 q150)).symm).trans ((apc214 q149 q150).trans (rfl))).trans (rfl))).symm
  have apc258 : forall (q189 q190 : G), (((q189 ◇ q189) ◇ q190) ◇ ((q190 ◇ q190) ◇ (q189 ◇ q189)))=(q189 ◇ q189):=by
    intro q189 q190
    exact (((rfl).symm).trans ((((apc256 q189 q189 (q190 ◇ q190) q189).symm).trans (apc212 (q189 ◇ q189) q190)).trans (rfl))).symm
  have apc260 : forall (q191 q192 q193 : G), ((q191 ◇ (q192 ◇ q192)) ◇ ((q192 ◇ q192) ◇ q193))=(q193 ◇ (q191 ◇ (q192 ◇ q192))):=by
    intro q191 q192 q193
    exact ((rfl).symm).trans ((((cg (fun t => (q191 ◇ (q192 ◇ q192)) ◇ t) (cg (fun t => t ◇ q193) (apc256 q191 q191 q191 q192))).symm).trans (apc38 q193 (q191 ◇ (q192 ◇ q192)) q191 q191 q191 q191)).trans (rfl))
  have apc261 : forall (q191 q192 q193 q151 q152 : G), ((q152 ◇ q151) ◇ ((q151 ◇ q151) ◇ q152))=(q152 ◇ (q152 ◇ (q151 ◇ q151))):=by
    intro q191 q192 q193 q151 q152
    exact (((rfl).symm).trans ((((apc260 q152 q151 q152).symm).trans ((apc218 q151 q152).trans (rfl))).trans (rfl))).symm
  have apc262 : forall (q189 q190 q191 q192 q193 q151 q152 : G), ((q190 ◇ q190) ◇ (q189 ◇ q189))=(q189 ◇ q189):=by
    intro q189 q190 q191 q192 q193 q151 q152
    exact ((apc39 q189 (q190 ◇ q190)).symm).trans ((((apc261 (((q189 ◇ q189) ◇ q190) ◇ ((q190 ◇ q190) ◇ (q189 ◇ q189))) (((q189 ◇ q189) ◇ q190) ◇ ((q190 ◇ q190) ◇ (q189 ◇ q189))) (((q189 ◇ q189) ◇ q190) ◇ ((q190 ◇ q190) ◇ (q189 ◇ q189))) q190 (q189 ◇ q189)).symm).trans ((apc258 q189 q190).trans (rfl))).trans (rfl))
  have apc263 : forall (q194 q195 : G), (q195 ◇ (q194 ◇ q194))=((q194 ◇ q194) ◇ q195):=by
    intro q194 q195
    exact ((rfl).symm).trans ((((cg (fun t => q195 ◇ t) (apc262 q194 q195 q194 q194 q194 q194 q194)).symm).trans (apc38 (q194 ◇ q194) q195 q194 q194 q194 q194)).trans (rfl))
  have apc264 : forall (q189 q190 q191 q192 q193 q194 q195 q151 q152 : G), ((q189 ◇ q189) ◇ (q190 ◇ q190))=(q189 ◇ q189):=by
    intro q189 q190 q191 q192 q193 q194 q195 q151 q152
    exact ((rfl).symm).trans ((((apc263 q189 (q190 ◇ q190)).symm).trans ((apc262 q189 q190 q189 q189 q189 q189 q189).trans (rfl))).trans (rfl))
  have apc266 : forall (q187 q188 q194 q195 q57 q58 : G), ((q58 ◇ q58) ◇ ((q58 ◇ q58) ◇ q57))=(q58 ◇ q58):=by
    intro q187 q188 q194 q195 q57 q58
    exact ((rfl).symm).trans ((((cg (fun t => (q58 ◇ q58) ◇ t) (apc263 q58 q57)).symm).trans ((apc255 q57 q57 q57 q58).trans (rfl))).trans (rfl))
  have apc267 : forall (q196 q197 : G), (q197 ◇ q197)=(q196 ◇ q196):=by
    intro q196 q197
    exact (((((cg (fun t => (q197 ◇ q197) ◇ t) (apc264 q196 q197 ((q196 ◇ q196) ◇ (q197 ◇ q197)) ((q196 ◇ q196) ◇ (q197 ◇ q197)) ((q196 ◇ q196) ◇ (q197 ◇ q197)) ((q196 ◇ q196) ◇ (q197 ◇ q197)) ((q196 ◇ q196) ◇ (q197 ◇ q197)) ((q196 ◇ q196) ◇ (q197 ◇ q197)) ((q196 ◇ q196) ◇ (q197 ◇ q197)))).trans (apc263 q196 (q197 ◇ q197))).trans (apc264 q196 q197 ((q196 ◇ q196) ◇ (q197 ◇ q197)) ((q196 ◇ q196) ◇ (q197 ◇ q197)) ((q196 ◇ q196) ◇ (q197 ◇ q197)) ((q196 ◇ q196) ◇ (q197 ◇ q197)) ((q196 ◇ q196) ◇ (q197 ◇ q197)) ((q196 ◇ q196) ◇ (q197 ◇ q197)) ((q196 ◇ q196) ◇ (q197 ◇ q197)))).symm).trans ((((cg (fun t => (q197 ◇ q197) ◇ t) (apc263 q196 (q197 ◇ q197))).symm).trans (apc266 q196 q196 q196 q196 (q196 ◇ q196) q197)).trans (rfl))).symm
  have apc268 : forall (q198 q199 q200 : G), ((q198 ◇ q198) ◇ (q199 ◇ q200))=(q200 ◇ q200):=by
    intro q198 q199 q200
    exact ((apc263 q198 (q199 ◇ q200)).symm).trans ((((cg (fun t => (q199 ◇ q200) ◇ t) (apc267 q198 q200)).symm).trans (apc222 q199 q200)).trans (rfl))
  have apc270 : forall (q201 q202 : G), ((q201 ◇ q201) ◇ q202)=(q202 ◇ q202):=by
    intro q201 q202
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q202) (apc267 q201 q202)).symm).trans (apc210 q202 q202)).trans (rfl))
  have apc271 : forall (q30 q31 q50 q51 q52 q47 q201 q202 : G), (q31 ◇ (q30 ◇ q30))=(q30 ◇ q31):=by
    intro q30 q31 q50 q51 q52 q47 q201 q202
    exact ((rfl).symm).trans ((((cg (fun t => q31 ◇ t) (apc270 q31 q30)).symm).trans ((apc38 q30 q31 q30 q30 q30 q30).trans (rfl))).trans (rfl))
  have apc272 : forall (q203 q204 q205 : G), (q204 ◇ q205)=(q203 ◇ q205):=by
    intro q203 q204 q205
    exact (((apc271 q203 q205 (q205 ◇ (q203 ◇ q203)) (q205 ◇ (q203 ◇ q203)) (q205 ◇ (q203 ◇ q203)) (q205 ◇ (q203 ◇ q203)) (q205 ◇ (q203 ◇ q203)) (q205 ◇ (q203 ◇ q203))).symm).trans ((((cg (fun t => q205 ◇ t) (apc267 q203 q204)).symm).trans (apc271 q204 q205 q203 q203 q203 q203 q203 q203)).trans (rfl))).symm
  have apc274 : forall (q206 q207 q208 q209 : G), ((q206 ◇ q207) ◇ (q208 ◇ q209))=(q209 ◇ q209):=by
    intro q206 q207 q208 q209
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q208 ◇ q209)) (apc272 q206 q207 q207)).symm).trans (apc268 q207 q208 q209)).trans (rfl))
  have apc275 : forall (q210 q211 q212 : G), (q212 ◇ (q210 ◇ q211))=(q212 ◇ q212):=by
    intro q210 q211 q212
    exact ((apc271 q212 (q210 ◇ q211) ((q210 ◇ q211) ◇ (q212 ◇ q212)) ((q210 ◇ q211) ◇ (q212 ◇ q212)) ((q210 ◇ q211) ◇ (q212 ◇ q212)) ((q210 ◇ q211) ◇ (q212 ◇ q212)) ((q210 ◇ q211) ◇ (q212 ◇ q212)) ((q210 ◇ q211) ◇ (q212 ◇ q212))).symm).trans ((((cg (fun t => (q210 ◇ q211) ◇ t) (apc210 q210 q212)).symm).trans (apc274 q210 q211 (q210 ◇ q212) q212)).trans (rfl))
  have apc276 : forall (q213 q214 q215 q216 : G), ((q214 ◇ q215) ◇ (q213 ◇ q213))=(q216 ◇ q216):=by
    intro q213 q214 q215 q216
    exact ((rfl).symm).trans ((((cg (fun t => (q214 ◇ q215) ◇ t) (apc267 q213 q216)).symm).trans (apc274 q214 q215 q216 q216)).trans (rfl))
  have apc277 : forall (q217 q218 q219 q220 q221 : G), ((q218 ◇ q219) ◇ (q217 ◇ q217))=(q220 ◇ q221):=by
    intro q217 q218 q219 q220 q221
    exact ((rfl).symm).trans (((((apc276 q217 q218 q219 q221).symm).symm).trans (apc272 q220 q221 q221)).trans (rfl))
  have apc284 : forall (q222 q223 q224 q225 : G), ((q222 ◇ q223) ◇ (q222 ◇ q223))=(q224 ◇ q225):=by
    intro q222 q223 q224 q225
    exact (((rfl).symm).trans ((((apc277 q222 q222 q223 q224 q225).symm).trans (apc275 q222 q222 (q222 ◇ q223))).trans (rfl))).symm
  exact ((apc284 (x ◇ y) ((z ◇ w) ◇ (u ◇ (x ◇ y))) x y).symm).trans (((apc284 (x ◇ y) ((z ◇ w) ◇ (u ◇ (x ◇ y))) (z ◇ w) (u ◇ (x ◇ y))).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45486_to_46755 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45486_to_46755
