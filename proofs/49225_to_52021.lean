-- Equation49225 → Equation52021
-- Recorded verdict: true
-- Premise: x * y = ((z * z) * y) * (y * x)
-- Conclusion: x * y = ((z * w) * (u * x)) * v
-- Original submission SHA-256: 23d48e99df24b8d365cabc1ec7a2e45502af5d1a0c59c162c3b397a67e4e04df
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ z) ◇ y) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = ((z ◇ w) ◇ (u ◇ x)) ◇ v
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have cg : ∀ (f : G → G) {a b : G}, a = b → f a = f b := by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 : G), ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q2) ◇ (q2 ◇ q1)) = (q1 ◇ q2) := by
    intro q0 q1 q2
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q2 ◇ q1)) (cg (fun t => t ◇ q2) ((h (q0 ◇ q0) (q0 ◇ q0) q0).symm))).symm).trans ((h q1 q2 ((q0 ◇ q0) ◇ (q0 ◇ q0))).symm)).trans (rfl))
  have apc1 : forall (x y z : G), (((z ◇ z) ◇ y) ◇ (y ◇ x)) = (((x ◇ x) ◇ y) ◇ (y ◇ x)) := by
    intro x y z
    exact ((rfl).symm).trans (((h x y z).symm.trans (h x y x)).trans (rfl))
  have apc2 : forall (x y z q0 q1 q2 : G), (((q1 ◇ q1) ◇ q2) ◇ (q2 ◇ q1)) = (q1 ◇ q2) := by
    intro x y z q0 q1 q2
    exact ((rfl).symm).trans ((((apc1 q1 q2 (q0 ◇ q0)).symm).trans ((apc0 q0 q1 q2).trans (rfl))).trans (rfl))
  have apc3 : forall (q3 q0 q1 : G), ((q3 ◇ (q0 ◇ q0)) ◇ (((q0 ◇ q0) ◇ q3) ◇ q1)) = (q1 ◇ ((q0 ◇ q0) ◇ q3)) := by
    intro q3 q0 q1
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (((q0 ◇ q0) ◇ q3) ◇ q1)) ((h q3 (q0 ◇ q0) q0).symm)).symm).trans ((h q1 ((q0 ◇ q0) ◇ q3) (q0 ◇ q0)).symm)).trans (rfl))
  have apc4 : forall (q4 q5 q6 : G), ((q5 ◇ q4) ◇ ((q6 ◇ q6) ◇ q5)) = ((q5 ◇ (q6 ◇ q6)) ◇ (q4 ◇ q5)) := by
    intro q4 q5 q6
    exact (((rfl).symm).trans ((((cg (fun t => (q5 ◇ (q6 ◇ q6)) ◇ t) ((h q4 q5 q6).symm)).symm).trans (apc3 q5 q6 (q5 ◇ q4))).trans (rfl))).symm
  have apc5 : forall (q3 q7 q0 q8 : G), (((q8 ◇ q8) ◇ ((q0 ◇ q0) ◇ q7)) ◇ (q3 ◇ q7)) = ((q7 ◇ (q0 ◇ q0)) ◇ (q3 ◇ q7)) := by
    intro q3 q7 q0 q8
    exact ((rfl).symm).trans ((((cg (fun t => ((q8 ◇ q8) ◇ ((q0 ◇ q0) ◇ q7)) ◇ t) ((h q3 q7 q0).symm)).symm).trans ((h (q7 ◇ q3) ((q0 ◇ q0) ◇ q7) q8).symm)).trans (apc4 q3 q7 q0))
  have apc6 : forall (q9 q10 : G), (((q10 ◇ q10) ◇ (q9 ◇ q9)) ◇ ((q9 ◇ q9) ◇ (q10 ◇ q10))) = ((q10 ◇ q10) ◇ (q9 ◇ q9)) := by
    intro q9 q10
    exact ((rfl).symm).trans ((((apc4 (q9 ◇ q9) (q10 ◇ q10) q9).symm).trans ((h (q10 ◇ q10) (q9 ◇ q9) q10).symm)).trans (rfl))
  have apc7 : forall (q0 q1 q2 : G), ((((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ q2) ◇ (q2 ◇ q1)) = ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q2) ◇ (q2 ◇ q1)) := by
    intro q0 q1 q2
    exact (((rfl).symm).trans (((apc0 q0 q1 q2).trans ((apc0 q1 q1 q2).symm)).trans (rfl))).symm
  have apc11 : forall (q11 q12 q9 q10 : G), (((q10 ◇ q10) ◇ (q12 ◇ q11)) ◇ ((q12 ◇ (q9 ◇ q9)) ◇ (q11 ◇ q12))) = (((q9 ◇ q9) ◇ q12) ◇ (q12 ◇ q11)) := by
    intro q11 q12 q9 q10
    exact ((rfl).symm).trans ((((cg (fun t => ((q10 ◇ q10) ◇ (q12 ◇ q11)) ◇ t) (apc4 q11 q12 q9)).symm).trans ((h ((q9 ◇ q9) ◇ q12) (q12 ◇ q11) q10).symm)).trans (rfl))
  have apc18 : forall (q13 q14 q15 q16 q17 : G), (((q14 ◇ q13) ◇ (q16 ◇ q16)) ◇ (((q15 ◇ q15) ◇ q14) ◇ (q14 ◇ q13))) = (((q17 ◇ q17) ◇ ((q16 ◇ q16) ◇ (q14 ◇ q13))) ◇ (q13 ◇ q14)) := by
    intro q13 q14 q15 q16 q17
    exact (((rfl).symm).trans ((((cg (fun t => ((q17 ◇ q17) ◇ ((q16 ◇ q16) ◇ (q14 ◇ q13))) ◇ t) ((h q13 q14 q15).symm)).symm).trans (apc5 ((q15 ◇ q15) ◇ q14) (q14 ◇ q13) q16 q17)).trans (rfl))).symm
  have apc19 : forall (q18 q19 q20 q21 : G), (((q21 ◇ q21) ◇ ((q20 ◇ q20) ◇ (q19 ◇ q18))) ◇ (q18 ◇ q19)) = (((q19 ◇ q18) ◇ (q20 ◇ q20)) ◇ (q18 ◇ q19)) := by
    intro q18 q19 q20 q21
    exact (((rfl).symm).trans ((((cg (fun t => ((q19 ◇ q18) ◇ (q20 ◇ q20)) ◇ t) ((h q18 q19 q18).symm)).symm).trans (apc18 q18 q19 q18 q20 q21)).trans (rfl))).symm
  have apc20 : forall (q22 q23 : G), ((((q22 ◇ q22) ◇ (q22 ◇ q22)) ◇ (q22 ◇ q22)) ◇ ((q22 ◇ q22) ◇ q23)) = (q23 ◇ (q22 ◇ q22)) := by
    intro q22 q23
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q22 ◇ q22) ◇ q23)) (apc19 q22 q22 q22 (q22 ◇ q22))).symm).trans ((h q23 (q22 ◇ q22) ((q22 ◇ q22) ◇ (q22 ◇ q22))).symm)).trans (rfl))
  have apc21 : forall (q18 q19 q24 q20 : G), (((q19 ◇ q18) ◇ (q20 ◇ q20)) ◇ (((q24 ◇ q24) ◇ q19) ◇ (q19 ◇ q18))) = (((q19 ◇ q18) ◇ (q20 ◇ q20)) ◇ (q18 ◇ q19)) := by
    intro q18 q19 q24 q20
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ (q18 ◇ q19)) ((h (q19 ◇ q18) (q20 ◇ q20) q20).symm)).symm).trans ((apc18 q18 q19 q24 q20 (q20 ◇ q20)).symm)).trans (rfl))).symm
  have apc25 : forall (q25 : G), ((q25 ◇ q25) ◇ ((q25 ◇ q25) ◇ (q25 ◇ q25))) = ((q25 ◇ q25) ◇ (q25 ◇ q25)) := by
    intro q25
    exact ((((apc5 (q25 ◇ q25) (q25 ◇ q25) q25 q25).trans (apc6 q25 q25)).symm).trans ((((apc4 (q25 ◇ q25) (q25 ◇ q25) (q25 ◇ q25)).symm).trans (apc3 (q25 ◇ q25) q25 (q25 ◇ q25))).trans (rfl))).symm
  have apc26 : forall (q26 q6 q27 : G), ((q6 ◇ q6) ◇ (((q6 ◇ (q26 ◇ q26)) ◇ (q6 ◇ q6)) ◇ q27)) = (q27 ◇ ((q6 ◇ (q26 ◇ q26)) ◇ (q6 ◇ q6))) := by
    intro q26 q6 q27
    exact ((cg (fun t => (q6 ◇ q6) ◇ t) (cg (fun t => t ◇ q27) (apc4 q6 q6 q26))).symm).trans ((((cg (fun t => t ◇ (((q6 ◇ q6) ◇ ((q26 ◇ q26) ◇ q6)) ◇ q27)) ((h q6 q6 q26).symm)).symm).trans (apc3 ((q26 ◇ q26) ◇ q6) q6 q27)).trans (cg (fun t => q27 ◇ t) (apc4 q6 q6 q26)))
  have apc27 : forall (q28 q29 : G), (((q29 ◇ q29) ◇ (q28 ◇ q28)) ◇ ((q28 ◇ q28) ◇ (q28 ◇ q28))) = (((q28 ◇ q28) ◇ (q28 ◇ q28)) ◇ (q28 ◇ q28)) := by
    intro q28 q29
    exact ((rfl).symm).trans ((((cg (fun t => ((q29 ◇ q29) ◇ (q28 ◇ q28)) ◇ t) (apc25 q28)).symm).trans ((h ((q28 ◇ q28) ◇ (q28 ◇ q28)) (q28 ◇ q28) q29).symm)).trans (rfl))
  have apc28 : forall (q30 : G), (((q30 ◇ q30) ◇ (q30 ◇ q30)) ◇ (q30 ◇ q30)) = ((q30 ◇ q30) ◇ (q30 ◇ q30)) := by
    intro q30
    exact ((rfl).symm).trans ((((apc27 q30 q30).symm).trans ((h (q30 ◇ q30) (q30 ◇ q30) q30).symm)).trans (rfl))
  have apc29 : forall (q22 q23 q30 : G), (((q22 ◇ q22) ◇ (q22 ◇ q22)) ◇ ((q22 ◇ q22) ◇ q23)) = (q23 ◇ (q22 ◇ q22)) := by
    intro q22 q23 q30
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q22 ◇ q22) ◇ q23)) (apc28 q22)).symm).trans ((apc20 q22 q23).trans (rfl))).trans (rfl))
  have apc32 : forall (q31 q32 q33 q34 : G), ((((q32 ◇ q32) ◇ (q32 ◇ q32)) ◇ q34) ◇ (q34 ◇ q33)) = ((((q31 ◇ q31) ◇ (q31 ◇ q31)) ◇ q34) ◇ (q34 ◇ q33)) := by
    intro q31 q32 q33 q34
    exact (((rfl).symm).trans ((((apc7 q31 q33 q34).symm).trans (apc7 q32 q33 q34)).trans (rfl))).symm
  have apc33 : forall (q35 q36 q37 : G), ((((q35 ◇ q35) ◇ (q35 ◇ q35)) ◇ q37) ◇ (q37 ◇ (q36 ◇ q36))) = ((q36 ◇ q36) ◇ q37) := by
    intro q35 q36 q37
    exact ((rfl).symm).trans ((((apc32 q35 q36 (q36 ◇ q36) q37).symm).trans (apc2 q35 q35 q35 q35 (q36 ◇ q36) q37)).trans (rfl))
  have apc34 : forall (q38 q39 q40 : G), (((q38 ◇ q38) ◇ (q40 ◇ q40)) ◇ (q39 ◇ ((q38 ◇ q38) ◇ (q40 ◇ q40)))) = ((((q38 ◇ q38) ◇ (q40 ◇ q40)) ◇ q39) ◇ ((q40 ◇ q40) ◇ (q38 ◇ q38))) := by
    intro q38 q39 q40
    exact ((rfl).symm).trans ((((cg (fun t => ((q38 ◇ q38) ◇ (q40 ◇ q40)) ◇ t) (apc3 (q40 ◇ q40) q38 q39)).symm).trans (apc3 (q38 ◇ q38) q40 (((q38 ◇ q38) ◇ (q40 ◇ q40)) ◇ q39))).trans (rfl))
  have apc35 : forall (q41 q42 : G), ((((q42 ◇ q42) ◇ (q41 ◇ q41)) ◇ (q41 ◇ q41)) ◇ ((q41 ◇ q41) ◇ (q42 ◇ q42))) = (((q42 ◇ q42) ◇ (q41 ◇ q41)) ◇ (q41 ◇ q41)) := by
    intro q41 q42
    exact ((rfl).symm).trans ((((apc34 q42 (q41 ◇ q41) q41).symm).trans ((h ((q42 ◇ q42) ◇ (q41 ◇ q41)) (q41 ◇ q41) q42).symm)).trans (rfl))
  have apc40 : forall (q43 q44 q45 q46 : G), (((q44 ◇ (q45 ◇ q45)) ◇ (q43 ◇ q44)) ◇ ((q46 ◇ q46) ◇ (q44 ◇ q43))) = (((q44 ◇ q43) ◇ (q46 ◇ q46)) ◇ (q43 ◇ q44)) := by
    intro q43 q44 q45 q46
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q46 ◇ q46) ◇ (q44 ◇ q43))) (apc4 q43 q44 q45)).symm).trans (apc4 ((q45 ◇ q45) ◇ q44) (q44 ◇ q43) q46)).trans (apc21 q43 q44 q45 q46))
  have apc41 : forall (q47 q48 q49 : G), ((q49 ◇ q49) ◇ (((q49 ◇ q49) ◇ (q47 ◇ q47)) ◇ (q49 ◇ q49))) = (((q48 ◇ q48) ◇ q49) ◇ (q49 ◇ q49)) := by
    intro q47 q48 q49
    exact ((rfl).symm).trans ((((cg (fun t => (q49 ◇ q49) ◇ t) (apc40 q49 q49 q48 q47)).symm).trans (apc26 q48 q49 ((q47 ◇ q47) ◇ (q49 ◇ q49)))).trans (apc11 q49 q49 q48 q47))
  have apc44 : forall (q50 q51 : G), ((q51 ◇ q51) ◇ (((q51 ◇ q51) ◇ (q50 ◇ q50)) ◇ (q51 ◇ q51))) = (q51 ◇ q51) := by
    intro q50 q51
    exact ((rfl).symm).trans (((((apc41 q50 q50 q51).symm).symm).trans ((h q51 q51 q50).symm)).trans (rfl))
  have apc45 : forall (q52 : G), ((q52 ◇ q52) ◇ (q52 ◇ q52)) = (q52 ◇ q52) := by
    intro q52
    exact ((apc25 q52).symm).trans ((((cg (fun t => (q52 ◇ q52) ◇ t) (apc28 q52)).symm).trans (apc44 q52 q52)).trans (rfl))
  have apc47 : forall (q53 q54 : G), (((q54 ◇ q54) ◇ (q53 ◇ q53)) ◇ (q53 ◇ q53)) = (q53 ◇ q53) := by
    intro q53 q54
    exact ((rfl).symm).trans ((((cg (fun t => ((q54 ◇ q54) ◇ (q53 ◇ q53)) ◇ t) (apc45 q53)).symm).trans ((h (q53 ◇ q53) (q53 ◇ q53) q54).symm)).trans (apc45 q53))
  have apc49 : forall (q52 q35 q36 q37 : G), (((q35 ◇ q35) ◇ q37) ◇ (q37 ◇ (q36 ◇ q36))) = ((q36 ◇ q36) ◇ q37) := by
    intro q52 q35 q36 q37
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q37 ◇ (q36 ◇ q36))) (cg (fun t => t ◇ q37) (apc45 q35))).symm).trans ((apc33 q35 q36 q37).trans (rfl))).trans (rfl))
  have apc51 : forall (q41 q42 q53 q54 : G), ((q41 ◇ q41) ◇ ((q41 ◇ q41) ◇ (q42 ◇ q42))) = (q41 ◇ q41) := by
    intro q41 q42 q53 q54
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q41 ◇ q41) ◇ (q42 ◇ q42))) (apc47 q41 q42)).symm).trans ((apc35 q41 q42).trans (apc47 q41 q42))).trans (rfl))
  have apc52 : forall (q55 q56 : G), (((q55 ◇ q55) ◇ (q56 ◇ q56)) ◇ (q55 ◇ q55)) = ((q56 ◇ q56) ◇ (q55 ◇ q55)) := by
    intro q55 q56
    exact (((rfl).symm).trans ((((cg (fun t => t ◇ (q55 ◇ q55)) (apc51 q56 q55 q55 q55)).symm).trans (apc19 q55 q55 q56 q56)).trans (rfl))).symm
  have apc54 : forall (q50 q51 q55 q56 : G), ((q51 ◇ q51) ◇ ((q50 ◇ q50) ◇ (q51 ◇ q51))) = (q51 ◇ q51) := by
    intro q50 q51 q55 q56
    exact ((rfl).symm).trans ((((cg (fun t => (q51 ◇ q51) ◇ t) (apc52 q51 q50)).symm).trans ((apc44 q50 q51).trans (rfl))).trans (rfl))
  have apc55 : forall (q57 q58 : G), ((q58 ◇ q58) ◇ (q57 ◇ q57)) = (q57 ◇ q57) := by
    intro q57 q58
    exact (((apc45 q57).symm).trans ((((cg (fun t => t ◇ (q57 ◇ q57)) (apc54 q58 q57 q57 q57)).symm).trans (apc19 q57 q57 q58 q57)).trans (apc52 q57 q58))).symm
  have apc57 : forall (q41 q42 q53 q54 q57 q58 : G), (q42 ◇ q42) = (q41 ◇ q41) := by
    intro q41 q42 q53 q54 q57 q58
    exact ((rfl).symm).trans (((((cg (fun t => (q41 ◇ q41) ◇ t) (apc55 q42 q41)).trans (apc55 q42 q41)).symm).trans ((apc51 q41 q42 q53 q54).trans (rfl))).trans (rfl))
  have apc58 : forall (q59 q60 q61 : G), (((q61 ◇ q61) ◇ q60) ◇ (q59 ◇ q59)) = (q60 ◇ q60) := by
    intro q59 q60 q61
    exact ((rfl).symm).trans ((((cg (fun t => ((q61 ◇ q61) ◇ q60) ◇ t) (apc57 q59 q60 q59 q59 q59 q59)).symm).trans ((h q60 q60 q61).symm)).trans (rfl))
  have apc67 : forall (q62 q63 q64 q65 : G), ((q64 ◇ q64) ◇ q65) = ((q62 ◇ q62) ◇ q65) := by
    intro q62 q63 q64 q65
    exact (((apc49 (((q63 ◇ q63) ◇ q65) ◇ (q65 ◇ (q62 ◇ q62))) q63 q62 q65).symm).trans ((((cg (fun t => ((q63 ◇ q63) ◇ q65) ◇ t) (cg (fun t => q65 ◇ t) (apc57 q62 q64 q62 q62 q62 q62))).symm).trans (apc49 q62 q63 q64 q65)).trans (rfl))).symm
  have apc72 : forall (q22 q23 q30 q52 : G), ((q22 ◇ q22) ◇ ((q22 ◇ q22) ◇ q23)) = (q23 ◇ (q22 ◇ q22)) := by
    intro q22 q23 q30 q52
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q22 ◇ q22) ◇ q23)) (apc45 q22)).symm).trans ((apc29 q22 q23 q30).trans (rfl))).trans (rfl))
  have apc73 : forall (q66 : G), ((q66 ◇ (q66 ◇ q66)) ◇ (q66 ◇ q66)) = (q66 ◇ (q66 ◇ q66)) := by
    intro q66
    exact (((rfl).symm).trans ((((apc72 q66 q66 q66 q66).symm).trans (apc4 q66 q66 q66)).trans (rfl))).symm
  have apc75 : forall (q67 q68 : G), ((q68 ◇ (q68 ◇ q68)) ◇ (q67 ◇ q67)) = (q68 ◇ (q68 ◇ q68)) := by
    intro q67 q68
    exact ((rfl).symm).trans ((((cg (fun t => (q68 ◇ (q68 ◇ q68)) ◇ t) (apc57 q67 q68 q67 q67 q67 q67)).symm).trans (apc73 q68)).trans (rfl))
  have apc77 : forall (q69 : G), (((q69 ◇ q69) ◇ q69) ◇ ((q69 ◇ q69) ◇ q69)) = (q69 ◇ (q69 ◇ q69)) := by
    intro q69
    exact (((rfl).symm).trans ((((apc75 ((q69 ◇ q69) ◇ q69) q69).symm).trans (apc3 q69 q69 ((q69 ◇ q69) ◇ q69))).trans (rfl))).symm
  have apc78 : forall (q70 q71 q72 : G), ((q70 ◇ (q70 ◇ q70)) ◇ q72) = ((q71 ◇ q71) ◇ q72) := by
    intro q70 q71 q72
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q72) (apc77 q70)).symm).trans (apc67 q71 q70 ((q70 ◇ q70) ◇ q70) q72)).trans (rfl))
  have apc80 : forall (q73 q74 q75 q76 : G), ((q74 ◇ (q73 ◇ q73)) ◇ q76) = ((q75 ◇ q75) ◇ q76) := by
    intro q73 q74 q75 q76
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q76) (cg (fun t => q74 ◇ t) (apc57 q73 q74 q73 q73 q73 q73))).symm).trans (apc78 q74 q75 q76)).trans (rfl))
  have apc82 : forall (q77 q78 q79 : G), (((q79 ◇ q79) ◇ q78) ◇ (q77 ◇ (q77 ◇ q77))) = (q78 ◇ q78) := by
    intro q77 q78 q79
    exact ((rfl).symm).trans ((((cg (fun t => ((q79 ◇ q79) ◇ q78) ◇ t) (apc77 q77)).symm).trans (apc58 ((q77 ◇ q77) ◇ q77) q78 q79)).trans (rfl))
  have apc83 : forall (q80 : G), ((q80 ◇ q80) ◇ q80) = (q80 ◇ q80) := by
    intro q80
    exact (((rfl).symm).trans ((((apc82 q80 q80 q80).symm).trans ((h (q80 ◇ q80) q80 q80).symm)).trans (rfl))).symm
  have apc86 : forall (q81 q82 q83 : G), ((q82 ◇ (q81 ◇ q81)) ◇ q83) = (q83 ◇ q83) := by
    intro q81 q82 q83
    exact (((rfl).symm).trans ((((apc83 q83).symm).trans ((apc80 q81 q82 q83 q83).symm)).trans (rfl))).symm
  have apc87 : forall (q84 q85 q86 : G), ((q85 ◇ q85) ◇ q86) = (q86 ◇ q86) := by
    intro q84 q85 q86
    exact ((cg (fun t => t ◇ q86) (apc55 q85 q84)).symm).trans ((((cg (fun t => t ◇ q86) (apc67 q84 q84 q84 (q85 ◇ q85))).symm).trans (apc86 q85 (q84 ◇ q84) q86)).trans (rfl))
  have apc98 : forall (q87 q88 : G), ((q88 ◇ q87) ◇ (q88 ◇ q87)) = (q87 ◇ q88) := by
    intro q87 q88
    exact ((apc87 ((q88 ◇ q88) ◇ (q88 ◇ q87)) q88 (q88 ◇ q87)).symm).trans ((((cg (fun t => t ◇ (q88 ◇ q87)) (apc83 q88)).symm).trans ((h q87 q88 q88).symm)).trans (rfl))
  have apc101 : forall (q89 q90 q91 : G), (q91 ◇ q91) = (q89 ◇ q90) := by
    intro q89 q90 q91
    exact (((rfl).symm).trans ((((apc98 q89 q90).symm).trans (apc57 q91 (q90 ◇ q89) q89 q89 q89 q89)).trans (rfl))).symm
  exact ((apc101 x y (x ◇ y)).symm).trans (((apc101 ((z ◇ w) ◇ (u ◇ x)) v (x ◇ y)).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49225_to_52021 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49225_to_52021
