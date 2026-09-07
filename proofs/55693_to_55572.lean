-- Equation55693 → Equation55572
-- Recorded verdict: true
-- Premise: x ◇ (x ◇ y) = (z ◇ x) ◇ (y ◇ z)
-- Conclusion: x ◇ (x ◇ x) = (x ◇ y) ◇ (z ◇ x)
-- Original submission SHA-256: 85de0dabf3766aa06d7ba5475d8953a68f2391878e9bfdadf0f67249fbb40e2d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ y) = (z ◇ x) ◇ (y ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ x) = (x ◇ y) ◇ (z ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f : G → G) {a b : G}, a = b → f a = f b := by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z : G), ((z ◇ x) ◇ (y ◇ z)) = ((x ◇ x) ◇ (y ◇ x)) := by
    intro x y z
    exact ((rfl).symm).trans (((h x y z).symm.trans (h x y x)).trans (rfl))
  have apc1 : forall (q0 q1 : G), ((q0 ◇ q0) ◇ (q1 ◇ q0)) = (q0 ◇ (q0 ◇ q1)) := by
    intro q0 q1
    exact ((rfl).symm).trans ((((apc0 q0 q1 q0).symm).trans ((h q0 q1 q0).symm)).trans (rfl))
  have apc2 : forall (q2 q3 q4 q5 : G), (((q3 ◇ q4) ◇ q5) ◇ (q2 ◇ (q2 ◇ q3))) = (q5 ◇ (q5 ◇ (q4 ◇ q2))) := by
    intro q2 q3 q4 q5
    exact ((rfl).symm).trans ((((cg (fun t => ((q3 ◇ q4) ◇ q5) ◇ t) ((h q2 q3 q4).symm)).symm).trans ((h q5 (q4 ◇ q2) (q3 ◇ q4)).symm)).trans (rfl))
  have apc3 : forall (q6 q7 : G), (q7 ◇ (q7 ◇ (q6 ◇ q6))) = (q7 ◇ (q7 ◇ q6)) := by
    intro q6 q7
    exact ((rfl).symm).trans ((((apc2 q6 q6 q6 q7).symm).trans ((h q7 q6 (q6 ◇ q6)).symm)).trans (rfl))
  have apc5 : forall (q2 q3 q4 q8 : G), ((q2 ◇ (q2 ◇ q3)) ◇ (q8 ◇ (q4 ◇ q2))) = ((q3 ◇ q4) ◇ ((q3 ◇ q4) ◇ q8)) := by
    intro q2 q3 q4 q8
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q8 ◇ (q4 ◇ q2))) ((h q2 q3 q4).symm)).symm).trans ((h (q3 ◇ q4) q8 (q4 ◇ q2)).symm)).trans (rfl))
  have apc20 : forall (q9 q10 q11 q12 : G), (((q10 ◇ q11) ◇ q12) ◇ (q9 ◇ (q9 ◇ (q10 ◇ q9)))) = (q12 ◇ (q12 ◇ (q11 ◇ (q10 ◇ q9)))) := by
    intro q9 q10 q11 q12
    exact ((rfl).symm).trans ((((cg (fun t => ((q10 ◇ q11) ◇ q12) ◇ t) ((h q9 (q10 ◇ q9) q10).symm)).symm).trans (apc2 (q10 ◇ q9) q10 q11 q12)).trans (rfl))
  have apc21 : forall (q13 q14 q15 : G), (q15 ◇ (q15 ◇ (q14 ◇ (q13 ◇ q13)))) = (q15 ◇ (q15 ◇ (q14 ◇ q13))) := by
    intro q13 q14 q15
    exact (((apc2 q13 q13 q14 q15).symm).trans ((((cg (fun t => ((q13 ◇ q14) ◇ q15) ◇ t) (apc3 q13 q13)).symm).trans (apc20 q13 q13 q14 q15)).trans (rfl))).symm
  have apc22 : forall (q16 q17 q18 : G), (q18 ◇ (q18 ◇ (q16 ◇ (q16 ◇ q17)))) = (q18 ◇ (q18 ◇ ((q17 ◇ q16) ◇ q17))) := by
    intro q16 q17 q18
    exact ((rfl).symm).trans ((((cg (fun t => q18 ◇ t) (cg (fun t => q18 ◇ t) ((h q16 q17 q17).symm))).symm).trans (apc21 q17 (q17 ◇ q16) q18)).trans (rfl))
  have apc23 : forall (q16 q19 q18 : G), (q18 ◇ (q18 ◇ (q19 ◇ (q16 ◇ (q16 ◇ q16))))) = (q18 ◇ (q18 ◇ (q19 ◇ q16))) := by
    intro q16 q19 q18
    exact ((rfl).symm).trans ((((cg (fun t => q18 ◇ t) (cg (fun t => q18 ◇ t) (cg (fun t => q19 ◇ t) ((h q16 q16 q16).symm)))).symm).trans (apc21 (q16 ◇ q16) q19 q18)).trans (apc21 q16 q19 q18))
  have apc27 : forall (q20 q21 q6 q22 q7 : G), (((q20 ◇ (q20 ◇ q21)) ◇ q7) ◇ (q22 ◇ (q22 ◇ (q6 ◇ q20)))) = (q7 ◇ (q7 ◇ ((q21 ◇ q6) ◇ q22))) := by
    intro q20 q21 q6 q22 q7
    exact ((rfl).symm).trans ((((cg (fun t => ((q20 ◇ (q20 ◇ q21)) ◇ q7) ◇ t) (apc2 q20 q21 q6 q22)).symm).trans ((h q7 ((q21 ◇ q6) ◇ q22) (q20 ◇ (q20 ◇ q21))).symm)).trans (rfl))
  have apc29 : forall (q23 q24 q25 : G), (q25 ◇ (q25 ◇ ((q24 ◇ q23) ◇ q24))) = (q25 ◇ (q25 ◇ ((q23 ◇ q24) ◇ q24))) := by
    intro q23 q24 q25
    exact (((rfl).symm).trans ((((apc27 q24 q23 q24 q24 q25).symm).trans (apc20 q24 q24 (q24 ◇ q23) q25)).trans (apc21 q24 (q24 ◇ q23) q25))).symm
  have apc30 : forall (q16 q17 q18 q23 q24 q25 : G), (q18 ◇ (q18 ◇ (q16 ◇ (q16 ◇ q17)))) = (q18 ◇ (q18 ◇ ((q16 ◇ q17) ◇ q17))) := by
    intro q16 q17 q18 q23 q24 q25
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc22 q16 q17 q18).trans (apc29 q16 q17 q18))).trans (rfl))
  have apc31 : forall (q26 q27 q10 q11 : G), ((q11 ◇ (q11 ◇ q26)) ◇ (q27 ◇ (q27 ◇ q10))) = ((q26 ◇ q10) ◇ ((q26 ◇ q10) ◇ (q11 ◇ q27))) := by
    intro q26 q27 q10 q11
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q27 ◇ (q27 ◇ q10))) ((h q11 q26 q10).symm)).symm).trans (apc2 q27 q10 q11 (q26 ◇ q10))).trans (rfl))
  have apc35 : forall (q28 q29 q30 : G), ((q29 ◇ q28) ◇ ((q29 ◇ q28) ◇ (q28 ◇ q30))) = ((q29 ◇ q30) ◇ ((q29 ◇ q30) ◇ q30)) := by
    intro q28 q29 q30
    exact ((rfl).symm).trans ((((apc31 q29 q30 q28 q28).symm).trans (apc5 q28 q29 q30 q30)).trans (rfl))
  have apc36 : forall (q31 q32 q33 : G), (((q32 ◇ (q31 ◇ q32)) ◇ (q31 ◇ q32)) ◇ (((q32 ◇ (q31 ◇ q32)) ◇ (q31 ◇ q32)) ◇ q33)) = (((q31 ◇ q32) ◇ ((q31 ◇ q32) ◇ q31)) ◇ (((q31 ◇ q32) ◇ ((q31 ◇ q32) ◇ q31)) ◇ q33)) := by
    intro q31 q32 q33
    exact ((apc5 ((q31 ◇ q32) ◇ q31) (q32 ◇ (q31 ◇ q32)) (q31 ◇ q32) q33).symm).trans ((((cg (fun t => t ◇ (q33 ◇ ((q31 ◇ q32) ◇ ((q31 ◇ q32) ◇ q31)))) (apc2 (q31 ◇ q32) q31 q32 ((q31 ◇ q32) ◇ q31))).symm).trans (apc1 ((q31 ◇ q32) ◇ ((q31 ◇ q32) ◇ q31)) q33)).trans (rfl))
  have apc37 : forall (q34 q35 : G), ((q35 ◇ q34) ◇ (q34 ◇ (q34 ◇ q34))) = (q35 ◇ (q35 ◇ q35)) := by
    intro q34 q35
    exact ((rfl).symm).trans ((((cg (fun t => (q35 ◇ q34) ◇ t) ((h q34 q34 q35).symm)).symm).trans (apc35 q34 q35 q35)).trans ((apc1 q35 (q35 ◇ q35)).trans (apc3 q35 q35)))
  have apc38 : forall (q36 q37 : G), ((q36 ◇ q37) ◇ ((q36 ◇ q37) ◇ (q36 ◇ q37))) = (q36 ◇ (q36 ◇ (q37 ◇ q36))) := by
    intro q36 q37
    exact ((rfl).symm).trans ((((apc37 q36 (q36 ◇ q37)).symm).trans (apc2 q36 q36 q37 q36)).trans (rfl))
  have apc43 : forall (q38 q39 q40 : G), (q40 ◇ (q40 ◇ ((q38 ◇ q39) ◇ q39))) = (q40 ◇ (q40 ◇ q38)) := by
    intro q38 q39 q40
    exact ((((apc21 q38 q38 q40).trans (apc3 q38 q40)).symm).trans ((((cg (fun t => q40 ◇ t) (cg (fun t => q40 ◇ t) (apc37 q39 q38))).symm).trans (apc23 q39 (q38 ◇ q39) q40)).trans (rfl))).symm
  have apc46 : forall (q16 q17 q18 q23 q24 q25 q38 q39 q40 : G), (q18 ◇ (q18 ◇ (q16 ◇ (q16 ◇ q17)))) = (q18 ◇ (q18 ◇ q16)) := by
    intro q16 q17 q18 q23 q24 q25 q38 q39 q40
    exact ((rfl).symm).trans ((((rfl).symm).trans ((apc30 q16 q17 q18 q23 q24 q25).trans (apc43 q16 q17 q18))).trans (rfl))
  have apc50 : forall (q41 q42 q43 : G), (q43 ◇ (q43 ◇ (q41 ◇ q42))) = (q43 ◇ (q43 ◇ q42)) := by
    intro q41 q42 q43
    exact ((apc46 (q41 ◇ q42) q41 q43 (q43 ◇ (q43 ◇ ((q41 ◇ q42) ◇ ((q41 ◇ q42) ◇ q41)))) (q43 ◇ (q43 ◇ ((q41 ◇ q42) ◇ ((q41 ◇ q42) ◇ q41)))) (q43 ◇ (q43 ◇ ((q41 ◇ q42) ◇ ((q41 ◇ q42) ◇ q41)))) (q43 ◇ (q43 ◇ ((q41 ◇ q42) ◇ ((q41 ◇ q42) ◇ q41)))) (q43 ◇ (q43 ◇ ((q41 ◇ q42) ◇ ((q41 ◇ q42) ◇ q41)))) (q43 ◇ (q43 ◇ ((q41 ◇ q42) ◇ ((q41 ◇ q42) ◇ q41))))).symm).trans ((((cg (fun t => q43 ◇ t) (cg (fun t => q43 ◇ t) ((h (q41 ◇ q42) q41 q42).symm))).symm).trans (apc43 q42 (q41 ◇ q42) q43)).trans (rfl))
  have apc51 : forall (q41 q42 q43 q38 q39 q40 : G), (q40 ◇ (q40 ◇ q39)) = (q40 ◇ (q40 ◇ q38)) := by
    intro q41 q42 q43 q38 q39 q40
    exact ((rfl).symm).trans ((((apc50 (q38 ◇ q39) q39 q40).symm).trans ((apc43 q38 q39 q40).trans (rfl))).trans (rfl))
  have apc53 : forall (q41 q42 q43 q36 q37 : G), ((q36 ◇ q37) ◇ ((q36 ◇ q37) ◇ q37)) = (q36 ◇ (q36 ◇ q36)) := by
    intro q41 q42 q43 q36 q37
    exact ((rfl).symm).trans ((((apc50 q36 q37 (q36 ◇ q37)).symm).trans ((apc38 q36 q37).trans (apc50 q37 q36 q36))).trans (rfl))
  have apc55 : forall (q44 q45 q46 : G), ((q44 ◇ q46) ◇ ((q44 ◇ q46) ◇ q45)) = (q44 ◇ (q44 ◇ q44)) := by
    intro q44 q45 q46
    exact (((rfl).symm).trans ((((apc53 q44 q44 q44 q44 q46).symm).trans (apc51 q44 q44 q44 q45 q46 (q44 ◇ q46))).trans (rfl))).symm
  have apc57 : forall (q31 q32 q33 q44 q45 q46 : G), (q32 ◇ (q32 ◇ q32)) = (q31 ◇ (q31 ◇ q31)) := by
    intro q31 q32 q33 q44 q45 q46
    exact ((rfl).symm).trans (((((apc55 (q32 ◇ (q31 ◇ q32)) q33 (q31 ◇ q32)).trans (apc55 q32 (q32 ◇ (q31 ◇ q32)) (q31 ◇ q32))).symm).trans ((apc36 q31 q32 q33).trans (((cg (fun t => ((q31 ◇ q32) ◇ ((q31 ◇ q32) ◇ q31)) ◇ t) (cg (fun t => t ◇ q33) (apc55 q31 q31 q32))).trans (cg (fun t => t ◇ ((q31 ◇ (q31 ◇ q31)) ◇ q33)) (apc55 q31 q31 q32))).trans (apc55 q31 q33 (q31 ◇ q31))))).trans (rfl))
  have apc58 : forall (q47 q48 q49 : G), (q49 ◇ (q49 ◇ q48)) = (q47 ◇ (q47 ◇ q47)) := by
    intro q47 q48 q49
    exact (((rfl).symm).trans ((((apc57 q47 q49 q47 q47 q47 q47).symm).trans (apc51 q47 q47 q47 q48 q49 q49)).trans (rfl))).symm
  exact (calc
    (x ◇ (x ◇ x)) = (y ◇ (y ◇ z)) := (apc58 x z y).symm
    _ = ((x ◇ y) ◇ (z ◇ x)) := ((h y z x).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_55693_to_55572 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_55693_to_55572
