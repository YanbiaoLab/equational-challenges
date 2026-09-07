-- Equation23790 → Equation33904
-- Recorded verdict: true
-- Premise: x = ((y ◇ z) ◇ z) ◇ (y ◇ (x ◇ z))
-- Conclusion: x = ((y ◇ x) ◇ (y ◇ (z ◇ z))) ◇ x
-- Original submission SHA-256: dc031b21bc1af4e46ff06f4a82b4e76626aa6d6d00a71b91a58fac7139194f73
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ z) ◇ (y ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ x) ◇ (y ◇ (z ◇ z))) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f : G → G) {a b : G}, a = b → f a = f b := by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0 q1 q2 : G), (((((q2 ◇ q1) ◇ q1) ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)) ◇ q0) = q2 := by
    intro q0 q1 q2
    exact ((rfl).symm).trans ((((cg (fun t => ((((q2 ◇ q1) ◇ q1) ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)) ◇ t) ((h q0 q2 q1).symm)).symm).trans ((h q2 ((q2 ◇ q1) ◇ q1) (q0 ◇ q1)).symm)).trans (rfl))
  have apc1 : forall (q0 q3 q1 q4 : G), (((q4 ◇ (q3 ◇ (q0 ◇ q1))) ◇ (q3 ◇ (q0 ◇ q1))) ◇ (q4 ◇ q0)) = ((q3 ◇ q1) ◇ q1) := by
    intro q0 q3 q1 q4
    exact ((rfl).symm).trans ((((cg (fun t => ((q4 ◇ (q3 ◇ (q0 ◇ q1))) ◇ (q3 ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => q4 ◇ t) ((h q0 q3 q1).symm))).symm).trans ((h ((q3 ◇ q1) ◇ q1) q4 (q3 ◇ (q0 ◇ q1))).symm)).trans (rfl))
  have apc2 : forall (q5 q6 q7 : G), (((((q7 ◇ (q5 ◇ q6)) ◇ (q5 ◇ q6)) ◇ q5) ◇ q6) ◇ q6) = q7 := by
    intro q5 q6 q7
    exact ((rfl).symm).trans ((((apc1 q5 (((q7 ◇ (q5 ◇ q6)) ◇ (q5 ◇ q6)) ◇ q5) q6 ((q7 ◇ (q5 ◇ q6)) ◇ (q5 ◇ q6))).symm).trans (apc0 (((q7 ◇ (q5 ◇ q6)) ◇ (q5 ◇ q6)) ◇ q5) (q5 ◇ q6) q7)).trans (rfl))
  have apc3 : forall (q8 q9 q10 : G), (((((q10 ◇ q8) ◇ q9) ◇ q9) ◇ (q8 ◇ q9)) ◇ (q8 ◇ q9)) = q10 := by
    intro q8 q9 q10
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q8 ◇ q9)) (cg (fun t => t ◇ (q8 ◇ q9)) (apc1 q8 (q10 ◇ q8) q9 q10))).symm).trans (apc2 (q10 ◇ q8) (q8 ◇ q9) q10)).trans (rfl))
  have apc7 : forall (q11 q12 q13 : G), ((q12 ◇ (q13 ◇ (q11 ◇ q13))) ◇ (q13 ◇ (q11 ◇ q13))) = ((q12 ◇ q11) ◇ q13) := by
    intro q11 q12 q13
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q13 ◇ (q11 ◇ q13))) (cg (fun t => t ◇ (q13 ◇ (q11 ◇ q13))) (apc3 q11 q13 q12))).symm).trans (apc3 q13 (q11 ◇ q13) ((q12 ◇ q11) ◇ q13))).trans (rfl))
  have apc8 : forall (q14 q15 q16 : G), (((q16 ◇ q14) ◇ q15) ◇ (q16 ◇ q14)) = ((q15 ◇ q15) ◇ q15) := by
    intro q14 q15 q16
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q16 ◇ q14)) (apc7 q14 q16 q15)).symm).trans (apc1 q14 q15 q15 q16)).trans (rfl))
  have apc9 : forall (q17 q18 : G), ((((q18 ◇ q18) ◇ q18) ◇ (q17 ◇ q18)) ◇ q17) = q17 := by
    intro q17 q18
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q17) (cg (fun t => t ◇ (q17 ◇ q18)) (apc8 q18 q18 q17))).symm).trans (apc0 q17 q18 q17)).trans (rfl))
  have apc11 : forall (q19 : G), (((q19 ◇ q19) ◇ q19) ◇ q19) = q19 := by
    intro q19
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q19) (apc8 q19 q19 q19)).symm).trans (apc9 q19 q19)).trans (rfl))
  have apc13 : forall (q20 : G), (((q20 ◇ q20) ◇ (q20 ◇ q20)) ◇ (q20 ◇ q20)) = (q20 ◇ q20) := by
    intro q20
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q20 ◇ q20)) (cg (fun t => t ◇ (q20 ◇ q20)) (cg (fun t => t ◇ q20) (apc11 q20)))).symm).trans (apc3 q20 q20 (q20 ◇ q20))).trans (rfl))
  have apc14 : forall (q21 q22 : G), (((q21 ◇ q21) ◇ (q22 ◇ (q21 ◇ q21))) ◇ q22) = q22 := by
    intro q21 q22
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q22) (cg (fun t => t ◇ (q22 ◇ (q21 ◇ q21))) (apc13 q21))).symm).trans (apc9 q22 (q21 ◇ q21))).trans (rfl))
  have apc23 : forall (q23 q24 q25 q26 : G), ((((q24 ◇ q23) ◇ q23) ◇ (q26 ◇ q23)) ◇ (q26 ◇ q23)) = (((q25 ◇ q26) ◇ q26) ◇ (q25 ◇ q24)) := by
    intro q23 q24 q25 q26
    exact (((rfl).symm).trans ((((cg (fun t => ((q25 ◇ q26) ◇ q26) ◇ t) (cg (fun t => q25 ◇ t) (apc0 q26 q23 q24))).symm).trans ((h ((((q24 ◇ q23) ◇ q23) ◇ (q26 ◇ q23)) ◇ (q26 ◇ q23)) q25 q26).symm)).trans (rfl))).symm
  have apc24 : forall (q27 q28 q29 : G), ((((q27 ◇ q28) ◇ q28) ◇ (q27 ◇ q29)) ◇ q28) = q29 := by
    intro q27 q28 q29
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q28) (apc23 q27 q29 q27 q28)).symm).trans (apc0 q28 q27 q29)).trans (rfl))
  have apc26 : forall (q30 q31 : G), ((q30 ◇ ((q30 ◇ q30) ◇ q31)) ◇ q30) = q31 := by
    intro q30 q31
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q30) (cg (fun t => t ◇ ((q30 ◇ q30) ◇ q31)) (apc11 q30))).symm).trans (apc24 (q30 ◇ q30) q30 q31)).trans (rfl))
  have apc41 : forall (q32 q33 q34 : G), (((q32 ◇ q33) ◇ ((q33 ◇ ((q33 ◇ q33) ◇ q32)) ◇ q34)) ◇ q33) = q34 := by
    intro q32 q33 q34
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q33) (cg (fun t => t ◇ ((q33 ◇ ((q33 ◇ q33) ◇ q32)) ◇ q34)) (cg (fun t => t ◇ q33) (apc26 q33 q32)))).symm).trans (apc24 (q33 ◇ ((q33 ◇ q33) ◇ q32)) q33 q34)).trans (rfl))
  have apc42 : forall (q35 q36 : G), (((q35 ◇ q36) ◇ q35) ◇ q36) = q36 := by
    intro q35 q36
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q36) (cg (fun t => (q35 ◇ q36) ◇ t) (apc26 q36 q35))).symm).trans (apc41 q35 q36 q36)).trans (rfl))
  have apc62 : forall (q37 q38 : G), (((q38 ◇ q38) ◇ (q37 ◇ q38)) ◇ (q37 ◇ q38)) = (q37 ◇ q38) := by
    intro q37 q38
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q37 ◇ q38)) (cg (fun t => t ◇ (q37 ◇ q38)) (cg (fun t => t ◇ q38) (apc42 q37 q38)))).symm).trans (apc3 q37 q38 (q37 ◇ q38))).trans (rfl))
  have apc64 : forall (q39 q40 q41 : G), (((q39 ◇ q40) ◇ ((q40 ◇ q40) ◇ q41)) ◇ (q39 ◇ q40)) = q41 := by
    intro q39 q40 q41
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q39 ◇ q40)) (cg (fun t => t ◇ ((q40 ◇ q40) ◇ q41)) (apc62 q39 q40))).symm).trans (apc24 (q40 ◇ q40) (q39 ◇ q40) q41)).trans (rfl))
  have apc67 : forall (q42 q43 : G), ((q43 ◇ ((q42 ◇ q42) ◇ (q43 ◇ (q42 ◇ q42)))) ◇ q43) = q43 := by
    intro q42 q43
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q43) (cg (fun t => t ◇ ((q42 ◇ q42) ◇ (q43 ◇ (q42 ◇ q42)))) (apc14 q42 q43))).symm).trans (apc42 ((q42 ◇ q42) ◇ (q43 ◇ (q42 ◇ q42))) q43)).trans (rfl))
  have apc167 : forall (q11 q44 q12 : G), (((q12 ◇ (q11 ◇ q44)) ◇ ((q11 ◇ q44) ◇ (q11 ◇ q44))) ◇ ((q11 ◇ q44) ◇ (q11 ◇ q44))) = (((q12 ◇ q11) ◇ q44) ◇ q44) := by
    intro q11 q44 q12
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q11 ◇ q44) ◇ (q11 ◇ q44))) (cg (fun t => t ◇ ((q11 ◇ q44) ◇ (q11 ◇ q44))) (cg (fun t => t ◇ (q11 ◇ q44)) (apc3 q11 q44 q12)))).symm).trans (apc3 (q11 ◇ q44) (q11 ◇ q44) (((q12 ◇ q11) ◇ q44) ◇ q44))).trans (rfl))
  have apc168 : forall (q45 q46 : G), ((q45 ◇ q46) ◇ (q46 ◇ q46)) = (q45 ◇ q46) := by
    intro q45 q46
    exact (((rfl).symm).trans ((((apc67 q46 (q45 ◇ q46)).symm).trans (apc64 q45 q46 ((q45 ◇ q46) ◇ (q46 ◇ q46)))).trans (rfl))).symm
  have apc169 : forall (q11 q44 q12 q45 q46 : G), (((q12 ◇ q11) ◇ q44) ◇ q44) = (q12 ◇ (q11 ◇ q44)) := by
    intro q11 q44 q12 q45 q46
    exact (((rfl).symm).trans (((((cg (fun t => t ◇ ((q11 ◇ q44) ◇ (q11 ◇ q44))) (apc168 q12 (q11 ◇ q44))).trans (apc168 q12 (q11 ◇ q44))).symm).trans ((apc167 q11 q44 q12).trans (rfl))).trans (rfl))).symm
  have apc177 : forall (q47 q48 q49 : G), (((q48 ◇ (q47 ◇ q49)) ◇ (q47 ◇ q49)) ◇ q47) = (q48 ◇ q49) := by
    intro q47 q48 q49
    exact ((((cg (fun t => t ◇ (q49 ◇ q49)) (apc168 q48 q49)).trans (apc168 q48 q49)).symm).trans ((((cg (fun t => t ◇ (q49 ◇ q49)) (cg (fun t => t ◇ (q49 ◇ q49)) (cg (fun t => t ◇ q49) (apc2 q47 q49 q48)))).symm).trans (apc3 q49 q49 (((q48 ◇ (q47 ◇ q49)) ◇ (q47 ◇ q49)) ◇ q47))).trans (rfl))).symm
  have apc178 : forall (q5 q6 q7 q47 q48 q49 : G), (q7 ◇ (q6 ◇ q6)) = q7 := by
    intro q5 q6 q7 q47 q48 q49
    exact ((apc169 q6 q6 q7 (((q7 ◇ q6) ◇ q6) ◇ q6) (((q7 ◇ q6) ◇ q6) ◇ q6)).symm).trans ((((cg (fun t => t ◇ q6) (cg (fun t => t ◇ q6) (apc177 q5 q7 q6))).symm).trans ((apc2 q5 q6 q7).trans (rfl))).trans (rfl))
  exact (calc
    x = x := rfl
    _ = (((y ◇ x) ◇ (y ◇ (z ◇ z))) ◇ x) := ((cg (fun t => t ◇ x) (cg (fun t => (y ◇ x) ◇ t) (apc178 (y ◇ (z ◇ z)) z y (y ◇ (z ◇ z)) (y ◇ (z ◇ z)) (y ◇ (z ◇ z))))).trans (apc42 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23790_to_33904 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_23790_to_33904
