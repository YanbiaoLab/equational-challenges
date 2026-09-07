-- Equation6010 → Equation61799
-- Recorded verdict: true
-- Premise: x = y ◇ (y ◇ (z ◇ ((x ◇ z) ◇ z)))
-- Conclusion: (x ◇ x) ◇ y = ((y ◇ y) ◇ x) ◇ x
-- Original submission SHA-256: 8eaa17e64b6db0bc88b6de13ac5ae8830cc3b86821661d3db90ee5a90bdd93dd
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ (z ◇ ((x ◇ z) ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ x) ◇ y = ((y ◇ y) ◇ x) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc0:=fun (x y z:G)=>by
    exact ((h x y z).symm).trans (h x x x)
  have apc1:=fun (x y z:G)=>by
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc3:=fun (q0 q1 q2 q3:G)=>by
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => q3 ◇ t) (cg (fun t => (q2 ◇ (q1 ◇ ((q0 ◇ q1) ◇ q1))) ◇ t) (cg (fun t => t ◇ (q2 ◇ (q1 ◇ ((q0 ◇ q1) ◇ q1)))) ((h q0 q2 q1).symm))))).symm).trans ((h q2 q3 (q2 ◇ (q1 ◇ ((q0 ◇ q1) ◇ q1)))).symm)
  have apc4:=fun (q4 q5 q6:G)=>by
    exact ((cg (fun t => q6 ◇ t) (cg (fun t => q6 ◇ t) (cg (fun t => (q5 ◇ (q4 ◇ ((q5 ◇ q4) ◇ q4))) ◇ t) ((h q5 q5 q4).symm)))).symm).trans (apc3 q5 q4 q5 q6)
  have apc6:=fun (q7 q8 q9:G)=>by
    exact ((cg (fun t => ((q8 ◇ ((q7 ◇ q8) ◇ q8)) ◇ (q9 ◇ (((q8 ◇ ((q7 ◇ q8) ◇ q8)) ◇ q9) ◇ q9))) ◇ t) ((h q7 ((q8 ◇ ((q7 ◇ q8) ◇ q8)) ◇ (q9 ◇ (((q8 ◇ ((q7 ◇ q8) ◇ q8)) ◇ q9) ◇ q9))) q8).symm)).symm).trans (apc4 q9 (q8 ◇ ((q7 ◇ q8) ◇ q8)) ((q8 ◇ ((q7 ◇ q8) ◇ q8)) ◇ (q9 ◇ (((q8 ◇ ((q7 ◇ q8) ◇ q8)) ◇ q9) ◇ q9))))
  have apc7:=fun (q10 q11 q12 q13:G)=>by
    exact (((cg (fun t => q12 ◇ t) (cg (fun t => q12 ◇ t) (cg (fun t => q13 ◇ t) (cg (fun t => t ◇ q13) (apc6 q13 q10 q11))))).symm).trans ((h ((q10 ◇ ((q13 ◇ q10) ◇ q10)) ◇ (q11 ◇ (((q10 ◇ ((q13 ◇ q10) ◇ q10)) ◇ q11) ◇ q11))) q12 q13).symm)).symm
  have apc8:=fun (q14 q15 q16:G)=>by
    exact ((cg (fun t => t ◇ q15) (apc7 q16 q14 q14 q15)).symm).trans (apc6 q15 q16 q14)
  have apc9:=fun (q10 q11 q12 q13:G)=>by
    exact ((apc7 q10 q10 q12 q13).symm).trans (apc7 q10 q10 q10 q13)
  have apc10:=fun (q17 q18:G)=>by
    exact ((cg (fun t => t ◇ q18) (cg (fun t => q17 ◇ t) (cg (fun t => q17 ◇ t) (cg (fun t => q18 ◇ t) (cg (fun t => t ◇ q18) (cg (fun t => (q18 ◇ (q18 ◇ ((q18 ◇ q18) ◇ q18))) ◇ t) (apc1 q18 (q18 ◇ (q18 ◇ (q18 ◇ ((q18 ◇ q18) ◇ q18)))) (q18 ◇ (q18 ◇ (q18 ◇ ((q18 ◇ q18) ◇ q18))))))))))).symm).trans ((((cg (fun t => t ◇ q18) (cg (fun t => q17 ◇ t) (cg (fun t => q17 ◇ t) (cg (fun t => q18 ◇ t) (cg (fun t => t ◇ q18) (cg (fun t => (q18 ◇ (q18 ◇ ((q18 ◇ q18) ◇ q18))) ◇ t) (cg (fun t => t ◇ (q18 ◇ (q18 ◇ ((q18 ◇ q18) ◇ q18)))) (apc1 q18 q17 q17)))))))).symm).trans (apc8 q17 q18 (q18 ◇ (q18 ◇ ((q18 ◇ q18) ◇ q18))))).trans ((cg (fun t => (q18 ◇ (q18 ◇ ((q18 ◇ q18) ◇ q18))) ◇ t) (cg (fun t => t ◇ (q18 ◇ (q18 ◇ ((q18 ◇ q18) ◇ q18)))) (apc1 q18 (q18 ◇ (q18 ◇ (q18 ◇ ((q18 ◇ q18) ◇ q18)))) (q18 ◇ (q18 ◇ (q18 ◇ ((q18 ◇ q18) ◇ q18))))))).trans (cg (fun t => (q18 ◇ (q18 ◇ ((q18 ◇ q18) ◇ q18))) ◇ t) (apc1 q18 (q18 ◇ (q18 ◇ (q18 ◇ ((q18 ◇ q18) ◇ q18)))) (q18 ◇ (q18 ◇ (q18 ◇ ((q18 ◇ q18) ◇ q18))))))))
  have apc12:=fun (q19 q20 q21:G)=>by
    exact ((cg (fun t => q20 ◇ t) (cg (fun t => q20 ◇ t) (cg (fun t => q21 ◇ t) (cg (fun t => t ◇ q21) (apc10 q19 q21))))).symm).trans ((h (q19 ◇ (q19 ◇ (q21 ◇ (((q21 ◇ (q21 ◇ ((q21 ◇ q21) ◇ q21))) ◇ q21) ◇ q21)))) q20 q21).symm)
  have apc13:=fun (q22 q23:G)=>by
    exact ((apc12 q22 q22 q23).symm).trans ((h (q23 ◇ (q23 ◇ ((q23 ◇ q23) ◇ q23))) q22 q23).symm)
  have apc14:=fun (q10 q11 q12 q13:G)=>by
    exact (apc7 q10 q11 q10 q13).trans (apc9 q10 (q10 ◇ (q10 ◇ (q13 ◇ ((q10 ◇ ((q13 ◇ q10) ◇ q10)) ◇ q13)))) q10 q13)
  have apc18:=fun (q24 q25 q26:G)=>by
    exact ((cg (fun t => q26 ◇ t) (cg (fun t => q26 ◇ t) (cg (fun t => t ◇ (q24 ◇ ((q25 ◇ q24) ◇ q24))) (apc9 q24 (q24 ◇ (q24 ◇ (q25 ◇ ((q24 ◇ ((q25 ◇ q24) ◇ q24)) ◇ q25)))) q24 q25)))).symm).trans (((cg (fun t => q26 ◇ t) (cg (fun t => q26 ◇ t) (cg (fun t => t ◇ (q24 ◇ ((q25 ◇ q24) ◇ q24))) (apc7 q24 q24 q24 q25)))).symm).trans (apc4 q24 (q24 ◇ ((q25 ◇ q24) ◇ q24)) q26))
  have apc19:=fun (q27 q28:G)=>by
    exact (((((cg (fun t => q28 ◇ t) (cg (fun t => q28 ◇ t) (cg (fun t => t ◇ ((q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ ((q27 ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27)))) ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27)))))) (cg (fun t => (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ t) (cg (fun t => (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ t) (cg (fun t => q27 ◇ t) (cg (fun t => t ◇ q27) (cg (fun t => (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ t) (apc1 q27 (q27 ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27)))) (q27 ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))))))))))))).trans (cg (fun t => q28 ◇ t) (cg (fun t => q28 ◇ t) (cg (fun t => ((q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ ((q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ (q27 ◇ (((q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ q27) ◇ q27)))) ◇ t) (cg (fun t => (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ t) (cg (fun t => t ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27)))) (apc1 q27 (q27 ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27)))) (q27 ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))))))))))).trans (cg (fun t => q28 ◇ t) (cg (fun t => q28 ◇ t) (cg (fun t => ((q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ ((q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ (q27 ◇ (((q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ q27) ◇ q27)))) ◇ t) (cg (fun t => (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ t) (apc1 q27 (q27 ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27)))) (q27 ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27)))))))))).trans (cg (fun t => q28 ◇ t) (cg (fun t => q28 ◇ t) (cg (fun t => t ◇ ((q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ q27)) (apc13 (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) q27))))).symm).trans ((((cg (fun t => q28 ◇ t) (cg (fun t => q28 ◇ t) (cg (fun t => t ◇ ((q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ ((q27 ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27)))) ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27)))))) (cg (fun t => (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ t) (cg (fun t => (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ t) (cg (fun t => q27 ◇ t) (cg (fun t => t ◇ q27) (cg (fun t => (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ t) (cg (fun t => t ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27)))) (apc1 q27 q27 q27)))))))))).symm).trans (apc18 (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) q27 q28)).trans ((cg (fun t => (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ t) (cg (fun t => t ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27)))) (apc1 q27 (q27 ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27)))) (q27 ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))))))).trans (cg (fun t => (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))) ◇ t) (apc1 q27 (q27 ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27)))) (q27 ◇ (q27 ◇ (q27 ◇ ((q27 ◇ q27) ◇ q27))))))))
  have apc20:=fun (q29 q30 q31:G)=>by
    exact ((((cg (fun t => q31 ◇ t) (cg (fun t => q31 ◇ t) ((h q29 ((q30 ◇ ((q29 ◇ q30) ◇ q30)) ◇ ((q30 ◇ ((q29 ◇ q30) ◇ q30)) ◇ (((q30 ◇ ((q29 ◇ q30) ◇ q30)) ◇ (q30 ◇ ((q29 ◇ q30) ◇ q30))) ◇ (q30 ◇ ((q29 ◇ q30) ◇ q30))))) q30).symm))).symm).trans (apc19 (q30 ◇ ((q29 ◇ q30) ◇ q30)) q31)).trans (cg (fun t => t ◇ (q30 ◇ ((q29 ◇ q30) ◇ q30))) (apc14 q30 (q30 ◇ ((q29 ◇ q30) ◇ q30)) ((q30 ◇ ((q29 ◇ q30) ◇ q30)) ◇ ((q30 ◇ ((q29 ◇ q30) ◇ q30)) ◇ (((q30 ◇ ((q29 ◇ q30) ◇ q30)) ◇ (q30 ◇ ((q29 ◇ q30) ◇ q30))) ◇ (q30 ◇ ((q29 ◇ q30) ◇ q30))))) q29))).symm
  have apc21:=fun (q29 q30 q31:G)=>by
    exact ((apc20 q29 q29 q31).symm).trans (apc20 q29 q29 q29)
  have apc22:=fun (q32 q33 q34 q35:G)=>by
    exact ((cg (fun t => q35 ◇ t) (cg (fun t => q35 ◇ t) (apc20 q34 q33 q32))).symm).trans (apc18 q33 q34 q35)
  have apc28:=fun (q36 q37 q38 q39 q40:G)=>by
    exact ((apc22 q36 q36 q39 q37).trans ((apc22 q38 q36 q39 q40).symm)).symm
  have apc30:=fun (q41 q42 q43:G)=>by
    exact (((cg (fun t => q42 ◇ t) ((h q41 q42 q42).symm)).symm).trans (apc22 q42 q43 ((q41 ◇ q42) ◇ q42) q42)).symm
  have apc31:=fun (q44 q45 q46:G)=>by
    exact ((cg (fun t => q46 ◇ t) (cg (fun t => q46 ◇ t) (apc30 q44 q45 q44))).symm).trans ((h ((q44 ◇ q45) ◇ q45) q46 q44).symm)
  have apc34:=fun (q36 q37 q38 q39 q40 q44 q45 q46:G)=>by
    exact ((apc31 (q38 ◇ q39) q38 q36).symm).trans ((apc28 q36 q36 q38 q39 q36).trans (apc31 (q36 ◇ q39) q36 q36))
  have apc38:=fun (x y z q44 q45 q46:G)=>by
    exact ((h x x z).trans (apc31 ((x ◇ z) ◇ z) z x)).symm
  have apc40:=fun (q47 q48:G)=>by
    exact ((cg (fun t => t ◇ q48) (apc34 q47 q47 q48 q48 q47 q47 q47 q47)).symm).trans (apc38 q48 q47 q48 q47 q47 q47)
  have apc41:=fun (q49:G)=>by
    exact (((apc40 q49 q49).symm).trans (((cg (fun t => (((q49 ◇ q49) ◇ q49) ◇ q49) ◇ t) (apc40 q49 q49)).symm).trans (apc21 q49 q49 (((q49 ◇ q49) ◇ q49) ◇ q49)))).symm
  have apc42:=fun (q50 q51:G)=>by
    exact (((apc40 q50 (q51 ◇ q50)).symm).trans (((cg (fun t => (((q50 ◇ (q51 ◇ q50)) ◇ q50) ◇ q50) ◇ t) (apc40 q50 (q51 ◇ q50))).symm).trans (apc31 q50 q51 (((q50 ◇ (q51 ◇ q50)) ◇ q50) ◇ q50)))).symm
  have apc43:=fun (q52:G)=>by
    exact (((apc41 q52).symm).trans ((((cg (fun t => t ◇ (q52 ◇ q52)) (apc41 q52)).symm).trans (apc42 q52 (q52 ◇ q52))).trans (apc42 q52 q52))).symm
  exact (calc
    ((x ◇ x) ◇ y)=(x ◇ y):=cg (fun t => t ◇ y) (apc43 x)
    _=(((y ◇ y) ◇ x) ◇ x):=((cg (fun t => t ◇ x) (cg (fun t => t ◇ x) (apc43 y))).trans (apc42 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6010_to_61799 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6010_to_61799
