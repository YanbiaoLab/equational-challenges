-- Equation42780 → Equation3752
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (x ◇ ((z ◇ x) ◇ x))
-- Conclusion: x ◇ y = (y ◇ x) ◇ (y ◇ y)
-- Original submission SHA-256: be0811c26395056ed7a9dcc6818312eeccd3eace81307fd2103c37c2d4dbd4b6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (x ◇ ((z ◇ x) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = (y ◇ x) ◇ (y ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), (y ◇ (x ◇ ((z ◇ x) ◇ x))) = (y ◇ (x ◇ ((x ◇ x) ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (q0 q1:G), (q1 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((apc0 q0 q1 q0).symm).trans ((h q0 q1 q0).symm)
  have apc4 : forall (q2 q3 q4 q5:G), (q4 ◇ ((q2 ◇ ((q3 ◇ q2) ◇ q2)) ◇ (q2 ◇ (q5 ◇ (q2 ◇ ((q3 ◇ q2) ◇ q2)))))) = ((q2 ◇ ((q3 ◇ q2) ◇ q2)) ◇ q4):=by
    intro q2 q3 q4 q5
    exact ((cg (fun t => q4 ◇ t) (cg (fun t => (q2 ◇ ((q3 ◇ q2) ◇ q2)) ◇ t) ((h q2 (q5 ◇ (q2 ◇ ((q3 ◇ q2) ◇ q2))) q3).symm))).symm).trans ((h (q2 ◇ ((q3 ◇ q2) ◇ q2)) q4 q5).symm)
  have apc5 : forall (q6 q7 q8 q9:G), (q8 ◇ ((q6 ◇ ((q7 ◇ q6) ◇ q6)) ◇ (q6 ◇ (q6 ◇ q9)))) = ((q6 ◇ ((q7 ◇ q6) ◇ q6)) ◇ q8):=by
    intro q6 q7 q8 q9
    exact ((cg (fun t => q8 ◇ t) (cg (fun t => (q6 ◇ ((q7 ◇ q6) ◇ q6)) ◇ t) (cg (fun t => q6 ◇ t) ((h q6 q9 q7).symm)))).symm).trans (apc4 q6 q7 q8 q9)
  have apc7 : forall (q10 q11 q12 q13:G), (q13 ◇ ((q11 ◇ ((q12 ◇ q11) ◇ q11)) ◇ (q11 ◇ (q10 ◇ q11)))) = ((q11 ◇ ((q12 ◇ q11) ◇ q11)) ◇ q13):=by
    intro q10 q11 q12 q13
    exact ((cg (fun t => q13 ◇ t) (cg (fun t => (q11 ◇ ((q12 ◇ q11) ◇ q11)) ◇ t) (cg (fun t => q11 ◇ t) ((h q10 q11 q10).symm)))).symm).trans (apc5 q11 q12 q13 (q10 ◇ ((q10 ◇ q10) ◇ q10)))
  have apc8 : forall (q14 q15 q16:G), (q16 ◇ (q14 ◇ (q14 ◇ ((q15 ◇ q14) ◇ q14)))) = ((q14 ◇ ((q15 ◇ q14) ◇ q14)) ◇ q16):=by
    intro q14 q15 q16
    exact ((cg (fun t => q16 ◇ t) ((h q14 (q14 ◇ ((q15 ◇ q14) ◇ q14)) q14).symm)).symm).trans (apc7 (q14 ◇ q14) q14 q15 q16)
  have apc9 : forall (q17 q18:G), ((q17 ◇ ((q17 ◇ q17) ◇ q17)) ◇ q18) = (q18 ◇ (q17 ◇ q17)):=by
    intro q17 q18
    exact (((cg (fun t => q18 ◇ t) (apc1 q17 q17)).symm).trans (apc8 q17 q17 q18)).symm
  have apc11 : forall (q19 q20:G), ((q19 ◇ q19) ◇ (q20 ◇ q20)) = (q19 ◇ q20):=by
    intro q19 q20
    exact ((apc9 q20 (q19 ◇ q19)).symm).trans ((((apc9 q19 (q20 ◇ ((q20 ◇ q20) ◇ q20))).symm).trans (apc1 q20 (q19 ◇ ((q19 ◇ q19) ◇ q19)))).trans (apc1 q19 q20))
  have apc12 : forall (q21 q22:G), ((q21 ◇ q21) ◇ q22) = (q21 ◇ q22):=by
    intro q21 q22
    exact (((apc11 q21 q22).symm).trans (((cg (fun t => t ◇ (q22 ◇ q22)) (apc11 q21 q21)).symm).trans (apc11 (q21 ◇ q21) q22))).symm
  have apc14 : forall (q23 q24:G), (q24 ◇ (q23 ◇ (q23 ◇ (q23 ◇ q23)))) = (q24 ◇ (q23 ◇ (q23 ◇ q23))):=by
    intro q23 q24
    exact (((cg (fun t => (q24 ◇ q24) ◇ t) (cg (fun t => q23 ◇ t) (cg (fun t => q23 ◇ t) (apc12 q23 q23)))).trans (apc12 q24 (q23 ◇ (q23 ◇ (q23 ◇ q23))))).symm).trans ((((cg (fun t => (q24 ◇ q24) ◇ t) (apc1 q23 (q23 ◇ ((q23 ◇ q23) ◇ q23)))).symm).trans (apc11 q24 (q23 ◇ ((q23 ◇ q23) ◇ q23)))).trans (cg (fun t => q24 ◇ t) (cg (fun t => q23 ◇ t) (apc12 q23 q23))))
  have apc18 : forall (q25 q26:G), (q26 ◇ (q25 ◇ (q25 ◇ q25))) = (q25 ◇ q26):=by
    intro q25 q26
    exact ((((cg (fun t => q26 ◇ t) (cg (fun t => (q25 ◇ q25) ◇ t) (apc12 q25 (q25 ◇ q25)))).trans (cg (fun t => q26 ◇ t) (apc12 q25 (q25 ◇ (q25 ◇ q25))))).trans (apc14 q25 q26)).symm).trans ((((cg (fun t => q26 ◇ t) (cg (fun t => (q25 ◇ q25) ◇ t) (cg (fun t => t ◇ (q25 ◇ q25)) (apc11 q25 q25)))).symm).trans (apc1 (q25 ◇ q25) q26)).trans (apc12 q25 q26))
  have apc19 : forall (q25 q26 q23 q24:G), (q24 ◇ (q23 ◇ q23)) = (q23 ◇ q24):=by
    intro q25 q26 q23 q24
    exact ((cg (fun t => q24 ◇ t) (apc18 q23 q23)).symm).trans ((apc14 q23 q24).trans (apc18 q23 q24))
  have apc20 : forall (q27 q28:G), (q28 ◇ q27) = (q27 ◇ q28):=by
    intro q27 q28
    exact ((apc19 (q27 ◇ (q28 ◇ q28)) (q27 ◇ (q28 ◇ q28)) q28 q27).symm).trans ((((apc18 q27 (q28 ◇ q28)).symm).trans (apc12 q28 (q27 ◇ (q27 ◇ q27)))).trans ((cg (fun t => q28 ◇ t) (apc19 (q27 ◇ (q27 ◇ q27)) (q27 ◇ (q27 ◇ q27)) q27 q27)).trans (apc19 (q28 ◇ (q27 ◇ q27)) (q28 ◇ (q27 ◇ q27)) q27 q28)))
  have apc25 : forall (q29 q30 q31:G), ((((q29 ◇ q31) ◇ q29) ◇ q29) ◇ q30) = (q29 ◇ q30):=by
    intro q29 q30 q31
    exact (((((((((((cg (fun t => q30 ◇ t) (cg (fun t => (q29 ◇ (q29 ◇ q29)) ◇ t) (cg (fun t => q29 ◇ t) (cg (fun t => q31 ◇ t) (apc20 (q29 ◇ q29) q29))))).trans (cg (fun t => q30 ◇ t) (cg (fun t => (q29 ◇ (q29 ◇ q29)) ◇ t) (cg (fun t => q29 ◇ t) (cg (fun t => q31 ◇ t) (apc12 q29 q29)))))).trans (cg (fun t => q30 ◇ t) (cg (fun t => (q29 ◇ (q29 ◇ q29)) ◇ t) (cg (fun t => q29 ◇ t) (apc20 (q29 ◇ q29) q31))))).trans (cg (fun t => q30 ◇ t) (cg (fun t => (q29 ◇ (q29 ◇ q29)) ◇ t) (cg (fun t => q29 ◇ t) (apc12 q29 q31))))).trans (cg (fun t => q30 ◇ t) (cg (fun t => t ◇ (q29 ◇ (q29 ◇ q31))) (apc20 (q29 ◇ q29) q29)))).trans (cg (fun t => q30 ◇ t) (cg (fun t => t ◇ (q29 ◇ (q29 ◇ q31))) (apc12 q29 q29)))).trans (cg (fun t => q30 ◇ t) (cg (fun t => (q29 ◇ q29) ◇ t) (apc20 (q29 ◇ q31) q29)))).trans (cg (fun t => q30 ◇ t) (apc12 q29 ((q29 ◇ q31) ◇ q29)))).trans (cg (fun t => q30 ◇ t) (apc20 ((q29 ◇ q31) ◇ q29) q29))).trans (apc20 (((q29 ◇ q31) ◇ q29) ◇ q29) q30)).symm).trans ((((cg (fun t => q30 ◇ t) (cg (fun t => (q29 ◇ (q29 ◇ q29)) ◇ t) (apc18 q29 (q31 ◇ (q29 ◇ (q29 ◇ q29)))))).symm).trans ((h (q29 ◇ (q29 ◇ q29)) q30 q31).symm)).trans (((cg (fun t => t ◇ q30) (apc20 (q29 ◇ q29) q29)).trans (cg (fun t => t ◇ q30) (apc12 q29 q29))).trans (apc12 q29 q30)))
  have apc26 : forall (q32 q33 q34:G), ((((q32 ◇ q33) ◇ q33) ◇ q33) ◇ q34) = (q33 ◇ q34):=by
    intro q32 q33 q34
    exact (((cg (fun t => q34 ◇ t) (apc20 ((q32 ◇ q33) ◇ q33) q33)).trans (apc20 (((q32 ◇ q33) ◇ q33) ◇ q33) q34)).symm).trans (((cg (fun t => q34 ◇ t) (cg (fun t => q33 ◇ t) (cg (fun t => t ◇ q33) (apc25 q32 q33 q32)))).symm).trans ((h q33 q34 (((q32 ◇ q32) ◇ q32) ◇ q32)).symm))
  have apc27 : forall (q35 q36 q37:G), (((q35 ◇ q37) ◇ q37) ◇ q36) = (q36 ◇ q37):=by
    intro q35 q36 q37
    exact (((((((cg (fun t => t ◇ q36) (cg (fun t => t ◇ ((q35 ◇ q37) ◇ q37)) (apc20 ((q35 ◇ q37) ◇ q37) q37))).trans (cg (fun t => t ◇ q36) (apc26 q35 q37 ((q35 ◇ q37) ◇ q37)))).trans (cg (fun t => t ◇ q36) (apc20 ((q35 ◇ q37) ◇ q37) q37))).trans (apc26 q35 q37 q36)).trans (apc20 q36 q37)).symm).trans (((cg (fun t => t ◇ q36) (cg (fun t => t ◇ ((q35 ◇ q37) ◇ q37)) (apc26 q35 q37 ((q35 ◇ q37) ◇ q37)))).symm).trans (apc25 ((q35 ◇ q37) ◇ q37) q36 q37))).symm
  have apc28 : forall (q38 q39 q40 q41:G), (((q38 ◇ q39) ◇ q38) ◇ q40) = (q38 ◇ q40):=by
    intro q38 q39 q40 q41
    exact (((((((cg (fun t => t ◇ q40) (cg (fun t => q38 ◇ t) (cg (fun t => q39 ◇ t) (cg (fun t => q38 ◇ t) (cg (fun t => t ◇ q38) (apc20 q38 q41)))))).trans (cg (fun t => t ◇ q40) (cg (fun t => q38 ◇ t) (cg (fun t => q39 ◇ t) (apc20 ((q38 ◇ q41) ◇ q38) q38))))).trans (cg (fun t => t ◇ q40) (cg (fun t => q38 ◇ t) (apc20 (((q38 ◇ q41) ◇ q38) ◇ q38) q39)))).trans (cg (fun t => t ◇ q40) (cg (fun t => q38 ◇ t) (apc27 (q38 ◇ q41) q39 q38)))).trans (cg (fun t => t ◇ q40) (cg (fun t => q38 ◇ t) (apc20 q38 q39)))).trans (cg (fun t => t ◇ q40) (apc20 (q38 ◇ q39) q38))).symm).trans ((((cg (fun t => t ◇ q40) ((h q38 (q39 ◇ (q38 ◇ ((q41 ◇ q38) ◇ q38))) q41).symm)).symm).trans (apc27 q39 q40 (q38 ◇ ((q41 ◇ q38) ◇ q38)))).trans (((((cg (fun t => q40 ◇ t) (cg (fun t => q38 ◇ t) (cg (fun t => t ◇ q38) (apc20 q38 q41)))).trans (cg (fun t => q40 ◇ t) (apc20 ((q38 ◇ q41) ◇ q38) q38))).trans (apc20 (((q38 ◇ q41) ◇ q38) ◇ q38) q40)).trans (apc27 (q38 ◇ q41) q40 q38)).trans (apc20 q38 q40)))
  have apc29 : forall (q42 q43 q44:G), ((q42 ◇ q43) ◇ q44) = (q43 ◇ q44):=by
    intro q42 q43 q44
    exact ((((apc27 q42 q44 q43).trans (apc20 q43 q44)).symm).trans (((cg (fun t => t ◇ q44) (apc27 q42 (q42 ◇ q43) q43)).symm).trans (apc28 (q42 ◇ q43) q43 q44 q42))).symm
  have apc31 : forall (q45 q46 q47 q48:G), (q46 ◇ q47) = (q45 ◇ q46):=by
    intro q45 q46 q47 q48
    exact ((((((((((((((cg (fun t => q46 ◇ t) (cg (fun t => q45 ◇ t) (cg (fun t => t ◇ (q48 ◇ q45)) (apc20 (q48 ◇ q45) q47)))).trans (cg (fun t => q46 ◇ t) (cg (fun t => q45 ◇ t) (cg (fun t => t ◇ (q48 ◇ q45)) (apc29 q48 q45 q47))))).trans (cg (fun t => q46 ◇ t) (cg (fun t => q45 ◇ t) (apc20 (q48 ◇ q45) (q45 ◇ q47))))).trans (cg (fun t => q46 ◇ t) (cg (fun t => q45 ◇ t) (apc29 q48 q45 (q45 ◇ q47))))).trans (cg (fun t => q46 ◇ t) (cg (fun t => q45 ◇ t) (apc20 (q45 ◇ q47) q45)))).trans (cg (fun t => q46 ◇ t) (cg (fun t => q45 ◇ t) (apc29 q45 q47 q45)))).trans (cg (fun t => q46 ◇ t) (cg (fun t => q45 ◇ t) (apc20 q45 q47)))).trans (cg (fun t => q46 ◇ t) (apc20 (q45 ◇ q47) q45))).trans (cg (fun t => q46 ◇ t) (apc29 q45 q47 q45))).trans (cg (fun t => q46 ◇ t) (apc20 q45 q47))).trans (apc20 (q45 ◇ q47) q46)).trans (apc29 q45 q47 q46)).trans (apc20 q46 q47)).symm).trans ((((cg (fun t => q46 ◇ t) (apc29 q48 q45 ((q47 ◇ (q48 ◇ q45)) ◇ (q48 ◇ q45)))).symm).trans ((h (q48 ◇ q45) q46 q47).symm)).trans (apc29 q48 q45 q46))
  exact (apc31 (y ◇ y) x y (x ◇ y)).trans (apc31 (y ◇ x) (y ◇ y) x (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42780_to_3752 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42780_to_3752
