-- Equation41916 → Equation42400
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (x ◇ (z ◇ (w ◇ y)))
-- Conclusion: x ◇ y = z ◇ (w ◇ (u ◇ (v ◇ y)))
-- Original submission SHA-256: 5eebf5e6f2ddd784cee43b7d4706720ff7e89f98071c30b682cab8653ff536cf
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (x ◇ (z ◇ (w ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = z ◇ (w ◇ (u ◇ (v ◇ y)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z w:G), (y ◇ (x ◇ (z ◇ (w ◇ y)))) = (y ◇ (x ◇ (x ◇ (x ◇ y)))):=by
    intro x y z w
    exact ((h x y z w).symm).trans (h x y x x)
  have apc1 : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((apc0 q0 q1 q0 q0).symm).trans ((h q0 q1 q0 q0).symm)
  have apc3 : forall (q2 q3 q4:G), ((q2 ◇ q3) ◇ (q4 ◇ q3)) = (q3 ◇ (q2 ◇ q3)):=by
    intro q2 q3 q4
    exact ((cg (fun t => (q2 ◇ q3) ◇ t) ((h q4 q3 q2 q2).symm)).symm).trans ((h q3 (q2 ◇ q3) q4 q2).symm)
  have apc4 : forall (q5 q6 q7:G), (q7 ◇ (q6 ◇ (q7 ◇ (q5 ◇ q7)))) = (q6 ◇ q7):=by
    intro q5 q6 q7
    exact ((cg (fun t => q7 ◇ t) (cg (fun t => q6 ◇ t) (apc3 q5 q7 q5))).symm).trans ((h q6 q7 (q5 ◇ q7) q5).symm)
  have apc5 : forall (q2 q8 q9 q3 q4:G), ((q8 ◇ (q2 ◇ q4)) ◇ (q3 ◇ (q9 ◇ q4))) = (q3 ◇ (q8 ◇ (q2 ◇ q4))):=by
    intro q2 q8 q9 q3 q4
    exact ((cg (fun t => (q8 ◇ (q2 ◇ q4)) ◇ t) (cg (fun t => q3 ◇ t) ((h q9 q4 q8 q2).symm))).symm).trans ((h q3 (q8 ◇ (q2 ◇ q4)) q4 q9).symm)
  have apc6 : forall (q10 q11 q12 q13:G), (q12 ◇ (q13 ◇ (q11 ◇ (q10 ◇ q12)))) = ((q11 ◇ (q10 ◇ q12)) ◇ q12):=by
    intro q10 q11 q12 q13
    exact ((cg (fun t => q12 ◇ t) (apc5 q10 q11 q10 q13 q12)).symm).trans ((h (q11 ◇ (q10 ◇ q12)) q12 q13 q10).symm)
  have apc9 : forall (q0 q1 q10 q11 q12 q13:G), ((q0 ◇ (q0 ◇ q1)) ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1 q10 q11 q12 q13
    exact ((apc6 q0 q0 q1 q0).symm).trans (apc1 q0 q1)
  have apc11 : forall (q5 q6 q7 q10 q11 q12 q13:G), ((q7 ◇ (q5 ◇ q7)) ◇ q7) = (q6 ◇ q7):=by
    intro q5 q6 q7 q10 q11 q12 q13
    exact ((apc6 q5 q7 q7 q6).symm).trans (apc4 q5 q6 q7)
  have apc13 : forall (q5 q6 q7 q10 q11 q12 q13:G), (q6 ◇ q7) = (q5 ◇ q7):=by
    intro q5 q6 q7 q10 q11 q12 q13
    exact ((apc11 q5 q6 q7 q10 q11 q12 q13).symm).trans (apc11 q5 q5 q7 q10 q11 q12 q13)
  have apc14 : forall (q14 q15 q16 q17 q18:G), (q14 ◇ (q16 ◇ (q18 ◇ (q15 ◇ q17)))) = (q16 ◇ q17):=by
    intro q14 q15 q16 q17 q18
    exact ((apc13 q14 q17 (q16 ◇ (q18 ◇ (q15 ◇ q17))) q14 q14 q14 q14).symm).trans ((h q16 q17 q18 q15).symm)
  have apc15 : forall (q19 q20:G), (q20 ◇ q20) = (q19 ◇ q20):=by
    intro q19 q20
    exact (((apc11 q20 q19 q20 q19 q19 q19 q19).symm).trans (apc9 q20 q20 q19 q19 q19 q19)).symm
  have apc16 : forall (q21 q22 q23 q24:G), (q23 ◇ (q22 ◇ q23)) = (q21 ◇ (q24 ◇ q23)):=by
    intro q21 q22 q23 q24
    exact (((apc13 q21 (q22 ◇ q23) (q24 ◇ q23) q21 q21 q21 q21).symm).trans (apc3 q22 q23 q24)).symm
  have apc20 : forall (q25 q26 q27 q28:G), (q27 ◇ (q25 ◇ q26)) = (q26 ◇ (q25 ◇ q26)):=by
    intro q25 q26 q27 q28
    exact (((apc3 q25 q26 q28).symm).trans (((cg (fun t => (q25 ◇ q26) ◇ t) (apc14 q27 q25 q28 q26 q25)).symm).trans ((h q27 (q25 ◇ q26) q28 q25).symm))).symm
  have apc21 : forall (q14 q15 q16 q17 q18 q25 q26 q27 q28:G), (q14 ◇ (q16 ◇ (q17 ◇ (q15 ◇ q17)))) = (q16 ◇ q17):=by
    intro q14 q15 q16 q17 q18 q25 q26 q27 q28
    exact ((cg (fun t => q14 ◇ t) (cg (fun t => q16 ◇ t) (apc20 q15 q17 q18 (q18 ◇ (q15 ◇ q17))))).symm).trans (apc14 q14 q15 q16 q17 q18)
  have apc22 : forall (q29 q30 q31 q32 q33 q34:G), (q33 ◇ (q30 ◇ (q31 ◇ (q29 ◇ q32)))) = (q33 ◇ q32):=by
    intro q29 q30 q31 q32 q33 q34
    exact ((((cg (fun t => q34 ◇ t) (cg (fun t => q33 ◇ t) (apc20 q30 q32 (q30 ◇ (q31 ◇ (q29 ◇ q32))) ((q30 ◇ (q31 ◇ (q29 ◇ q32))) ◇ (q30 ◇ q32))))).trans (apc21 q34 q30 q33 q32 (q34 ◇ (q33 ◇ (q32 ◇ (q30 ◇ q32)))) (q34 ◇ (q33 ◇ (q32 ◇ (q30 ◇ q32)))) (q34 ◇ (q33 ◇ (q32 ◇ (q30 ◇ q32)))) (q34 ◇ (q33 ◇ (q32 ◇ (q30 ◇ q32)))) (q34 ◇ (q33 ◇ (q32 ◇ (q30 ◇ q32)))))).symm).trans (((cg (fun t => q34 ◇ t) (cg (fun t => q33 ◇ t) (cg (fun t => (q30 ◇ (q31 ◇ (q29 ◇ q32))) ◇ t) ((h q30 q32 q31 q29).symm)))).symm).trans (apc21 q34 q32 q33 (q30 ◇ (q31 ◇ (q29 ◇ q32))) q29 q29 q29 q29 q29))).symm
  have apc24 : forall (q21 q22 q23 q24:G), (q22 ◇ (q22 ◇ q23)) = (q21 ◇ (q24 ◇ q23)):=by
    intro q21 q22 q23 q24
    exact (((apc16 q21 q22 q23 q24).symm).trans (apc16 q22 q22 q23 q22)).symm
  have apc28 : forall (q25 q26 q27 q28:G), (q26 ◇ (q25 ◇ q26)) = (q25 ◇ (q25 ◇ q26)):=by
    intro q25 q26 q27 q28
    exact ((apc20 q25 q26 q27 (q27 ◇ (q25 ◇ q26))).symm).trans ((apc20 q25 q26 q27 q28).trans ((apc20 q25 q26 q25 q28).symm))
  have apc32 : forall (q25 q26 q27 q28:G), (q27 ◇ (q25 ◇ q26)) = (q25 ◇ (q25 ◇ q26)):=by
    intro q25 q26 q27 q28
    exact (apc20 q25 q26 q27 q28).trans (apc28 q25 q26 (q26 ◇ (q25 ◇ q26)) (q26 ◇ (q25 ◇ q26)))
  have apc33 : forall (q29 q30 q31 q34 q32 q33 q25 q26 q27 q28:G), (q29 ◇ (q29 ◇ (q29 ◇ (q29 ◇ q32)))) = (q33 ◇ q32):=by
    intro q29 q30 q31 q34 q32 q33 q25 q26 q27 q28
    exact ((((cg (fun t => q33 ◇ t) (cg (fun t => q30 ◇ t) (apc32 q29 q32 q31 (q31 ◇ (q29 ◇ q32))))).trans (cg (fun t => q33 ◇ t) (apc32 q29 (q29 ◇ q32) q30 (q30 ◇ (q29 ◇ (q29 ◇ q32)))))).trans (apc32 q29 (q29 ◇ (q29 ◇ q32)) q33 (q33 ◇ (q29 ◇ (q29 ◇ (q29 ◇ q32)))))).symm).trans (apc22 q29 q30 q31 q32 q33 q34)
  have apc41 : forall (q35 q36 q37 q38:G), (q35 ◇ (q35 ◇ (q35 ◇ (q36 ◇ q37)))) = (q38 ◇ q37):=by
    intro q35 q36 q37 q38
    exact (((cg (fun t => q36 ◇ t) (apc32 q35 (q36 ◇ q37) q36 (q36 ◇ (q35 ◇ (q36 ◇ q37))))).trans (apc32 q35 (q35 ◇ (q36 ◇ q37)) q36 (q36 ◇ (q35 ◇ (q35 ◇ (q36 ◇ q37)))))).symm).trans (((cg (fun t => q36 ◇ t) (cg (fun t => q36 ◇ t) (apc13 q35 q36 (q36 ◇ q37) q35 q35 q35 q35))).symm).trans (apc33 q36 q35 q35 q35 q37 q38 q35 q35 q35 q35))
  have apc42 : forall (q39 q40 q41 q42 q43 q44:G), (q39 ◇ (q40 ◇ (q41 ◇ (q42 ◇ q43)))) = (q44 ◇ q43):=by
    intro q39 q40 q41 q42 q43 q44
    exact ((apc24 q39 q41 (q41 ◇ (q42 ◇ q43)) q40).symm).trans (apc41 q41 q42 q43 q44)
  have apc43 : forall (q45 q46 q47 q48 q49:G), (q45 ◇ (q46 ◇ (q47 ◇ (q48 ◇ q49)))) = (q49 ◇ q49):=by
    intro q45 q46 q47 q48 q49
    exact (apc42 q45 q46 q47 q48 q49 q45).trans ((apc15 q45 q49).symm)
  exact (calc
    (x ◇ y) = (y ◇ y):=(apc15 x y).symm
    _ = (z ◇ (w ◇ (u ◇ (v ◇ y)))):=(apc43 z w u v y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41916_to_42400 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41916_to_42400
