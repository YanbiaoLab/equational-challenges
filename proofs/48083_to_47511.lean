-- Equation48083 → Equation47511
-- Recorded verdict: true
-- Premise: x * y = (y * (y * z)) * (y * x)
-- Conclusion: x * y = (z * z) * ((w * z) * x)
-- Original submission SHA-256: 0e75dd5483709541c1fdfbaf3354f61e40243f0b352839b5be0e135c2b2f9463
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ (y ◇ z)) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ z) ◇ ((w ◇ z) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((y ◇ (y ◇ z)) ◇ (y ◇ x)) = ((y ◇ (y ◇ x)) ◇ (y ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have apc1 : forall (q0 q1:G), ((q1 ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0)) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((apc0 q0 q1 q0).symm).trans ((h q0 q1 q0).symm)
  have apc2 : forall (q2 q3:G), (((q3 ◇ (q3 ◇ q2)) ◇ (q2 ◇ q3)) ◇ (q2 ◇ q3)) = ((q3 ◇ q2) ◇ (q3 ◇ (q3 ◇ q2))):=by
    intro q2 q3
    exact ((cg (fun t => ((q3 ◇ (q3 ◇ q2)) ◇ (q2 ◇ q3)) ◇ t) (apc1 q2 q3)).symm).trans (((cg (fun t => t ◇ ((q3 ◇ (q3 ◇ q2)) ◇ (q3 ◇ q2))) (cg (fun t => (q3 ◇ (q3 ◇ q2)) ◇ t) (apc1 q2 q3))).symm).trans (apc1 (q3 ◇ q2) (q3 ◇ (q3 ◇ q2))))
  have apc3 : forall (q4:G), ((q4 ◇ q4) ◇ (q4 ◇ (q4 ◇ q4))) = ((q4 ◇ q4) ◇ (q4 ◇ q4)):=by
    intro q4
    exact (((cg (fun t => t ◇ (q4 ◇ q4)) ((h q4 q4 q4).symm)).symm).trans (apc2 q4 q4)).symm
  have apc4 : forall (q5:G), ((q5 ◇ q5) ◇ (q5 ◇ q5)) = (q5 ◇ q5):=by
    intro q5
    exact (((cg (fun t => ((q5 ◇ q5) ◇ ((q5 ◇ q5) ◇ (q5 ◇ q5))) ◇ t) (apc3 q5)).trans (apc1 (q5 ◇ q5) (q5 ◇ q5))).symm).trans ((((cg (fun t => t ◇ ((q5 ◇ q5) ◇ (q5 ◇ (q5 ◇ q5)))) (cg (fun t => (q5 ◇ q5) ◇ t) (apc3 q5))).symm).trans (apc1 (q5 ◇ (q5 ◇ q5)) (q5 ◇ q5))).trans (apc1 q5 q5))
  have apc6 : forall (q4:G), ((q4 ◇ q4) ◇ (q4 ◇ (q4 ◇ q4))) = (q4 ◇ q4):=by
    intro q4
    exact (apc3 q4).trans (apc4 q4)
  have apc7 : forall (q6 q7:G), ((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q7)) = (q7 ◇ (q6 ◇ q6)):=by
    intro q6 q7
    exact ((cg (fun t => t ◇ ((q6 ◇ q6) ◇ q7)) (apc4 q6)).symm).trans (((cg (fun t => t ◇ ((q6 ◇ q6) ◇ q7)) (cg (fun t => (q6 ◇ q6) ◇ t) (apc4 q6))).symm).trans ((h q7 (q6 ◇ q6) (q6 ◇ q6)).symm))
  have apc8 : forall (q8 q9:G), ((q9 ◇ q9) ◇ (q8 ◇ (q9 ◇ q9))) = (((q9 ◇ q9) ◇ q8) ◇ (q9 ◇ q9)):=by
    intro q8 q9
    exact ((cg (fun t => (q9 ◇ q9) ◇ t) (apc7 q9 q8)).symm).trans (apc7 q9 ((q9 ◇ q9) ◇ q8))
  have apc9 : forall (q4:G), (((q4 ◇ q4) ◇ q4) ◇ (q4 ◇ q4)) = (q4 ◇ q4):=by
    intro q4
    exact ((apc8 q4 q4).symm).trans (apc6 q4)
  have apc10 : forall (q10:G), (q10 ◇ (q10 ◇ q10)) = (q10 ◇ q10):=by
    intro q10
    exact (((((cg (fun t => t ◇ (((q10 ◇ q10) ◇ q10) ◇ (q10 ◇ q10))) (apc9 q10)).trans (cg (fun t => (q10 ◇ q10) ◇ t) (apc9 q10))).trans (apc4 q10)).symm).trans ((((cg (fun t => t ◇ (((q10 ◇ q10) ◇ q10) ◇ (q10 ◇ q10))) (cg (fun t => ((q10 ◇ q10) ◇ q10) ◇ t) (apc9 q10))).symm).trans (apc1 (q10 ◇ q10) ((q10 ◇ q10) ◇ q10))).trans (apc7 q10 q10))).symm
  have apc12 : forall (q11:G), ((q11 ◇ q11) ◇ q11) = (q11 ◇ q11):=by
    intro q11
    exact (((((cg (fun t => t ◇ (q11 ◇ (q11 ◇ q11))) (apc10 q11)).trans (cg (fun t => (q11 ◇ q11) ◇ t) (apc10 q11))).trans (apc4 q11)).symm).trans (((cg (fun t => t ◇ (q11 ◇ (q11 ◇ q11))) (cg (fun t => q11 ◇ t) (apc10 q11))).symm).trans (apc1 (q11 ◇ q11) q11))).symm
  have apc15 : forall (q12 q13:G), ((q13 ◇ q13) ◇ (q13 ◇ q12)) = (q12 ◇ q13):=by
    intro q12 q13
    exact ((cg (fun t => t ◇ (q13 ◇ q12)) (apc10 q13)).symm).trans ((h q12 q13 q13).symm)
  have apc17 : forall (q14 q15:G), ((q15 ◇ (q14 ◇ q14)) ◇ (q14 ◇ q14)) = (q14 ◇ q14):=by
    intro q14 q15
    exact ((cg (fun t => t ◇ (q14 ◇ q14)) (apc7 q14 q15)).symm).trans ((((cg (fun t => ((q14 ◇ q14) ◇ ((q14 ◇ q14) ◇ q15)) ◇ t) (apc12 q14)).symm).trans ((h q14 (q14 ◇ q14) q15).symm)).trans (apc10 q14))
  have apc18 : forall (q16 q17:G), (((q16 ◇ q16) ◇ q17) ◇ (q16 ◇ q16)) = (q16 ◇ q16):=by
    intro q16 q17
    exact (((((cg (fun t => t ◇ ((q17 ◇ (q16 ◇ q16)) ◇ (q16 ◇ q16))) (apc17 q16 q17)).trans (cg (fun t => (q16 ◇ q16) ◇ t) (apc17 q16 q17))).trans (apc15 q16 q16)).symm).trans ((((cg (fun t => t ◇ ((q17 ◇ (q16 ◇ q16)) ◇ (q16 ◇ q16))) (cg (fun t => (q17 ◇ (q16 ◇ q16)) ◇ t) (apc17 q16 q17))).symm).trans (apc1 (q16 ◇ q16) (q17 ◇ (q16 ◇ q16)))).trans (apc8 q17 q16))).symm
  have apc19 : forall (q18 q19:G), (q19 ◇ (q18 ◇ q18)) = (q18 ◇ q18):=by
    intro q18 q19
    exact (((((cg (fun t => t ◇ (((q18 ◇ q18) ◇ q19) ◇ (q18 ◇ q18))) (apc18 q18 q19)).trans (cg (fun t => (q18 ◇ q18) ◇ t) (apc18 q18 q19))).trans (apc15 q18 q18)).symm).trans ((((cg (fun t => t ◇ (((q18 ◇ q18) ◇ q19) ◇ (q18 ◇ q18))) (cg (fun t => ((q18 ◇ q18) ◇ q19) ◇ t) (apc18 q18 q19))).symm).trans (apc1 (q18 ◇ q18) ((q18 ◇ q18) ◇ q19))).trans (apc7 q18 q19))).symm
  have apc20 : forall (q20 q21:G), ((q20 ◇ q20) ◇ q21) = (q20 ◇ q20):=by
    intro q20 q21
    exact (((apc19 q20 (q21 ◇ q21)).symm).trans (((cg (fun t => (q21 ◇ q21) ◇ t) (apc19 q20 q21)).symm).trans (apc15 (q20 ◇ q20) q21))).symm
  have apc21 : forall (q12 q13:G), (q13 ◇ q13) = (q12 ◇ q13):=by
    intro q12 q13
    exact ((apc20 q13 (q13 ◇ q12)).symm).trans (apc15 q12 q13)
  have apc24 : forall (q22 q23 q24:G), (q24 ◇ q24) = (q22 ◇ q23):=by
    intro q22 q23 q24
    exact (((cg (fun t => t ◇ (q23 ◇ q22)) (apc19 q24 q23)).trans (apc20 q24 (q23 ◇ q22))).symm).trans (((cg (fun t => t ◇ (q23 ◇ q22)) (cg (fun t => q23 ◇ t) ((apc21 q23 q24).symm))).symm).trans ((h q22 q23 q24).symm))
  exact ((apc24 x y (x ◇ y)).symm).trans (apc24 (z ◇ z) ((w ◇ z) ◇ x) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48083_to_47511 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48083_to_47511
