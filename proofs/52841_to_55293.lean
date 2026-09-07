-- Equation52841 → Equation55293
-- Recorded verdict: true
-- Premise: x * y = ((z * (w * z)) * x) * x
-- Conclusion: x * (y * z) = y * ((y * z) * z)
-- Original submission SHA-256: 5b0f612c1dd8b6176d69c56d1197d61a66202493b40ee8a9446936f40a950215
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ (w ◇ z)) ◇ x) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ z) = y ◇ ((y ◇ z) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc1 : forall (q0 q1 q2 q3:G), (((q1 ◇ q1) ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1 q2 q3
    exact (((((cg (fun t => t ◇ ((q1 ◇ (q2 ◇ q1)) ◇ q0)) (cg (fun t => t ◇ q0) (cg (fun t => q1 ◇ t) (apc0 q2 q1 (q2 ◇ q1) (q2 ◇ q1))))).trans (cg (fun t => ((q1 ◇ (q2 ◇ q2)) ◇ q0) ◇ t) (cg (fun t => t ◇ q0) (cg (fun t => q1 ◇ t) (apc0 q2 q1 (q2 ◇ q1) (q2 ◇ q1)))))).trans (cg (fun t => t ◇ ((q1 ◇ (q2 ◇ q2)) ◇ q0)) (cg (fun t => t ◇ q0) (apc0 q1 (q2 ◇ q2) (q1 ◇ (q2 ◇ q2)) (q1 ◇ (q2 ◇ q2)))))).trans (cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (cg (fun t => t ◇ q0) (apc0 q1 (q2 ◇ q2) (q1 ◇ (q2 ◇ q2)) (q1 ◇ (q2 ◇ q2)))))).symm).trans ((((apc0 ((q1 ◇ (q2 ◇ q1)) ◇ q0) q0 q2 q2).symm).trans ((h q0 q3 q1 q2).symm)).trans (apc0 q0 q3 (q0 ◇ q3) (q0 ◇ q3)))
  have apc2 : forall (q4 q5 q6:G), ((q5 ◇ q5) ◇ (q5 ◇ q5)) = (q4 ◇ q4):=by
    intro q4 q5 q6
    exact ((((((((((((cg (fun t => ((q5 ◇ (q6 ◇ q5)) ◇ q4) ◇ t) (cg (fun t => t ◇ (q5 ◇ (q6 ◇ q5))) (cg (fun t => t ◇ (q5 ◇ (q6 ◇ q5))) (cg (fun t => q5 ◇ t) (apc0 q6 q5 (q6 ◇ q5) (q6 ◇ q5)))))).trans (cg (fun t => ((q5 ◇ (q6 ◇ q5)) ◇ q4) ◇ t) (cg (fun t => t ◇ (q5 ◇ (q6 ◇ q5))) (cg (fun t => (q5 ◇ (q6 ◇ q6)) ◇ t) (cg (fun t => q5 ◇ t) (apc0 q6 q5 (q6 ◇ q5) (q6 ◇ q5))))))).trans (cg (fun t => t ◇ (((q5 ◇ (q6 ◇ q6)) ◇ (q5 ◇ (q6 ◇ q6))) ◇ (q5 ◇ (q6 ◇ q5)))) (cg (fun t => t ◇ q4) (cg (fun t => q5 ◇ t) (apc0 q6 q5 (q6 ◇ q5) (q6 ◇ q5)))))).trans (cg (fun t => ((q5 ◇ (q6 ◇ q6)) ◇ q4) ◇ t) (cg (fun t => ((q5 ◇ (q6 ◇ q6)) ◇ (q5 ◇ (q6 ◇ q6))) ◇ t) (cg (fun t => q5 ◇ t) (apc0 q6 q5 (q6 ◇ q5) (q6 ◇ q5)))))).trans (cg (fun t => ((q5 ◇ (q6 ◇ q6)) ◇ q4) ◇ t) (cg (fun t => t ◇ (q5 ◇ (q6 ◇ q6))) (cg (fun t => t ◇ (q5 ◇ (q6 ◇ q6))) (apc0 q5 (q6 ◇ q6) (q5 ◇ (q6 ◇ q6)) (q5 ◇ (q6 ◇ q6))))))).trans (cg (fun t => ((q5 ◇ (q6 ◇ q6)) ◇ q4) ◇ t) (cg (fun t => t ◇ (q5 ◇ (q6 ◇ q6))) (cg (fun t => (q5 ◇ q5) ◇ t) (apc0 q5 (q6 ◇ q6) (q5 ◇ (q6 ◇ q6)) (q5 ◇ (q6 ◇ q6))))))).trans (cg (fun t => t ◇ (((q5 ◇ q5) ◇ (q5 ◇ q5)) ◇ (q5 ◇ (q6 ◇ q6)))) (cg (fun t => t ◇ q4) (apc0 q5 (q6 ◇ q6) (q5 ◇ (q6 ◇ q6)) (q5 ◇ (q6 ◇ q6)))))).trans (cg (fun t => ((q5 ◇ q5) ◇ q4) ◇ t) (cg (fun t => ((q5 ◇ q5) ◇ (q5 ◇ q5)) ◇ t) (apc0 q5 (q6 ◇ q6) (q5 ◇ (q6 ◇ q6)) (q5 ◇ (q6 ◇ q6)))))).trans (apc0 ((q5 ◇ q5) ◇ q4) (((q5 ◇ q5) ◇ (q5 ◇ q5)) ◇ (q5 ◇ q5)) (((q5 ◇ q5) ◇ q4) ◇ (((q5 ◇ q5) ◇ (q5 ◇ q5)) ◇ (q5 ◇ q5))) (((q5 ◇ q5) ◇ q4) ◇ (((q5 ◇ q5) ◇ (q5 ◇ q5)) ◇ (q5 ◇ q5))))).trans (apc1 q4 q5 (((q5 ◇ q5) ◇ q4) ◇ ((q5 ◇ q5) ◇ q4)) (((q5 ◇ q5) ◇ q4) ◇ ((q5 ◇ q5) ◇ q4)))).symm).trans ((((cg (fun t => t ◇ (((q5 ◇ (q6 ◇ q5)) ◇ (q5 ◇ (q6 ◇ q5))) ◇ (q5 ◇ (q6 ◇ q5)))) ((h (q5 ◇ (q6 ◇ q5)) q4 q5 q6).symm)).symm).trans (apc1 (q5 ◇ (q6 ◇ q5)) (q5 ◇ (q6 ◇ q5)) q6 q6)).trans ((((cg (fun t => t ◇ (q5 ◇ (q6 ◇ q5))) (cg (fun t => q5 ◇ t) (apc0 q6 q5 (q6 ◇ q5) (q6 ◇ q5)))).trans (cg (fun t => (q5 ◇ (q6 ◇ q6)) ◇ t) (cg (fun t => q5 ◇ t) (apc0 q6 q5 (q6 ◇ q5) (q6 ◇ q5))))).trans (cg (fun t => t ◇ (q5 ◇ (q6 ◇ q6))) (apc0 q5 (q6 ◇ q6) (q5 ◇ (q6 ◇ q6)) (q5 ◇ (q6 ◇ q6))))).trans (cg (fun t => (q5 ◇ q5) ◇ t) (apc0 q5 (q6 ◇ q6) (q5 ◇ (q6 ◇ q6)) (q5 ◇ (q6 ◇ q6))))))).symm
  have apc3 : forall (q6 q4 q5:G), (q5 ◇ q5) = (q4 ◇ q4):=by
    intro q6 q4 q5
    exact (((apc2 q4 q5 q6).symm).trans (apc2 q5 q5 q6)).symm
  have apc4 : forall (x y z w:G), (((z ◇ z) ◇ x) ◇ x) = (((x ◇ x) ◇ x) ◇ x):=by
    intro x y z w
    exact (((cg (fun t => t ◇ x) (cg (fun t => t ◇ x) (cg (fun t => z ◇ t) (apc0 w z (w ◇ z) (w ◇ z))))).trans (cg (fun t => t ◇ x) (cg (fun t => t ◇ x) (apc0 z (w ◇ w) (z ◇ (w ◇ w)) (z ◇ (w ◇ w)))))).symm).trans ((((h x y z w).symm).trans (h x y x x)).trans (cg (fun t => t ◇ x) (cg (fun t => t ◇ x) (apc0 x (x ◇ x) (x ◇ (x ◇ x)) (x ◇ (x ◇ x))))))
  have apc6 : forall (q7 q8 q9:G), (((q9 ◇ q9) ◇ q8) ◇ ((q7 ◇ q7) ◇ q8)) = (q8 ◇ q8):=by
    intro q7 q8 q9
    exact ((cg (fun t => ((q9 ◇ q9) ◇ q8) ◇ t) (cg (fun t => t ◇ q8) (apc3 q7 q7 q9))).symm).trans (apc1 q8 q9 q7 q7)
  have apc9 : forall (q10 q11 q12 q13 q14:G), (((q11 ◇ q11) ◇ q10) ◇ (q11 ◇ q11)) = ((q11 ◇ q11) ◇ q12):=by
    intro q10 q11 q12 q13 q14
    exact (((((((cg (fun t => t ◇ (q11 ◇ (q13 ◇ (q14 ◇ q13)))) (cg (fun t => t ◇ q10) (cg (fun t => q11 ◇ t) (cg (fun t => q13 ◇ t) (apc0 q14 q13 (q14 ◇ q13) (q14 ◇ q13)))))).trans (cg (fun t => ((q11 ◇ (q13 ◇ (q14 ◇ q14))) ◇ q10) ◇ t) (cg (fun t => q11 ◇ t) (cg (fun t => q13 ◇ t) (apc0 q14 q13 (q14 ◇ q13) (q14 ◇ q13)))))).trans (cg (fun t => t ◇ (q11 ◇ (q13 ◇ (q14 ◇ q14)))) (cg (fun t => t ◇ q10) (cg (fun t => q11 ◇ t) (apc0 q13 (q14 ◇ q14) (q13 ◇ (q14 ◇ q14)) (q13 ◇ (q14 ◇ q14))))))).trans (cg (fun t => ((q11 ◇ (q13 ◇ q13)) ◇ q10) ◇ t) (cg (fun t => q11 ◇ t) (apc0 q13 (q14 ◇ q14) (q13 ◇ (q14 ◇ q14)) (q13 ◇ (q14 ◇ q14)))))).trans (cg (fun t => t ◇ (q11 ◇ (q13 ◇ q13))) (cg (fun t => t ◇ q10) (apc0 q11 (q13 ◇ q13) (q11 ◇ (q13 ◇ q13)) (q11 ◇ (q13 ◇ q13)))))).trans (cg (fun t => ((q11 ◇ q11) ◇ q10) ◇ t) (apc0 q11 (q13 ◇ q13) (q11 ◇ (q13 ◇ q13)) (q11 ◇ (q13 ◇ q13))))).symm).trans ((((cg (fun t => t ◇ (q11 ◇ (q13 ◇ (q14 ◇ q13)))) ((h (q11 ◇ (q13 ◇ (q14 ◇ q13))) q10 q13 q14).symm)).symm).trans ((h (q11 ◇ (q13 ◇ (q14 ◇ q13))) q12 (q13 ◇ (q14 ◇ q13)) q11).symm)).trans (((cg (fun t => t ◇ q12) (cg (fun t => q11 ◇ t) (cg (fun t => q13 ◇ t) (apc0 q14 q13 (q14 ◇ q13) (q14 ◇ q13))))).trans (cg (fun t => t ◇ q12) (cg (fun t => q11 ◇ t) (apc0 q13 (q14 ◇ q14) (q13 ◇ (q14 ◇ q14)) (q13 ◇ (q14 ◇ q14)))))).trans (cg (fun t => t ◇ q12) (apc0 q11 (q13 ◇ q13) (q11 ◇ (q13 ◇ q13)) (q11 ◇ (q13 ◇ q13))))))
  have apc10 : forall (q15 q16 q17:G), ((q16 ◇ q16) ◇ q17) = (q15 ◇ q15):=by
    intro q15 q16 q17
    exact (((apc9 q15 q16 q17 q15 q15).symm).trans (apc0 ((q16 ◇ q16) ◇ q15) (q16 ◇ q16) q15 q15)).trans (apc6 q16 q15 q16)
  have apc15 : forall (q18 q19 q10 q12:G), (((q18 ◇ q18) ◇ q18) ◇ q18) = (q18 ◇ q18):=by
    intro q18 q19 q10 q12
    exact (((cg (fun t => t ◇ q18) (cg (fun t => t ◇ q18) (apc0 q19 (q19 ◇ q10) (q19 ◇ (q19 ◇ q10)) (q19 ◇ (q19 ◇ q10))))).trans (apc4 q18 (((q19 ◇ q19) ◇ q18) ◇ q18) q19 (((q19 ◇ q19) ◇ q18) ◇ q18))).symm).trans ((((cg (fun t => t ◇ q18) (cg (fun t => t ◇ q18) (cg (fun t => q19 ◇ t) ((h q19 q10 q10 q10).symm)))).symm).trans ((h q18 q12 q19 ((q10 ◇ (q10 ◇ q10)) ◇ q19)).symm)).trans (apc0 q18 q12 (q18 ◇ q12) (q18 ◇ q12)))
  have apc18 : forall (q20 q21:G), ((q20 ◇ q20) ◇ q21) = (q21 ◇ q21):=by
    intro q20 q21
    exact ((cg (fun t => t ◇ q21) (apc10 q20 q21 q21)).symm).trans (apc15 q21 q20 q20 q20)
  have apc19 : forall (q10 q12 q13 q14 q19 q11:G), ((q12 ◇ q12) ◇ (q12 ◇ q12)) = (q12 ◇ q10):=by
    intro q10 q12 q13 q14 q19 q11
    exact (((h q12 q10 q13 q14).trans (h ((q13 ◇ (q14 ◇ q13)) ◇ q12) q12 q19 q11)).trans ((((((((((cg (fun t => t ◇ ((q13 ◇ (q14 ◇ q13)) ◇ q12)) (cg (fun t => (q19 ◇ (q11 ◇ q19)) ◇ t) (cg (fun t => t ◇ q12) (cg (fun t => q13 ◇ t) (apc0 q14 q13 (q14 ◇ q13) (q14 ◇ q13)))))).trans (cg (fun t => ((q19 ◇ (q11 ◇ q19)) ◇ ((q13 ◇ (q14 ◇ q14)) ◇ q12)) ◇ t) (cg (fun t => t ◇ q12) (cg (fun t => q13 ◇ t) (apc0 q14 q13 (q14 ◇ q13) (q14 ◇ q13)))))).trans (cg (fun t => t ◇ ((q13 ◇ (q14 ◇ q14)) ◇ q12)) (cg (fun t => t ◇ ((q13 ◇ (q14 ◇ q14)) ◇ q12)) (cg (fun t => q19 ◇ t) (apc0 q11 q19 (q11 ◇ q19) (q11 ◇ q19)))))).trans (cg (fun t => t ◇ ((q13 ◇ (q14 ◇ q14)) ◇ q12)) (cg (fun t => (q19 ◇ (q11 ◇ q11)) ◇ t) (cg (fun t => t ◇ q12) (apc0 q13 (q14 ◇ q14) (q13 ◇ (q14 ◇ q14)) (q13 ◇ (q14 ◇ q14))))))).trans (cg (fun t => t ◇ ((q13 ◇ (q14 ◇ q14)) ◇ q12)) (cg (fun t => (q19 ◇ (q11 ◇ q11)) ◇ t) (apc18 q13 q12)))).trans (cg (fun t => ((q19 ◇ (q11 ◇ q11)) ◇ (q12 ◇ q12)) ◇ t) (cg (fun t => t ◇ q12) (apc0 q13 (q14 ◇ q14) (q13 ◇ (q14 ◇ q14)) (q13 ◇ (q14 ◇ q14)))))).trans (cg (fun t => t ◇ ((q13 ◇ q13) ◇ q12)) (cg (fun t => t ◇ (q12 ◇ q12)) (apc0 q19 (q11 ◇ q11) (q19 ◇ (q11 ◇ q11)) (q19 ◇ (q11 ◇ q11)))))).trans (cg (fun t => ((q19 ◇ q19) ◇ (q12 ◇ q12)) ◇ t) (apc18 q13 q12))).trans (cg (fun t => t ◇ (q12 ◇ q12)) (apc18 q19 (q12 ◇ q12)))).trans (apc18 (q12 ◇ q12) (q12 ◇ q12)))).symm
  have apc21 : forall (q22 q23 q24:G), (q24 ◇ q24) = (q23 ◇ q22):=by
    intro q22 q23 q24
    exact (((apc19 q22 q23 q22 q22 q22 q22).symm).trans (apc3 q22 q24 (q23 ◇ q23))).symm
  exact ((apc21 (y ◇ z) x (x ◇ (y ◇ z))).symm).trans (apc21 ((y ◇ z) ◇ z) y (x ◇ (y ◇ z)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52841_to_55293 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52841_to_55293
