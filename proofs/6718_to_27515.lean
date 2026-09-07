-- Equation6718 → Equation27515
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ ((y ◇ z) ◇ (z ◇ y)))
-- Conclusion: x = ((x ◇ (x ◇ y)) ◇ x) ◇ (y ◇ x)
-- Original submission SHA-256: 38ddd7268ed6591adfa71ba8a318b73fc948040d0fc420d435cad38bbe08b2ae
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((y ◇ z) ◇ (z ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((x ◇ (x ◇ y)) ◇ x) ◇ (y ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q5 q6:G), ((q5 ◇ q6) ◇ ((q5 ◇ q6) ◇ (q6 ◇ q5))) = q6:=by
    intro q5 q6
    exact ((cg (fun t => (q5 ◇ q6) ◇ t) ((h ((q5 ◇ q6) ◇ (q6 ◇ q5)) q6 q5).symm)).symm).trans ((h q6 (q5 ◇ q6) (q6 ◇ q5)).symm)
  have p1 : forall (q7 q5 q6 q8:G), (q8 ◇ (q6 ◇ (q7 ◇ ((q7 ◇ ((q8 ◇ q5) ◇ (q5 ◇ q8))) ◇ q8)))) = q6:=by
    intro q7 q5 q6 q8
    exact ((cg (fun t => q8 ◇ t) (cg (fun t => q6 ◇ t) (cg (fun t => t ◇ ((q7 ◇ ((q8 ◇ q5) ◇ (q5 ◇ q8))) ◇ q8)) ((h q7 q8 q5).symm)))).symm).trans ((h q6 q8 (q7 ◇ ((q8 ◇ q5) ◇ (q5 ◇ q8)))).symm)
  have p2 : forall (q9 q10 q11:G), (((q9 ◇ q10) ◇ (q10 ◇ q9)) ◇ (q11 ◇ ((((q9 ◇ q10) ◇ (q10 ◇ q9)) ◇ (q9 ◇ q10)) ◇ q10))) = q11:=by
    intro q9 q10 q11
    exact ((cg (fun t => ((q9 ◇ q10) ◇ (q10 ◇ q9)) ◇ t) (cg (fun t => q11 ◇ t) (cg (fun t => (((q9 ◇ q10) ◇ (q10 ◇ q9)) ◇ (q9 ◇ q10)) ◇ t) (p0 q9 q10)))).symm).trans ((h q11 ((q9 ◇ q10) ◇ (q10 ◇ q9)) (q9 ◇ q10)).symm)
  have p3 : forall (q12 q13:G), (q13 ◇ (q13 ◇ (((q12 ◇ q13) ◇ (q13 ◇ q12)) ◇ (q12 ◇ q13)))) = ((q12 ◇ q13) ◇ (q13 ◇ q12)):=by
    intro q12 q13
    exact ((cg (fun t => q13 ◇ t) (p2 q12 q13 (q13 ◇ (((q12 ◇ q13) ◇ (q13 ◇ q12)) ◇ (q12 ◇ q13))))).symm).trans ((h ((q12 ◇ q13) ◇ (q13 ◇ q12)) q13 (((q12 ◇ q13) ◇ (q13 ◇ q12)) ◇ (q12 ◇ q13))).symm)
  have p4 : forall (q7 q5 q6 q14:G), ((q7 ◇ ((q14 ◇ q5) ◇ (q5 ◇ q14))) ◇ (q6 ◇ (((q7 ◇ ((q14 ◇ q5) ◇ (q5 ◇ q14))) ◇ q14) ◇ q7))) = q6:=by
    intro q7 q5 q6 q14
    exact ((cg (fun t => (q7 ◇ ((q14 ◇ q5) ◇ (q5 ◇ q14))) ◇ t) (cg (fun t => q6 ◇ t) (cg (fun t => ((q7 ◇ ((q14 ◇ q5) ◇ (q5 ◇ q14))) ◇ q14) ◇ t) ((h q7 q14 q5).symm)))).symm).trans ((h q6 (q7 ◇ ((q14 ◇ q5) ◇ (q5 ◇ q14))) q14).symm)
  have p5 : forall (q9 q10 q11:G), ((q9 ◇ q10) ◇ (q11 ◇ (q10 ◇ (((q9 ◇ q10) ◇ (q10 ◇ q9)) ◇ (q9 ◇ q10))))) = q11:=by
    intro q9 q10 q11
    exact ((cg (fun t => (q9 ◇ q10) ◇ t) (cg (fun t => q11 ◇ t) (cg (fun t => t ◇ (((q9 ◇ q10) ◇ (q10 ◇ q9)) ◇ (q9 ◇ q10))) (p0 q9 q10)))).symm).trans ((h q11 (q9 ◇ q10) ((q9 ◇ q10) ◇ (q10 ◇ q9))).symm)
  have p6 : forall (q15 q16 q17:G), (q17 ◇ (q17 ◇ ((q17 ◇ ((q16 ◇ q15) ◇ (q15 ◇ q16))) ◇ q16))) = (q17 ◇ ((q16 ◇ q15) ◇ (q15 ◇ q16))):=by
    intro q15 q16 q17
    exact ((cg (fun t => q17 ◇ t) (p4 q17 q15 (q17 ◇ ((q17 ◇ ((q16 ◇ q15) ◇ (q15 ◇ q16))) ◇ q16)) q16)).symm).trans ((h (q17 ◇ ((q16 ◇ q15) ◇ (q15 ◇ q16))) q17 ((q17 ◇ ((q16 ◇ q15) ◇ (q15 ◇ q16))) ◇ q16)).symm)
  have p7 : forall (q18 q19:G), (q19 ◇ (((q18 ◇ q19) ◇ (q19 ◇ q18)) ◇ ((q19 ◇ q18) ◇ (q18 ◇ q19)))) = ((q18 ◇ q19) ◇ (q19 ◇ q18)):=by
    intro q18 q19
    exact (((p3 q18 q19).symm).trans (((cg (fun t => q19 ◇ t) (cg (fun t => q19 ◇ t) (cg (fun t => t ◇ (q18 ◇ q19)) ((h ((q18 ◇ q19) ◇ (q19 ◇ q18)) q19 q18).symm)))).symm).trans (p6 (q19 ◇ q18) (q18 ◇ q19) q19))).symm
  have p8 : forall (q20 q21 q22 q23:G), (((q21 ◇ q20) ◇ (q20 ◇ q21)) ◇ (q23 ◇ (q21 ◇ ((((q21 ◇ q20) ◇ (q20 ◇ q21)) ◇ q22) ◇ (q22 ◇ ((q21 ◇ q20) ◇ (q20 ◇ q21))))))) = q23:=by
    intro q20 q21 q22 q23
    exact ((cg (fun t => ((q21 ◇ q20) ◇ (q20 ◇ q21)) ◇ t) (cg (fun t => q23 ◇ t) ((h (q21 ◇ ((((q21 ◇ q20) ◇ (q20 ◇ q21)) ◇ q22) ◇ (q22 ◇ ((q21 ◇ q20) ◇ (q20 ◇ q21))))) q21 q20).symm))).symm).trans (p1 q21 q22 q23 ((q21 ◇ q20) ◇ (q20 ◇ q21)))
  have p9 : forall (q24 q25:G), (((q25 ◇ q24) ◇ (q24 ◇ q25)) ◇ q25) = ((q25 ◇ q24) ◇ (q24 ◇ q25)):=by
    intro q24 q25
    exact ((cg (fun t => ((q25 ◇ q24) ◇ (q24 ◇ q25)) ◇ t) ((h q25 ((q25 ◇ q24) ◇ (q24 ◇ q25)) q24).symm)).symm).trans (p8 q24 q25 q24 ((q25 ◇ q24) ◇ (q24 ◇ q25)))
  have pa : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ ((q2 ◇ ((q2 ◇ q0) ◇ (q0 ◇ q2))) ◇ ((q2 ◇ q0) ◇ (q0 ◇ q2))))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => (q2 ◇ ((q2 ◇ q0) ◇ (q0 ◇ q2))) ◇ t) (p9 q0 q2)))).symm).trans ((h q1 q2 ((q2 ◇ q0) ◇ (q0 ◇ q2))).symm)
  have pb : forall (q0 q1:G), (((q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ q1) = ((q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ q1) (cg (fun t => (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ t) (p9 q0 q1))).symm).trans (p9 ((q1 ◇ q0) ◇ (q0 ◇ q1)) q1)).trans (cg (fun t => (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ t) (p9 q0 q1))
  have pc : forall (q0 q1:G), (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))))) = q1:=by
    intro q0 q1
    exact ((cg (fun t => ((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => t ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) (p9 q0 q1))).symm).trans (((cg (fun t => t ◇ ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ q1) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))))) (p9 q0 q1)).symm).trans (p0 ((q1 ◇ q0) ◇ (q0 ◇ q1)) q1))
  have pd : forall (q0 q1 q2:G), (q1 ◇ ((((q1 ◇ q2) ◇ (q2 ◇ q1)) ◇ q0) ◇ (q0 ◇ ((q1 ◇ q2) ◇ (q2 ◇ q1))))) = ((((q1 ◇ q2) ◇ (q2 ◇ q1)) ◇ q0) ◇ (q0 ◇ ((q1 ◇ q2) ◇ (q2 ◇ q1)))):=by
    intro q0 q1 q2
    exact ((cg (fun t => q1 ◇ t) (p9 q0 ((q1 ◇ q2) ◇ (q2 ◇ q1)))).symm).trans ((h ((((q1 ◇ q2) ◇ (q2 ◇ q1)) ◇ q0) ◇ (q0 ◇ ((q1 ◇ q2) ◇ (q2 ◇ q1)))) q1 q2).symm)
  have pe : forall (q0 q1:G), (q0 ◇ (((q0 ◇ q1) ◇ (q1 ◇ q0)) ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q1 ◇ q0))))) = (((q0 ◇ q1) ◇ (q1 ◇ q0)) ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q1 ◇ q0)))):=by
    intro q0 q1
    exact (((cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q1 ◇ q0)))) (p9 q1 q0))).symm).trans (pd q0 q0 q1)).trans (cg (fun t => t ◇ (q0 ◇ ((q0 ◇ q1) ◇ (q1 ◇ q0)))) (p9 q1 q0))
  have pf : forall (q0 q1 q2:G), (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ q2) ◇ (q2 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))))) = q1:=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ t) (pd q2 q1 q0)).symm).trans ((h q1 ((q1 ◇ q0) ◇ (q0 ◇ q1)) q2).symm)
  have pg : forall (q20 q21 q22 q23 q0 q1 q2:G), (((q21 ◇ q20) ◇ (q20 ◇ q21)) ◇ (q23 ◇ ((((q21 ◇ q20) ◇ (q20 ◇ q21)) ◇ q22) ◇ (q22 ◇ ((q21 ◇ q20) ◇ (q20 ◇ q21)))))) = q23:=by
    intro q20 q21 q22 q23 q0 q1 q2
    exact ((cg (fun t => ((q21 ◇ q20) ◇ (q20 ◇ q21)) ◇ t) (cg (fun t => q23 ◇ t) (pd q22 q21 q20))).symm).trans (p8 q20 q21 q22 q23)
  have ph : forall (q0 q1:G), (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) ◇ q1)) = ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => ((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) ◇ t) (cg (fun t => ((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => t ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) (p9 q0 q1))))).trans (cg (fun t => ((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) ◇ t) (pc q0 q1)))).symm).trans ((((cg (fun t => ((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => t ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ q1) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))))) (cg (fun t => t ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) (p9 q0 q1)))).symm).trans (pe ((q1 ◇ q0) ◇ (q0 ◇ q1)) q1)).trans (((cg (fun t => ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ q1) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) ◇ t) (cg (fun t => ((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => t ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) (p9 q0 q1)))).trans (cg (fun t => t ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))))) (cg (fun t => t ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) (p9 q0 q1)))).trans (cg (fun t => (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) ◇ t) (pc q0 q1))))
  have pi : forall (q0 q1:G), ((q0 ◇ q1) ◇ (((((q0 ◇ q1) ◇ (q1 ◇ q0)) ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ q1) ◇ ((q0 ◇ q1) ◇ (q1 ◇ q0)))) = (((((q0 ◇ q1) ◇ (q1 ◇ q0)) ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ q1) ◇ ((q0 ◇ q1) ◇ (q1 ◇ q0))):=by
    intro q0 q1
    exact (((cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => ((((q0 ◇ q1) ◇ (q1 ◇ q0)) ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ q1) ◇ t) ((h ((q0 ◇ q1) ◇ (q1 ◇ q0)) q1 q0).symm))).symm).trans (pd q1 (q0 ◇ q1) (q1 ◇ q0))).trans (cg (fun t => ((((q0 ◇ q1) ◇ (q1 ◇ q0)) ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ q1) ◇ t) (p7 q0 q1))
  have pj : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ ((q3 ◇ q1) ◇ (q1 ◇ q3))) ◇ (q4 ◇ (q2 ◇ ((q2 ◇ (((q0 ◇ ((q3 ◇ q1) ◇ (q1 ◇ q3))) ◇ q3) ◇ q0)) ◇ (q0 ◇ ((q3 ◇ q1) ◇ (q1 ◇ q3))))))) = q4:=by
    intro q0 q1 q2 q3 q4
    exact ((cg (fun t => (q0 ◇ ((q3 ◇ q1) ◇ (q1 ◇ q3))) ◇ t) (cg (fun t => q4 ◇ t) (cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q0 ◇ ((q3 ◇ q1) ◇ (q1 ◇ q3)))) (cg (fun t => q2 ◇ t) (cg (fun t => ((q0 ◇ ((q3 ◇ q1) ◇ (q1 ◇ q3))) ◇ q3) ◇ t) ((h q0 q3 q1).symm))))))).symm).trans (p1 q2 q3 q4 (q0 ◇ ((q3 ◇ q1) ◇ (q1 ◇ q3))))
  have pk : forall (q0 q1:G), ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) ◇ ((q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) = (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))):=by
    intro q0 q1
    exact ((pd (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) q1 q0).symm).trans (pa q0 (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) q1)
  have pl : forall (q0 q1:G), ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))))) = (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))):=by
    intro q0 q1
    exact ((cg (fun t => (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) ◇ t) (pk q0 q1)).symm).trans (p0 ((q1 ◇ q0) ◇ (q0 ◇ q1)) (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))))
  have pm : forall (q0 q1:G), ((q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ ((q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))))) = (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))):=by
    intro q0 q1
    exact (((cg (fun t => (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => t ◇ ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))))) (pl q0 q1))).trans (cg (fun t => (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ t) (cg (fun t => (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ t) (pl q0 q1)))).symm).trans (((cg (fun t => t ◇ (((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))))) ◇ ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))))))) (pl q0 q1)).symm).trans (p0 (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))))))
  have pn : forall (q0 q1:G), ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) ◇ q1) = (q1 ◇ (q1 ◇ q1)):=by
    intro q0 q1
    exact (((((((cg (fun t => (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))))) ◇ t) (cg (fun t => t ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ q1) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))))) (cg (fun t => ((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => t ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) (p9 q0 q1))))).trans (cg (fun t => (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))))) ◇ t) (cg (fun t => (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))))) ◇ t) (cg (fun t => ((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => t ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) (p9 q0 q1)))))).trans (cg (fun t => (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))))) ◇ t) (cg (fun t => t ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))))) (pc q0 q1)))).trans (cg (fun t => (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))))) ◇ t) (cg (fun t => q1 ◇ t) (pc q0 q1)))).trans (cg (fun t => t ◇ (q1 ◇ q1)) (pc q0 q1))).symm).trans ((((cg (fun t => t ◇ ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ q1) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))))) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ q1) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))))))) (cg (fun t => ((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => t ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) (p9 q0 q1)))).symm).trans (pm q1 ((q1 ◇ q0) ◇ (q0 ◇ q1)))).trans (((cg (fun t => ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ q1) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) ◇ t) (cg (fun t => ((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => t ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) (p9 q0 q1)))).trans (cg (fun t => t ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))))) (cg (fun t => t ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) (p9 q0 q1)))).trans (cg (fun t => (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) ◇ t) (pc q0 q1))))).symm
  have po : forall (q0 q1:G), (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ (q1 ◇ q1))) = (q1 ◇ (q1 ◇ q1)):=by
    intro q0 q1
    exact ((cg (fun t => ((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ t) (pn q0 q1)).symm).trans ((ph q0 q1).trans (pn q0 q1))
  have pp : forall (q0 q1:G), (q0 ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) = q1:=by
    intro q0 q1
    exact (((((cg (fun t => ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ q0) (p0 q0 q0)))))).trans (cg (fun t => ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (p0 q0 q0))))).trans (cg (fun t => ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (p9 q0 q0)))).trans (cg (fun t => t ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (p0 q0 q0))).symm).trans (((cg (fun t => ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0)) ◇ t) (po (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0) (q0 ◇ q0))))).symm).trans (pj (q0 ◇ q0) q0 ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0)) q0 q1))
  have pq : forall (q0 q1:G), ((((q0 ◇ q0) ◇ q1) ◇ (q1 ◇ (q0 ◇ q0))) ◇ q0) = q0:=by
    intro q0 q1
    exact (((cg (fun t => (((q0 ◇ q0) ◇ q1) ◇ (q1 ◇ (q0 ◇ q0))) ◇ t) (p0 q0 q0)).symm).trans (po q1 (q0 ◇ q0))).trans (p0 q0 q0)
  have pr : forall (q0:G), ((q0 ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0)) = ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ q0)))):=by
    intro q0
    exact (((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (po (q0 ◇ q0) q0))).symm).trans (p3 q0 (q0 ◇ q0))).symm
  have ps : forall (q0:G), ((q0 ◇ q0) ◇ (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) = (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))):=by
    intro q0
    exact (((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (pq q0 (q0 ◇ q0)))).symm).trans (pi q0 q0)).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (pq q0 (q0 ◇ q0)))
  have pt : forall (q0 q1:G), ((q0 ◇ (q0 ◇ q0)) ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ q0))))) = q1:=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (po (q0 ◇ q0) q0)))).symm).trans (p5 q0 (q0 ◇ q0) q1)
  have pu : forall (q0:G), ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ q0))) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => t ◇ (q0 ◇ (q0 ◇ q0))) (p0 (q0 ◇ (q0 ◇ q0)) (q0 ◇ q0))).symm).trans ((((cg (fun t => t ◇ (q0 ◇ (q0 ◇ q0))) (cg (fun t => t ◇ (((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ q0))))) (pt q0 ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0))))).symm).trans (pb (q0 ◇ q0) (q0 ◇ (q0 ◇ q0)))).trans ((cg (fun t => t ◇ (((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ q0))))) (pt q0 ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)))).trans (p0 (q0 ◇ (q0 ◇ q0)) (q0 ◇ q0))))
  have pv : forall (q0:G), ((q0 ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0)) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0
    exact (pr q0).trans (cg (fun t => (q0 ◇ q0) ◇ t) (pu q0))
  have pw : forall (q0 q1:G), ((q0 ◇ (q0 ◇ q0)) ◇ (q1 ◇ (q0 ◇ q0))) = q1:=by
    intro q0 q1
    exact (((cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (po q0 q0)))).trans (cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (pu q0)))).symm).trans (((cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ (q0 ◇ (q0 ◇ q0))) (pv q0))))).symm).trans (p5 q0 (q0 ◇ q0) q1))
  have px : forall (q0:G), (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0)) = q0:=by
    intro q0
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (pw q0 q0))).symm).trans ((((cg (fun t => t ◇ ((q0 ◇ (q0 ◇ q0)) ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))))) (pw q0 q0)).symm).trans (pu (q0 ◇ (q0 ◇ q0)))).trans (pw q0 q0))
  have py : forall (q0 q1:G), (((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ (q1 ◇ q0)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => ((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ t) (cg (fun t => q1 ◇ t) (pw q0 q0))).symm).trans (((cg (fun t => t ◇ (q1 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))))) (cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (pw q0 q0))).symm).trans (pw (q0 ◇ (q0 ◇ q0)) q1))
  have pz : forall (q0:G), (((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => t ◇ (q0 ◇ q0)) (cg (fun t => t ◇ (q0 ◇ q0)) (po q0 q0))).symm).trans (((cg (fun t => t ◇ (q0 ◇ q0)) (cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (pw q0 (q0 ◇ q0)))).symm).trans (pq (q0 ◇ q0) (q0 ◇ (q0 ◇ q0))))
  have p10 : forall (q0:G), ((((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0) ◇ q0) = q0:=by
    intro q0
    exact (((cg (fun t => t ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0)))) (cg (fun t => ((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ t) (pw q0 q0))).trans (cg (fun t => (((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0) ◇ t) (pw q0 q0))).symm).trans ((((cg (fun t => t ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0)))) (cg (fun t => t ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0)))) (cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (pw q0 q0)))).symm).trans (pz (q0 ◇ (q0 ◇ q0)))).trans (pw q0 q0))
  have p11 : forall (q0 q1:G), (((q1 ◇ q1) ◇ q0) ◇ (q0 ◇ (q1 ◇ q1))) = (((q1 ◇ (q1 ◇ q1)) ◇ q1) ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => ((q1 ◇ (q1 ◇ q1)) ◇ q1) ◇ t) (pq q1 q0)).symm).trans (py q1 (((q1 ◇ q1) ◇ q0) ◇ (q0 ◇ (q1 ◇ q1))))).symm
  have p12 : forall (q0:G), (q0 ◇ (((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0)) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0
    exact ((cg (fun t => q0 ◇ t) (p11 (q0 ◇ q0) q0)).symm).trans ((h ((q0 ◇ q0) ◇ (q0 ◇ q0)) q0 q0).symm)
  have p13 : forall (q0:G), ((q0 ◇ (q0 ◇ q0)) ◇ q0) = (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))):=by
    intro q0
    exact ((((cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0)) (px q0))).trans (cg (fun t => q0 ◇ t) (p12 q0))).symm).trans (((cg (fun t => t ◇ ((q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0)) ◇ (((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0))) (px q0)).symm).trans (p0 q0 ((q0 ◇ (q0 ◇ q0)) ◇ q0)))).symm
  have p14 : forall (q0 q1:G), ((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ (q1 ◇ q0)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ q0)) (p13 q0)).symm).trans (py q0 q1)
  have p15 : forall (q0:G), (((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0) ◇ q0) = q0:=by
    intro q0
    exact ((cg (fun t => t ◇ q0) (cg (fun t => t ◇ q0) (p13 q0))).symm).trans (p10 q0)
  have p16 : forall (q0:G), (((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0) = ((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0):=by
    intro q0
    exact (((cg (fun t => (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (p10 q0)).symm).trans (p14 q0 (((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0))).symm
  have p17 : forall (q0 q1:G), (q0 ◇ ((q0 ◇ q1) ◇ (q1 ◇ q0))) = ((q0 ◇ (q0 ◇ q0)) ◇ q0):=by
    intro q0 q1
    exact (((((((cg (fun t => (((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0) ◇ (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0))) ◇ t) (cg (fun t => t ◇ (q1 ◇ ((((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0) ◇ (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0))))) (cg (fun t => t ◇ q1) (cg (fun t => (((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0) ◇ t) (px q0))))).trans (cg (fun t => (((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0) ◇ (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0))) ◇ t) (cg (fun t => (((((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0) ◇ q0) ◇ q1) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => (((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0) ◇ t) (px q0)))))).trans (cg (fun t => (((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0) ◇ (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0))) ◇ t) (cg (fun t => t ◇ (q1 ◇ ((((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0) ◇ q0))) (cg (fun t => t ◇ q1) (p10 q0))))).trans (cg (fun t => (((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0) ◇ (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0))) ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => q1 ◇ t) (p10 q0))))).trans (cg (fun t => t ◇ ((q0 ◇ q1) ◇ (q1 ◇ q0))) (cg (fun t => ((q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0) ◇ t) (px q0)))).trans (cg (fun t => t ◇ ((q0 ◇ q1) ◇ (q1 ◇ q0))) (p15 q0))).symm).trans (((cg (fun t => t ◇ ((((((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0) ◇ (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0))) ◇ q1) ◇ (q1 ◇ ((((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0) ◇ (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0)))))) (cg (fun t => t ◇ (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0))) (p16 q0))).symm).trans (pf q0 ((q0 ◇ (q0 ◇ q0)) ◇ q0) q1))
  have p18 : forall (q0 q1:G), ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ q1) = q1:=by
    intro q0 q1
    exact (((cg (fun t => (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ t) (pf q0 q1 ((q1 ◇ q0) ◇ (q0 ◇ q1)))).symm).trans (ps ((q1 ◇ q0) ◇ (q0 ◇ q1)))).trans (pf q0 q1 ((q1 ◇ q0) ◇ (q0 ◇ q1)))
  have p19 : forall (q0 q1:G), (((q1 ◇ q0) ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ (q1 ◇ q0)) = (q0 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact (((cg (fun t => q0 ◇ t) (py (q1 ◇ q0) (q0 ◇ q1))).symm).trans ((h (((q1 ◇ q0) ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ (q1 ◇ q0)) q0 q1).symm)).symm
  have p1a : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q0 ◇ (q0 ◇ q1))) = (q1 ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q0) ◇ t) (p19 q0 q1)).symm).trans (px (q1 ◇ q0))
  have p1b : forall (q0 q1 q2:G), ((q0 ◇ (q0 ◇ q1)) ◇ (q2 ◇ (q1 ◇ q0))) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q2 ◇ (q1 ◇ q0))) (p19 q0 q1)).symm).trans (py (q1 ◇ q0) q2)
  have p1c : forall (q0 q1:G), ((q0 ◇ (q0 ◇ q1)) ◇ q1) = ((q0 ◇ (q0 ◇ q0)) ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ (q0 ◇ q1)) ◇ t) (py q0 q1)).symm).trans (p1b q0 q1 ((q0 ◇ (q0 ◇ q0)) ◇ q0))
  have p1d : forall (q0 q1 q2:G), (((q1 ◇ q0) ◇ ((q1 ◇ q0) ◇ q2)) ◇ q2) = (q0 ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ q2) (p19 (q1 ◇ q0) q2)).symm).trans (((cg (fun t => (((q2 ◇ (q1 ◇ q0)) ◇ ((q2 ◇ (q1 ◇ q0)) ◇ (q2 ◇ (q1 ◇ q0)))) ◇ (q2 ◇ (q1 ◇ q0))) ◇ t) (p1b q0 q1 q2)).symm).trans (py (q2 ◇ (q1 ◇ q0)) (q0 ◇ (q0 ◇ q1))))
  have p1e : forall (q0 q1:G), (((q0 ◇ (q0 ◇ q1)) ◇ (q1 ◇ q0)) ◇ (q1 ◇ q0)) = (q1 ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ q0)) (cg (fun t => t ◇ (q1 ◇ q0)) (p19 q0 q1))).symm).trans (p10 (q1 ◇ q0))
  have p1f : forall (q0 q1:G), ((q1 ◇ q0) ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) = ((q0 ◇ (q0 ◇ q1)) ◇ (q0 ◇ (q0 ◇ q1))):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ (q0 ◇ (q0 ◇ q1))) (p1d q0 q1 (q1 ◇ q0))).symm).trans (((cg (fun t => (((q1 ◇ q0) ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ◇ (q1 ◇ q0)) ◇ t) (p19 q0 q1)).symm).trans (py (q1 ◇ q0) ((q1 ◇ q0) ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))))).symm
  have p1g : forall (q0 q1 q2:G), (q0 ◇ (q0 ◇ ((q1 ◇ q2) ◇ (q2 ◇ q1)))) = (q1 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0)):=by
    intro q0 q1 q2
    exact (((cg (fun t => q1 ◇ t) (p1c q0 ((q1 ◇ q2) ◇ (q2 ◇ q1)))).symm).trans ((h (q0 ◇ (q0 ◇ ((q1 ◇ q2) ◇ (q2 ◇ q1)))) q1 q2).symm)).symm
  have p1h : forall (q0:G), ((q0 ◇ q0) ◇ q0) = (q0 ◇ (q0 ◇ (q0 ◇ q0))):=by
    intro q0
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) (p1b q0 q0 q0)).symm).trans ((((cg (fun t => (q0 ◇ q0) ◇ t) (p1f q0 q0)).symm).trans (p1g (q0 ◇ q0) q0 q0)).trans (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (q0 ◇ q0)) (p0 q0 q0))))
  have p1i : forall (q0:G), (((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0) = (q0 ◇ ((q0 ◇ q0) ◇ q0)):=by
    intro q0
    exact ((((cg (fun t => ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p0 q0 q0))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (p0 q0 q0))).symm).trans (((cg (fun t => ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (p1h (q0 ◇ q0))).symm).trans (p11 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q0))).symm
  have p1j : forall (q0:G), (((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0
    exact (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (p18 q0 q0))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (p17 q0 q0))).symm).trans (((cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (cg (fun t => ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ q0) ◇ t) (pp q0 ((q0 ◇ q0) ◇ (q0 ◇ q0))))).symm).trans (pq ((q0 ◇ q0) ◇ (q0 ◇ q0)) q0))
  have p1k : forall (q0 q1:G), ((q1 ◇ q1) ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) = q1:=by
    intro q0 q1
    exact (((pf q0 q1 ((q1 ◇ q0) ◇ (q0 ◇ q1))).symm).trans ((((cg (fun t => ((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ t) (p1j ((q1 ◇ q0) ◇ (q0 ◇ q1)))).symm).trans (pg q0 q1 ((q1 ◇ q0) ◇ (q0 ◇ q1)) ((((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1)))) ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) q0 q0 q0)).trans (((cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) (p1f (q0 ◇ q1) (q1 ◇ q0))).trans (cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ ((q0 ◇ q1) ◇ (q1 ◇ q0)))) (p0 q0 q1)))).trans (cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) (cg (fun t => q1 ◇ t) (p0 q0 q1)))))).symm
  have p1l : forall (q0 q1:G), ((q1 ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ q1))) ◇ q1) = q1:=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ q1))) ◇ t) (p0 q1 q1)).symm).trans ((((cg (fun t => t ◇ ((q1 ◇ q1) ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1)))) (cg (fun t => t ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ q1))) (p1k q0 q1))).symm).trans (po ((q1 ◇ q0) ◇ (q0 ◇ q1)) (q1 ◇ q1))).trans (p0 q1 q1))
  have p1m : forall (q0 q1:G), (q1 ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ q1))) = (q1 ◇ ((q1 ◇ q1) ◇ q1)):=by
    intro q0 q1
    exact (((p1i q1).symm).trans (((cg (fun t => ((q1 ◇ (q1 ◇ q1)) ◇ q1) ◇ t) (p1l q0 q1)).symm).trans (py q1 (q1 ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ q1)))))).symm
  have p1n : forall (q0 q1:G), (q1 ◇ (q1 ◇ ((q1 ◇ q1) ◇ q1))) = ((q1 ◇ q0) ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact (((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ q1))) (p1k q0 q1))).trans (cg (fun t => q1 ◇ t) (p1m q0 q1))).symm).trans (((cg (fun t => t ◇ (((q1 ◇ q1) ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) ◇ (((q1 ◇ q0) ◇ (q0 ◇ q1)) ◇ (q1 ◇ q1)))) (p1k q0 q1)).symm).trans (p0 (q1 ◇ q1) ((q1 ◇ q0) ◇ (q0 ◇ q1))))
  have p1o : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ (q1 ◇ q2)) = ((q2 ◇ q0) ◇ (q0 ◇ q2)):=by
    intro q0 q1 q2
    exact (((p1n q0 q2).symm).trans (p1n q1 q2)).symm
  have p1p : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ ((q1 ◇ q0) ◇ (q0 ◇ q1))) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => (q1 ◇ q2) ◇ t) (p1o q0 q2 q1)).symm).trans (p0 q1 q2)
  have p1q : forall (q0 q1 q2:G), (((q0 ◇ (q0 ◇ q1)) ◇ q2) ◇ (q1 ◇ q0)) = q2:=by
    intro q0 q1 q2
    exact ((cg (fun t => ((q0 ◇ (q0 ◇ q1)) ◇ q2) ◇ t) (p1e q0 q1)).symm).trans (((cg (fun t => ((q0 ◇ (q0 ◇ q1)) ◇ q2) ◇ t) (cg (fun t => ((q0 ◇ (q0 ◇ q1)) ◇ (q1 ◇ q0)) ◇ t) (p1a q0 q1))).symm).trans (p1p (q1 ◇ q0) (q0 ◇ (q0 ◇ q1)) q2))
  exact (calc
    x = x:=rfl
    _ = (((x ◇ (x ◇ y)) ◇ x) ◇ (y ◇ x)):=(p1q x y x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6718_to_27515 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6718_to_27515
