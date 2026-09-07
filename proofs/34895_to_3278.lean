-- Equation34895 → Equation3278
-- Recorded verdict: true
-- Premise: x = ((y ◇ y) ◇ ((x ◇ z) ◇ z)) ◇ x
-- Conclusion: x ◇ x = y ◇ (y ◇ (x ◇ x))
-- Original submission SHA-256: 18dfb167e7efb311b12bde6262a342b8cabd9ed2a09838a67e4e0122b834a6ce
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ ((x ◇ z) ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = y ◇ (y ◇ (x ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q0 q1 q2 q3:G), (((q2 ◇ q2) ◇ (q3 ◇ q3)) ◇ ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1))) = ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1))) (cg (fun t => (q2 ◇ q2) ◇ t) (cg (fun t => t ◇ q3) ((h q3 q0 q1).symm)))).symm).trans ((h ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1)) q2 q3).symm)
  have p1 : forall (q0 q1:G), (((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)) = ((q1 ◇ q0) ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ ((q1 ◇ q0) ◇ q0)) (p0 ((q1 ◇ q0) ◇ q0) q0 q1 q1)).symm).trans ((h ((q1 ◇ q0) ◇ q0) (q1 ◇ q1) ((q1 ◇ q0) ◇ q0)).symm)
  have p2 : forall (q0 q1 q2:G), (((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q0)) ◇ (((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0))) = (((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0))) (cg (fun t => (q2 ◇ q2) ◇ t) (p1 q0 q1))).symm).trans ((h (((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) q2 ((q1 ◇ q0) ◇ q0)).symm)
  have p3 : forall (q6 q7 q8 q9 q10:G), (((q9 ◇ q9) ◇ ((q6 ◇ q10) ◇ q10)) ◇ (((q7 ◇ q7) ◇ ((q6 ◇ q8) ◇ q8)) ◇ q6)) = (((q7 ◇ q7) ◇ ((q6 ◇ q8) ◇ q8)) ◇ q6):=by
    intro q6 q7 q8 q9 q10
    exact ((cg (fun t => t ◇ (((q7 ◇ q7) ◇ ((q6 ◇ q8) ◇ q8)) ◇ q6)) (cg (fun t => (q9 ◇ q9) ◇ t) (cg (fun t => t ◇ q10) (cg (fun t => t ◇ q10) ((h q6 q7 q8).symm))))).symm).trans ((h (((q7 ◇ q7) ◇ ((q6 ◇ q8) ◇ q8)) ◇ q6) q9 q10).symm)
  have p4 : forall (q0 q1 q2 q3 q4:G), (((q3 ◇ q3) ◇ ((q0 ◇ q4) ◇ q4)) ◇ q0) = (((q1 ◇ q1) ◇ ((q0 ◇ q2) ◇ q2)) ◇ q0):=by
    intro q0 q1 q2 q3 q4
    exact ((cg (fun t => ((q3 ◇ q3) ◇ ((q0 ◇ q4) ◇ q4)) ◇ t) ((h q0 q1 q2).symm)).symm).trans (p3 q0 q1 q2 q3 q4)
  have p5 : forall (q0 q1 q2 q3 q4:G), (((q4 ◇ q4) ◇ (((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1)) ◇ ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1)))) ◇ ((q2 ◇ q2) ◇ (q3 ◇ q3))) = ((q2 ◇ q2) ◇ (q3 ◇ q3)):=by
    intro q0 q1 q2 q3 q4
    exact ((cg (fun t => t ◇ ((q2 ◇ q2) ◇ (q3 ◇ q3))) (cg (fun t => (q4 ◇ q4) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1))) (p0 q0 q1 q2 q3)))).symm).trans ((h ((q2 ◇ q2) ◇ (q3 ◇ q3)) q4 ((q0 ◇ q0) ◇ ((q3 ◇ q1) ◇ q1))).symm)
  have p6 : forall (q0:G), ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => t ◇ (q0 ◇ q0)) (p5 q0 q0 (q0 ◇ q0) q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))).symm).trans ((h (q0 ◇ q0) (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (q0 ◇ q0)).symm)
  have p7 : forall (q0 q1:G), (((q1 ◇ q1) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (cg (fun t => (q1 ◇ q1) ◇ t) (p6 q0))).symm).trans ((h ((q0 ◇ q0) ◇ (q0 ◇ q0)) q1 (q0 ◇ q0)).symm)
  have p8 : forall (q0 q1 q2:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q1 ◇ q1) ◇ (((q0 ◇ q0) ◇ q2) ◇ q2))) = ((q1 ◇ q1) ◇ (((q0 ◇ q0) ◇ q2) ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ ((q1 ◇ q1) ◇ (((q0 ◇ q0) ◇ q2) ◇ q2))) (p5 q0 q0 q0 q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))).symm).trans (p0 q1 q2 (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0))) (q0 ◇ q0))
  have p9 : forall (q0 q1 q2:G), (((q2 ◇ q2) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ ((q1 ◇ q1) ◇ (q0 ◇ q0))) = ((q1 ◇ q1) ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ ((q1 ◇ q1) ◇ (q0 ◇ q0))) (cg (fun t => (q2 ◇ q2) ◇ t) (p7 q0 q0))).symm).trans (((cg (fun t => t ◇ ((q1 ◇ q1) ◇ (q0 ◇ q0))) (cg (fun t => (q2 ◇ q2) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (p7 q0 q1)))).symm).trans ((h ((q1 ◇ q1) ◇ (q0 ◇ q0)) q2 ((q0 ◇ q0) ◇ (q0 ◇ q0))).symm))
  have pa : forall (q0 q1 q2:G), (((q2 ◇ q2) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => (q2 ◇ q2) ◇ t) (p9 q0 q0 q1))).symm).trans ((h (q1 ◇ q1) q2 ((q0 ◇ q0) ◇ (q0 ◇ q0))).symm)
  have pb : forall (q0 q1:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ q1)) (pa q0 (q0 ◇ q0) (q0 ◇ q0))).symm).trans (pa q0 q1 ((q0 ◇ q0) ◇ (q0 ◇ q0)))
  have pc : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q0 ◇ q0)) (pb q0 q0)).symm).trans (p6 q0)
  have pd : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ q1)) (pc q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)))).symm).trans (pb q0 q1)
  have pe : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ ((q0 ◇ q0) ◇ ((q2 ◇ q1) ◇ q1))) = ((q0 ◇ q0) ◇ ((q2 ◇ q1) ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q2 ◇ q1) ◇ q1))) (pa q0 q2 (q0 ◇ q0))).symm).trans (p0 q0 q1 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q2)
  have pf : forall (q0 q1 q2:G), ((q0 ◇ q0) ◇ ((q1 ◇ q1) ◇ (((q0 ◇ q0) ◇ q2) ◇ q2))) = ((q1 ◇ q1) ◇ (((q0 ◇ q0) ◇ q2) ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ ((q1 ◇ q1) ◇ (((q0 ◇ q0) ◇ q2) ◇ q2))) (pc q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)))).symm).trans (p8 q0 q1 q2)
  have pg : forall (q0 q1 q2 q3:G), (((q2 ◇ q2) ◇ ((((q1 ◇ q0) ◇ q0) ◇ q3) ◇ q3)) ◇ ((q1 ◇ q0) ◇ q0)) = ((q1 ◇ q0) ◇ q0):=by
    intro q0 q1 q2 q3
    exact (((p1 q0 q1).symm).trans (((cg (fun t => t ◇ ((q1 ◇ q0) ◇ q0)) (p0 ((q1 ◇ q0) ◇ q0) q0 q1 q1)).symm).trans (p4 ((q1 ◇ q0) ◇ q0) q2 q3 (q1 ◇ q1) ((q1 ◇ q0) ◇ q0)))).symm
  have ph : forall (q11 q12 q13 q14 q15 q16:G), (((q15 ◇ q15) ◇ ((((q11 ◇ q14) ◇ q14) ◇ q16) ◇ q16)) ◇ (((((q12 ◇ q12) ◇ ((q11 ◇ q13) ◇ q13)) ◇ q11) ◇ q14) ◇ q14)) = (((((q12 ◇ q12) ◇ ((q11 ◇ q13) ◇ q13)) ◇ q11) ◇ q14) ◇ q14):=by
    intro q11 q12 q13 q14 q15 q16
    exact ((cg (fun t => t ◇ (((((q12 ◇ q12) ◇ ((q11 ◇ q13) ◇ q13)) ◇ q11) ◇ q14) ◇ q14)) (cg (fun t => (q15 ◇ q15) ◇ t) (cg (fun t => t ◇ q16) (cg (fun t => t ◇ q16) (cg (fun t => t ◇ q14) (cg (fun t => t ◇ q14) ((h q11 q12 q13).symm))))))).symm).trans (pg q14 (((q12 ◇ q12) ◇ ((q11 ◇ q13) ◇ q13)) ◇ q11) q15 q16)
  have pi : forall (q0 q1 q2 q3 q4 q5:G), (((((q1 ◇ q1) ◇ ((q0 ◇ q2) ◇ q2)) ◇ q0) ◇ q3) ◇ q3) = ((q0 ◇ q3) ◇ q3):=by
    intro q0 q1 q2 q3 q4 q5
    exact (((pg q3 q0 q4 q5).symm).trans (((cg (fun t => ((q4 ◇ q4) ◇ ((((q0 ◇ q3) ◇ q3) ◇ q5) ◇ q5)) ◇ t) (cg (fun t => t ◇ q3) (cg (fun t => t ◇ q3) ((h q0 q1 q2).symm)))).symm).trans (ph q0 q1 q2 q3 q4 q5))).symm
  have pj : forall (q0 q1 q2 q3 q4:G), (((q3 ◇ q3) ◇ (((q0 ◇ q4) ◇ q4) ◇ q4)) ◇ ((((q1 ◇ q1) ◇ ((q0 ◇ q2) ◇ q2)) ◇ q0) ◇ q4)) = ((((q1 ◇ q1) ◇ ((q0 ◇ q2) ◇ q2)) ◇ q0) ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((cg (fun t => t ◇ ((((q1 ◇ q1) ◇ ((q0 ◇ q2) ◇ q2)) ◇ q0) ◇ q4)) (cg (fun t => (q3 ◇ q3) ◇ t) (cg (fun t => t ◇ q4) (pi q0 q1 q2 q4 q0 q0)))).symm).trans ((h ((((q1 ◇ q1) ◇ ((q0 ◇ q2) ◇ q2)) ◇ q0) ◇ q4) q3 q4).symm)
  have pk : forall (q0 q1 q2 q3 q4:G), (((q3 ◇ q3) ◇ (((q0 ◇ q4) ◇ q4) ◇ q4)) ◇ (q0 ◇ q4)) = ((((q1 ◇ q1) ◇ ((q0 ◇ q2) ◇ q2)) ◇ q0) ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((cg (fun t => ((q3 ◇ q3) ◇ (((q0 ◇ q4) ◇ q4) ◇ q4)) ◇ t) (cg (fun t => t ◇ q4) ((h q0 q1 q2).symm))).symm).trans (pj q0 q1 q2 q3 q4)
  have pl : forall (q0 q1 q2 q3:G), ((((q1 ◇ q1) ◇ ((q0 ◇ q2) ◇ q2)) ◇ q0) ◇ q3) = (q0 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((pk q0 q1 q2 q0 q3).symm).trans ((h (q0 ◇ q3) q0 q3).symm)
  have pm : forall (q17 q18 q19 q20 q21 q22:G), (q20 ◇ (((q18 ◇ q18) ◇ ((q17 ◇ q19) ◇ q19)) ◇ q17)) = (q20 ◇ q17):=by
    intro q17 q18 q19 q20 q21 q22
    exact (((pl q20 q21 q22 q17).symm).trans (((cg (fun t => (((q21 ◇ q21) ◇ ((q20 ◇ q22) ◇ q22)) ◇ q20) ◇ t) ((h q17 q18 q19).symm)).symm).trans (pl q20 q21 q22 (((q18 ◇ q18) ◇ ((q17 ◇ q19) ◇ q19)) ◇ q17)))).symm
  have pn : forall (q0 q1 q2 q3:G), ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q0))) = ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q0)):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => t ◇ ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q0))) (cg (fun t => (q3 ◇ q3) ◇ t) (pd ((q1 ◇ q0) ◇ q0) ((q1 ◇ q0) ◇ q0)))).trans (cg (fun t => t ◇ ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q0))) (pd q3 ((q1 ◇ q0) ◇ q0)))).symm).trans (((cg (fun t => t ◇ ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q0))) (cg (fun t => (q3 ◇ q3) ◇ t) (cg (fun t => t ◇ (((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0))) (p2 q0 q1 q2)))).symm).trans ((h ((q2 ◇ q2) ◇ ((q1 ◇ q0) ◇ q0)) q3 (((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0))).symm))
  have po : forall (q0 q1:G), ((((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0))) ◇ ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0))) = ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => (((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0))) ◇ t) (pe ((q1 ◇ q0) ◇ q0) q0 q1)).symm).trans (pn ((q1 ◇ q0) ◇ q0) ((q1 ◇ q0) ◇ q0) q1 q0)).trans (pe ((q1 ◇ q0) ◇ q0) q0 q1)
  have pp : forall (q0 q1:G), (((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0))) = ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0))) (po q0 q1)).symm).trans (p1 ((q1 ◇ q0) ◇ q0) ((q1 ◇ q0) ◇ q0))
  have pq : forall (q0 q1 q2 q3 q4:G), (q4 ◇ ((((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q2 ◇ q3) ◇ q3)) ◇ q2)) = (q4 ◇ q2):=by
    intro q0 q1 q2 q3 q4
    exact ((cg (fun t => q4 ◇ t) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ ((q2 ◇ q3) ◇ q3)) (pp q0 q1)))).symm).trans (pm q2 ((((q1 ◇ q0) ◇ q0) ◇ ((q1 ◇ q0) ◇ q0)) ◇ ((q1 ◇ q0) ◇ q0)) q3 q4 q0 q0)
  have pr : forall (q0 q1 q2:G), (q2 ◇ (((q0 ◇ q1) ◇ q1) ◇ q0)) = (q2 ◇ q0):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q0) ((h ((q0 ◇ q1) ◇ q1) ((((q0 ◇ q1) ◇ q1) ◇ q0) ◇ q0) q0).symm))).symm).trans (pq q0 ((q0 ◇ q1) ◇ q1) q0 q1 q2)
  have ps : forall (q0 q1 q2:G), (((((q0 ◇ q1) ◇ q1) ◇ q0) ◇ q0) ◇ (q2 ◇ q2)) = (q2 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q2 ◇ q2)) (pr q0 q1 (((q0 ◇ q1) ◇ q1) ◇ q0))).symm).trans (pd (((q0 ◇ q1) ◇ q1) ◇ q0) q2)
  have pt : forall (q0 q1:G), ((q1 ◇ q1) ◇ ((q0 ◇ q0) ◇ q1)) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => (q1 ◇ q1) ◇ t) (pr q1 q1 (q0 ◇ q0))).symm).trans (pf q1 q0 q1)).trans (pr q1 q1 (q0 ◇ q0))
  have pu : forall (q0 q1:G), ((((q0 ◇ q0) ◇ q0) ◇ q0) ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q1) (cg (fun t => t ◇ q0) (pt q0 q0))).symm).trans (pl q0 q0 q0 q1)
  have pv : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q0 ◇ q0))) = (q1 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (pu q0 (q0 ◇ q0))).symm).trans (pr (q0 ◇ q0) q0 q1)
  have pw : forall (q0:G), (((q0 ◇ q0) ◇ q0) ◇ q0) = q0:=by
    intro q0
    exact ((cg (fun t => t ◇ q0) (pt q0 q0)).symm).trans ((h q0 q0 q0).symm)
  have px : forall (q0 q1:G), (((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => t ◇ (q0 ◇ q0)) (pu q0 (q0 ◇ q0)))).symm).trans (ps (q0 ◇ q0) q0 q1)
  have py : forall (q0 q1:G), (q0 ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1
    exact (((((cg (fun t => t ◇ (q0 ◇ (q0 ◇ q0))) (pd q1 q0)).trans (pv q0 (q0 ◇ q0))).trans (pd q0 q0)).symm).trans (((cg (fun t => t ◇ (q0 ◇ (q0 ◇ q0))) (cg (fun t => (q1 ◇ q1) ◇ t) (px q0 q0))).symm).trans ((h (q0 ◇ (q0 ◇ q0)) q1 (q0 ◇ q0)).symm))).symm
  have pz : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q0) ◇ q0)) = (q1 ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q0) (pd q0 q0))).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q0) (cg (fun t => t ◇ (q0 ◇ q0)) (py q0 q0)))).symm).trans (pr q0 (q0 ◇ q0) q1))
  have p10 : forall (q0 q1:G), (q0 ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ q1)) (pw q0)).symm).trans (((cg (fun t => t ◇ (q1 ◇ q1)) (pz q0 ((q0 ◇ q0) ◇ q0))).symm).trans (pd ((q0 ◇ q0) ◇ q0) q1))
  exact (calc
    (x ◇ x) = (x ◇ x):=rfl
    _ = (y ◇ (y ◇ (x ◇ x))):=((cg (fun t => y ◇ t) (p10 y x)).trans (p10 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_34895_to_3278 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_34895_to_3278
