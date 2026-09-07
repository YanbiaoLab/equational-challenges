-- Equation40154 → Equation53775
-- Recorded verdict: true
-- Premise: x = (((y * (y * x)) * z) * y) * y
-- Conclusion: x * y = (((z * w) * u) * x) * v
-- Original submission SHA-256: ff8d40c42dc81ec5c164bd03b4641487fd3c52ec56f2ae0a5c25bd3e99fb349d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (((y ◇ (y ◇ x)) ◇ z) ◇ y) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = (((z ◇ w) ◇ u) ◇ x) ◇ v
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have cg : ∀ (f : G → G) {a b : G}, a = b → f a = f b := by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z : G), ((((y ◇ (y ◇ x)) ◇ z) ◇ y) ◇ y) = ((((x ◇ (x ◇ x)) ◇ x) ◇ x) ◇ x) := by
    intro x y z
    exact ((rfl).symm).trans (((h x y z).symm.trans (h x x x)).trans (rfl))
  have apc1 : forall (q0 : G), ((((q0 ◇ (q0 ◇ q0)) ◇ q0) ◇ q0) ◇ q0) = q0 := by
    intro q0
    exact ((rfl).symm).trans ((((apc0 q0 q0 q0).symm).trans ((h q0 q0 q0).symm)).trans (rfl))
  have apc3 : forall (q1 q2 q3 q4 : G), (((((((q3 ◇ (q3 ◇ q1)) ◇ q2) ◇ q3) ◇ q1) ◇ q4) ◇ (((q3 ◇ (q3 ◇ q1)) ◇ q2) ◇ q3)) ◇ (((q3 ◇ (q3 ◇ q1)) ◇ q2) ◇ q3)) = q3 := by
    intro q1 q2 q3 q4
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (((q3 ◇ (q3 ◇ q1)) ◇ q2) ◇ q3)) (cg (fun t => t ◇ (((q3 ◇ (q3 ◇ q1)) ◇ q2) ◇ q3)) (cg (fun t => t ◇ q4) (cg (fun t => (((q3 ◇ (q3 ◇ q1)) ◇ q2) ◇ q3) ◇ t) ((h q1 q3 q2).symm))))).symm).trans ((h q3 (((q3 ◇ (q3 ◇ q1)) ◇ q2) ◇ q3) q4).symm)).trans (rfl))
  have apc4 : forall (q5 q6 q7 : G), (((q5 ◇ q7) ◇ (((q5 ◇ (q5 ◇ q5)) ◇ q6) ◇ q5)) ◇ (((q5 ◇ (q5 ◇ q5)) ◇ q6) ◇ q5)) = q5 := by
    intro q5 q6 q7
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (((q5 ◇ (q5 ◇ q5)) ◇ q6) ◇ q5)) (cg (fun t => t ◇ (((q5 ◇ (q5 ◇ q5)) ◇ q6) ◇ q5)) (cg (fun t => t ◇ q7) ((h q5 q5 q6).symm)))).symm).trans (apc3 q5 q6 q5 q7)).trans (rfl))
  have apc5 : forall (q8 q9 q10 : G), ((((((q8 ◇ q9) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8)) ◇ q8) ◇ q10) ◇ ((q8 ◇ q9) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8))) ◇ ((q8 ◇ q9) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8))) = (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) := by
    intro q8 q9 q10
    exact ((((((cg (fun t => t ◇ ((((((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) ◇ ((((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) ◇ q8)) ◇ q9) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8))) (cg (fun t => t ◇ ((((((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) ◇ ((((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) ◇ q8)) ◇ q9) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8))) (cg (fun t => t ◇ q10) (cg (fun t => t ◇ q8) (cg (fun t => t ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8)) (cg (fun t => t ◇ q9) (apc1 q8))))))).trans (cg (fun t => t ◇ ((((((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) ◇ ((((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) ◇ q8)) ◇ q9) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8))) (cg (fun t => ((((q8 ◇ q9) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8)) ◇ q8) ◇ q10) ◇ t) (cg (fun t => t ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8)) (cg (fun t => t ◇ q9) (cg (fun t => (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) ◇ t) (apc1 q8))))))).trans (cg (fun t => t ◇ ((((((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) ◇ ((((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) ◇ q8)) ◇ q9) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8))) (cg (fun t => ((((q8 ◇ q9) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8)) ◇ q8) ◇ q10) ◇ t) (cg (fun t => t ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8)) (cg (fun t => t ◇ q9) (apc1 q8)))))).trans (cg (fun t => (((((q8 ◇ q9) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8)) ◇ q8) ◇ q10) ◇ ((q8 ◇ q9) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8))) ◇ t) (cg (fun t => t ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8)) (cg (fun t => t ◇ q9) (cg (fun t => (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) ◇ t) (apc1 q8)))))).trans (cg (fun t => (((((q8 ◇ q9) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8)) ◇ q8) ◇ q10) ◇ ((q8 ◇ q9) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8))) ◇ t) (cg (fun t => t ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8)) (cg (fun t => t ◇ q9) (apc1 q8))))).symm).trans ((((cg (fun t => t ◇ ((((((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) ◇ ((((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) ◇ q8)) ◇ q9) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8))) (cg (fun t => t ◇ ((((((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) ◇ ((((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) ◇ q8)) ◇ q9) ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8))) (cg (fun t => t ◇ q10) (cg (fun t => t ◇ q8) (cg (fun t => t ◇ (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8)) (cg (fun t => t ◇ q9) (cg (fun t => (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) ◇ t) (apc1 q8)))))))).symm).trans (apc3 q8 q9 (((q8 ◇ (q8 ◇ q8)) ◇ q8) ◇ q8) q10)).trans (rfl))
  have apc6 : forall (q11 q12 : G), ((q11 ◇ ((q12 ◇ (q12 ◇ q11)) ◇ (((q12 ◇ (q12 ◇ q12)) ◇ q12) ◇ q12))) ◇ ((q12 ◇ (q12 ◇ q11)) ◇ (((q12 ◇ (q12 ◇ q12)) ◇ q12) ◇ q12))) = (((q12 ◇ (q12 ◇ q12)) ◇ q12) ◇ q12) := by
    intro q11 q12
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ ((q12 ◇ (q12 ◇ q11)) ◇ (((q12 ◇ (q12 ◇ q12)) ◇ q12) ◇ q12))) (cg (fun t => t ◇ ((q12 ◇ (q12 ◇ q11)) ◇ (((q12 ◇ (q12 ◇ q12)) ◇ q12) ◇ q12))) ((h q11 q12 (((q12 ◇ (q12 ◇ q12)) ◇ q12) ◇ q12)).symm))).symm).trans (apc5 q12 (q12 ◇ q11) q12)).trans (rfl))
  have apc11 : forall (q13 q14 q15 : G), (((((q13 ◇ ((q14 ◇ (q14 ◇ q13)) ◇ (((q14 ◇ (q14 ◇ q14)) ◇ q14) ◇ q14))) ◇ (((q14 ◇ (q14 ◇ q14)) ◇ q14) ◇ q14)) ◇ q15) ◇ (q13 ◇ ((q14 ◇ (q14 ◇ q13)) ◇ (((q14 ◇ (q14 ◇ q14)) ◇ q14) ◇ q14)))) ◇ (q13 ◇ ((q14 ◇ (q14 ◇ q13)) ◇ (((q14 ◇ (q14 ◇ q14)) ◇ q14) ◇ q14)))) = ((q14 ◇ (q14 ◇ q13)) ◇ (((q14 ◇ (q14 ◇ q14)) ◇ q14) ◇ q14)) := by
    intro q13 q14 q15
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q13 ◇ ((q14 ◇ (q14 ◇ q13)) ◇ (((q14 ◇ (q14 ◇ q14)) ◇ q14) ◇ q14)))) (cg (fun t => t ◇ (q13 ◇ ((q14 ◇ (q14 ◇ q13)) ◇ (((q14 ◇ (q14 ◇ q14)) ◇ q14) ◇ q14)))) (cg (fun t => t ◇ q15) (cg (fun t => (q13 ◇ ((q14 ◇ (q14 ◇ q13)) ◇ (((q14 ◇ (q14 ◇ q14)) ◇ q14) ◇ q14))) ◇ t) (apc6 q13 q14))))).symm).trans ((h ((q14 ◇ (q14 ◇ q13)) ◇ (((q14 ◇ (q14 ◇ q14)) ◇ q14) ◇ q14)) (q13 ◇ ((q14 ◇ (q14 ◇ q13)) ◇ (((q14 ◇ (q14 ◇ q14)) ◇ q14) ◇ q14))) q15).symm)).trans (rfl))
  have apc12 : forall (q16 : G), ((q16 ◇ (q16 ◇ ((q16 ◇ (q16 ◇ q16)) ◇ (((q16 ◇ (q16 ◇ q16)) ◇ q16) ◇ q16)))) ◇ (q16 ◇ ((q16 ◇ (q16 ◇ q16)) ◇ (((q16 ◇ (q16 ◇ q16)) ◇ q16) ◇ q16)))) = ((q16 ◇ (q16 ◇ q16)) ◇ (((q16 ◇ (q16 ◇ q16)) ◇ q16) ◇ q16)) := by
    intro q16
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ (q16 ◇ ((q16 ◇ (q16 ◇ q16)) ◇ (((q16 ◇ (q16 ◇ q16)) ◇ q16) ◇ q16)))) (cg (fun t => t ◇ (q16 ◇ ((q16 ◇ (q16 ◇ q16)) ◇ (((q16 ◇ (q16 ◇ q16)) ◇ q16) ◇ q16)))) (apc4 q16 q16 ((q16 ◇ (q16 ◇ q16)) ◇ (((q16 ◇ (q16 ◇ q16)) ◇ q16) ◇ q16))))).symm).trans (apc11 q16 q16 (((q16 ◇ (q16 ◇ q16)) ◇ q16) ◇ q16))).trans (rfl))
  have apc13 : forall (q17 : G), ((((q17 ◇ (q17 ◇ q17)) ◇ (((q17 ◇ (q17 ◇ q17)) ◇ q17) ◇ q17)) ◇ q17) ◇ q17) = ((q17 ◇ (q17 ◇ q17)) ◇ (((q17 ◇ (q17 ◇ q17)) ◇ q17) ◇ q17)) := by
    intro q17
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q17) (cg (fun t => t ◇ q17) (apc12 q17))).symm).trans ((h ((q17 ◇ (q17 ◇ q17)) ◇ (((q17 ◇ (q17 ◇ q17)) ◇ q17) ◇ q17)) q17 (q17 ◇ ((q17 ◇ (q17 ◇ q17)) ◇ (((q17 ◇ (q17 ◇ q17)) ◇ q17) ◇ q17)))).symm)).trans (rfl))
  have apc15 : forall (q18 : G), ((q18 ◇ (q18 ◇ q18)) ◇ (((q18 ◇ (q18 ◇ q18)) ◇ q18) ◇ q18)) = q18 := by
    intro q18
    exact ((rfl).symm).trans ((((apc13 q18).symm).trans ((h q18 q18 (((q18 ◇ (q18 ◇ q18)) ◇ q18) ◇ q18)).symm)).trans (rfl))
  have apc16 : forall (q19 q20 : G), (((q19 ◇ q20) ◇ (q19 ◇ q19)) ◇ (q19 ◇ q19)) = q19 := by
    intro q19 q20
    exact ((cg (fun t => ((q19 ◇ q20) ◇ (q19 ◇ q19)) ◇ t) (cg (fun t => t ◇ q19) (apc15 q19))).symm).trans ((((cg (fun t => t ◇ (((q19 ◇ (q19 ◇ q19)) ◇ (((q19 ◇ (q19 ◇ q19)) ◇ q19) ◇ q19)) ◇ q19)) (cg (fun t => (q19 ◇ q20) ◇ t) (cg (fun t => t ◇ q19) (apc15 q19)))).symm).trans (apc4 q19 (((q19 ◇ (q19 ◇ q19)) ◇ q19) ◇ q19) q20)).trans (rfl))
  have apc17 : forall (q17 q18 : G), ((q17 ◇ q17) ◇ q17) = q17 := by
    intro q17 q18
    exact ((rfl).symm).trans ((((cg (fun t => t ◇ q17) (cg (fun t => t ◇ q17) (apc15 q17))).symm).trans ((apc13 q17).trans (apc15 q17))).trans (rfl))
  have apc18 : forall (q21 : G), (q21 ◇ q21) = q21 := by
    intro q21
    exact ((rfl).symm).trans ((((apc17 (q21 ◇ q21) q21).symm).trans (apc16 q21 q21)).trans (rfl))
  have apc19 : forall (q22 q23 : G), (((q22 ◇ q23) ◇ q22) ◇ q22) = q22 := by
    intro q22 q23
    exact ((cg (fun t => t ◇ q22) (cg (fun t => t ◇ q22) (cg (fun t => t ◇ q23) (apc18 q22)))).symm).trans ((((cg (fun t => t ◇ q22) (cg (fun t => t ◇ q22) (cg (fun t => t ◇ q23) (cg (fun t => q22 ◇ t) (apc18 q22))))).symm).trans ((h q22 q22 q23).symm)).trans (rfl))
  have apc21 : forall (q24 q25 : G), q25 = q24 := by
    intro q24 q25
    exact ((apc18 q25).symm).trans ((((cg (fun t => t ◇ q25) (apc19 q25 (q25 ◇ q24))).symm).trans ((h q24 q25 q25).symm)).trans (rfl))
  exact (apc21 (x ◇ y) (x ◇ y)).trans ((apc21 (x ◇ y) ((((z ◇ w) ◇ u) ◇ x) ◇ v)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_40154_to_53775 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_40154_to_53775
