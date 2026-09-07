-- Equation4904 → Equation55252
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (x ◇ (x ◇ (z ◇ x))))
-- Conclusion: x ◇ (y ◇ z) = x ◇ ((w ◇ z) ◇ z)
-- Original submission SHA-256: 9e2be0d91db9ff4079b9818d8ce8916dcaff0761229f3cfc5951c1b106693565
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (x ◇ (x ◇ (z ◇ x))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = x ◇ ((w ◇ z) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  have aux : forall (q32 q33 q34:G), (q34 ◇ q32) = (q33 ◇ q32):=by
    have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
      intro f a b p
      exact congrArg f p
    have apc1 : forall (q0 q1 q2:G), (q1 ◇ ((q2 ◇ (q2 ◇ (q0 ◇ q2))) ◇ ((q2 ◇ (q2 ◇ (q0 ◇ q2))) ◇ q2))) = (q2 ◇ (q2 ◇ (q0 ◇ q2))):=by
      intro q0 q1 q2
      exact ((cg (fun t => q1 ◇ t) (cg (fun t => (q2 ◇ (q2 ◇ (q0 ◇ q2))) ◇ t) (cg (fun t => (q2 ◇ (q2 ◇ (q0 ◇ q2))) ◇ t) ((h q2 (q2 ◇ (q2 ◇ (q0 ◇ q2))) q0).symm)))).symm).trans ((h (q2 ◇ (q2 ◇ (q0 ◇ q2))) q1 q2).symm)
    have apc3 : forall (q3 q0 q1:G), (q1 ◇ ((q3 ◇ (q3 ◇ (q3 ◇ (q0 ◇ q3)))) ◇ ((q3 ◇ (q3 ◇ (q3 ◇ (q0 ◇ q3)))) ◇ ((q3 ◇ (q3 ◇ (q3 ◇ (q0 ◇ q3)))) ◇ q3)))) = (q3 ◇ (q3 ◇ (q3 ◇ (q0 ◇ q3)))):=by
      intro q3 q0 q1
      exact ((cg (fun t => q1 ◇ t) (cg (fun t => (q3 ◇ (q3 ◇ (q3 ◇ (q0 ◇ q3)))) ◇ t) (cg (fun t => (q3 ◇ (q3 ◇ (q3 ◇ (q0 ◇ q3)))) ◇ t) (cg (fun t => (q3 ◇ (q3 ◇ (q3 ◇ (q0 ◇ q3)))) ◇ t) ((h q3 q3 q0).symm))))).symm).trans ((h (q3 ◇ (q3 ◇ (q3 ◇ (q0 ◇ q3)))) q1 q3).symm)
    have apc5 : forall (q4 q5 q6 q7:G), (q7 ◇ (((q4 ◇ (q4 ◇ (q4 ◇ (q5 ◇ q4)))) ◇ ((q4 ◇ (q4 ◇ (q4 ◇ (q5 ◇ q4)))) ◇ (q6 ◇ (q4 ◇ (q4 ◇ (q4 ◇ (q5 ◇ q4))))))) ◇ q4)) = ((q4 ◇ (q4 ◇ (q4 ◇ (q5 ◇ q4)))) ◇ ((q4 ◇ (q4 ◇ (q4 ◇ (q5 ◇ q4)))) ◇ (q6 ◇ (q4 ◇ (q4 ◇ (q4 ◇ (q5 ◇ q4))))))):=by
      intro q4 q5 q6 q7
      exact ((cg (fun t => q7 ◇ t) (cg (fun t => ((q4 ◇ (q4 ◇ (q4 ◇ (q5 ◇ q4)))) ◇ ((q4 ◇ (q4 ◇ (q4 ◇ (q5 ◇ q4)))) ◇ (q6 ◇ (q4 ◇ (q4 ◇ (q4 ◇ (q5 ◇ q4))))))) ◇ t) ((h q4 ((q4 ◇ (q4 ◇ (q4 ◇ (q5 ◇ q4)))) ◇ ((q4 ◇ (q4 ◇ (q4 ◇ (q5 ◇ q4)))) ◇ (q6 ◇ (q4 ◇ (q4 ◇ (q4 ◇ (q5 ◇ q4))))))) q5).symm))).symm).trans (apc1 q6 q7 (q4 ◇ (q4 ◇ (q4 ◇ (q5 ◇ q4)))))
    have apc6 : forall (q8 q9 q10 q11:G), ((q8 ◇ (q8 ◇ (q8 ◇ (q9 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q9 ◇ q8)))) ◇ (q10 ◇ (q8 ◇ (q8 ◇ (q8 ◇ (q9 ◇ q8))))))) = (q11 ◇ (((q8 ◇ (q8 ◇ (q8 ◇ (q9 ◇ q8)))) ◇ ((q8 ◇ (q8 ◇ (q8 ◇ (q9 ◇ q8)))) ◇ q8)) ◇ q8)):=by
      intro q8 q9 q10 q11
      exact (((cg (fun t => q11 ◇ t) (cg (fun t => t ◇ q8) (cg (fun t => (q8 ◇ (q8 ◇ (q8 ◇ (q9 ◇ q8)))) ◇ t) (cg (fun t => (q8 ◇ (q8 ◇ (q8 ◇ (q9 ◇ q8)))) ◇ t) ((h q8 q10 q9).symm))))).symm).trans (apc5 q8 q9 q10 q11)).symm
    have apc7 : forall (q12 q13 q14 q15:G), ((q13 ◇ (q13 ◇ (q13 ◇ (q14 ◇ q13)))) ◇ ((q13 ◇ (q13 ◇ (q13 ◇ (q14 ◇ q13)))) ◇ (q15 ◇ (q13 ◇ (q13 ◇ (q13 ◇ (q14 ◇ q13))))))) = ((q13 ◇ (q13 ◇ (q13 ◇ (q14 ◇ q13)))) ◇ ((q13 ◇ (q13 ◇ (q13 ◇ (q14 ◇ q13)))) ◇ (q12 ◇ (q13 ◇ (q13 ◇ (q13 ◇ (q14 ◇ q13))))))):=by
      intro q12 q13 q14 q15
      exact ((apc6 q13 q14 q12 q12).trans ((apc6 q13 q14 q15 q12).symm)).symm
    have apc8 : forall (q16 q17 q18:G), ((q17 ◇ (q17 ◇ (q17 ◇ (q18 ◇ q17)))) ◇ ((q17 ◇ (q17 ◇ (q17 ◇ (q18 ◇ q17)))) ◇ (q16 ◇ (q17 ◇ (q17 ◇ (q17 ◇ (q18 ◇ q17))))))) = ((q17 ◇ (q17 ◇ (q17 ◇ (q18 ◇ q17)))) ◇ ((q17 ◇ (q17 ◇ (q17 ◇ (q18 ◇ q17)))) ◇ q17)):=by
      intro q16 q17 q18
      exact (((cg (fun t => (q17 ◇ (q17 ◇ (q17 ◇ (q18 ◇ q17)))) ◇ t) (cg (fun t => (q17 ◇ (q17 ◇ (q17 ◇ (q18 ◇ q17)))) ◇ t) ((h q17 q16 q18).symm))).symm).trans (apc7 q16 q17 q18 q16)).symm
    have apc13 : forall (q19 q20 q21 q22:G), (q22 ◇ ((q19 ◇ (q19 ◇ (q19 ◇ (q20 ◇ q19)))) ◇ (q21 ◇ (((q19 ◇ (q19 ◇ (q19 ◇ (q20 ◇ q19)))) ◇ ((q19 ◇ (q19 ◇ (q19 ◇ (q20 ◇ q19)))) ◇ q19)) ◇ q19)))) = (q19 ◇ (q19 ◇ (q19 ◇ (q20 ◇ q19)))):=by
      intro q19 q20 q21 q22
      exact ((cg (fun t => q22 ◇ t) (cg (fun t => (q19 ◇ (q19 ◇ (q19 ◇ (q20 ◇ q19)))) ◇ t) (apc6 q19 q20 q19 q21))).symm).trans ((h (q19 ◇ (q19 ◇ (q19 ◇ (q20 ◇ q19)))) q22 q19).symm)
    have apc15 : forall (q23 q24 q25 q26 q27:G), (q27 ◇ (((q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ ((q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ ((q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ q23))) ◇ (q26 ◇ q23))) = ((q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ ((q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ ((q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ q23))):=by
      intro q23 q24 q25 q26 q27
      exact ((cg (fun t => q27 ◇ t) (cg (fun t => t ◇ (q26 ◇ q23)) (cg (fun t => (q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ t) (apc8 q25 q23 q24)))).symm).trans ((((cg (fun t => q27 ◇ t) (cg (fun t => ((q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ ((q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ ((q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ (q25 ◇ (q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))))))) ◇ t) (cg (fun t => q26 ◇ t) ((h q23 (((q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ ((q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ ((q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ (q25 ◇ (q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))))))) ◇ (((q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ ((q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ ((q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ (q25 ◇ (q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))))))) ◇ (q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))))) q24).symm)))).symm).trans (apc13 (q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) q25 q26 q27)).trans (cg (fun t => (q23 ◇ (q23 ◇ (q23 ◇ (q24 ◇ q23)))) ◇ t) (apc8 q25 q23 q24)))
    have apc17 : forall (q28 q29 q30 q31:G), (q31 ◇ ((q30 ◇ q28) ◇ (q28 ◇ (q28 ◇ (q28 ◇ (q29 ◇ q28)))))) = (q30 ◇ q28):=by
      intro q28 q29 q30 q31
      exact ((cg (fun t => q31 ◇ t) (cg (fun t => (q30 ◇ q28) ◇ t) (apc3 q28 q29 (q30 ◇ q28)))).symm).trans (((cg (fun t => q31 ◇ t) (cg (fun t => (q30 ◇ q28) ◇ t) (cg (fun t => (q30 ◇ q28) ◇ t) (apc15 q28 q29 q28 q30 (q30 ◇ q28))))).symm).trans ((h (q30 ◇ q28) q31 ((q28 ◇ (q28 ◇ (q28 ◇ (q29 ◇ q28)))) ◇ ((q28 ◇ (q28 ◇ (q28 ◇ (q29 ◇ q28)))) ◇ ((q28 ◇ (q28 ◇ (q28 ◇ (q29 ◇ q28)))) ◇ q28)))).symm))
    have apc18 : forall (q32 q33 q34:G), (q34 ◇ q32) = (q33 ◇ q32):=by
      intro q32 q33 q34
      exact ((cg (fun t => q34 ◇ t) ((h q32 (q33 ◇ q32) q32).symm)).symm).trans (apc17 q32 q32 q33 q34)
    exact apc18
  intro x y z w
  exact (aux (y ◇ z) x x).trans (congrArg (fun t => Magma.op x t) ((aux z (w ◇ z) y).trans (congrArg (fun t => Magma.op (w ◇ z) t) (rfl))))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4904_to_55252 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4904_to_55252
