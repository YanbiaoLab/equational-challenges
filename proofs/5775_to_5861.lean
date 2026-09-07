-- Equation5775 → Equation5861
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))
-- Conclusion: x = y ◇ (x ◇ (z ◇ ((x ◇ w) ◇ x)))
-- Original submission SHA-256: f86ff9b8e22be152a6b6279606b896e6e171c475e330d5f65104edea07d9519c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (x ◇ (z ◇ ((x ◇ w) ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f : G → G) {a b : G}, a = b → f a = f b := by
    intro f a b p
    exact congrArg f p
  have apc2 : forall (q0 q1 : G), (q1 ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0))) = (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) := by
    intro q0 q1
    exact ((rfl).symm).trans ((((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ t) ((h q0 ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))))).symm)))).symm).trans ((h (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) q1).symm)).trans (rfl))
  have apc3 : forall (q2 q3 : G), (q3 ◇ ((((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))))) ◇ (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))))) = (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))))) := by
    intro q2 q3
    exact (((((cg (fun t => q3 ◇ t) (cg (fun t => (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2))))) ◇ t) (cg (fun t => t ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2))) (cg (fun t => ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ t) (cg (fun t => ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ t) (cg (fun t => t ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2))) (apc2 q2 ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2))))))))).trans (cg (fun t => q3 ◇ t) (cg (fun t => (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2))))) ◇ t) (cg (fun t => t ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2))) (cg (fun t => ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ t) (cg (fun t => ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ t) (apc2 q2 (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2)))))))))).trans (cg (fun t => q3 ◇ t) (cg (fun t => t ◇ ((((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)))) (cg (fun t => ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ t) (cg (fun t => ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ t) (apc2 q2 (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))))))))).trans (cg (fun t => q3 ◇ t) (cg (fun t => (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))))) ◇ t) (apc2 q2 (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))))))))).symm).trans ((((cg (fun t => q3 ◇ t) (cg (fun t => t ◇ ((((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ ((((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2))))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)))) (cg (fun t => ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ t) (cg (fun t => ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ t) (cg (fun t => t ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2))) (apc2 q2 ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)))))))).symm).trans (apc2 ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) q3)).trans ((cg (fun t => ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ t) (cg (fun t => ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ t) (cg (fun t => t ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2))) (apc2 q2 ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)))))).trans (cg (fun t => ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ t) (cg (fun t => ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ t) (apc2 q2 (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))))))))
  have apc4 : forall (q4 q5 : G), (((q4 ◇ (q4 ◇ ((q4 ◇ q4) ◇ q4))) ◇ ((q4 ◇ (q4 ◇ ((q4 ◇ q4) ◇ q4))) ◇ q4)) ◇ (((q4 ◇ (q4 ◇ ((q4 ◇ q4) ◇ q4))) ◇ ((q4 ◇ (q4 ◇ ((q4 ◇ q4) ◇ q4))) ◇ q4)) ◇ (q4 ◇ (q4 ◇ ((q4 ◇ q4) ◇ q4))))) = (q5 ◇ q4) := by
    intro q4 q5
    exact (((rfl).symm).trans ((((cg (fun t => q5 ◇ t) ((h q4 (((q4 ◇ (q4 ◇ ((q4 ◇ q4) ◇ q4))) ◇ ((q4 ◇ (q4 ◇ ((q4 ◇ q4) ◇ q4))) ◇ q4)) ◇ (((q4 ◇ (q4 ◇ ((q4 ◇ q4) ◇ q4))) ◇ ((q4 ◇ (q4 ◇ ((q4 ◇ q4) ◇ q4))) ◇ q4)) ◇ (q4 ◇ (q4 ◇ ((q4 ◇ q4) ◇ q4)))))).symm)).symm).trans (apc3 q4 q5)).trans (rfl))).symm
  have apc5 : forall (q6 q7 q8 : G), (q8 ◇ q7) = (q6 ◇ q7) := by
    intro q6 q7 q8
    exact (((rfl).symm).trans ((((apc4 q7 q6).symm).trans (apc4 q7 q8)).trans (rfl))).symm
  have apc6 : forall (q9 q10 q11 : G), (q11 ◇ (q10 ◇ (q9 ◇ ((q10 ◇ q10) ◇ q10)))) = q10 := by
    intro q9 q10 q11
    exact ((rfl).symm).trans ((((cg (fun t => q11 ◇ t) (cg (fun t => q10 ◇ t) (apc5 q9 ((q10 ◇ q10) ◇ q10) q10))).symm).trans ((h q10 q11).symm)).trans (rfl))
  have apc7 : forall (q12 q13 q14 q15 : G), (q15 ◇ (q12 ◇ (q13 ◇ ((q14 ◇ q14) ◇ q14)))) = q14 := by
    intro q12 q13 q14 q15
    exact ((rfl).symm).trans ((((cg (fun t => q15 ◇ t) (apc5 q12 (q13 ◇ ((q14 ◇ q14) ◇ q14)) q14)).symm).trans (apc6 q13 q14 q15)).trans (rfl))
  have apc14 : forall (q2 q3 : G), (q3 ◇ q2) = (q2 ◇ q2) := by
    intro q2 q3
    exact (((cg (fun t => q3 ◇ t) (cg (fun t => t ◇ (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2)))) (cg (fun t => ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ t) (apc7 q2 q2 q2 ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)))))).trans (cg (fun t => q3 ◇ t) (apc7 q2 q2 q2 (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ q2)))).symm).trans (((apc3 q2 q3).trans ((apc3 q2 q2).symm)).trans ((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2)))) (cg (fun t => ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ t) (apc7 q2 q2 q2 ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)))))).trans (cg (fun t => q2 ◇ t) (apc7 q2 q2 q2 (((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ ((q2 ◇ (q2 ◇ ((q2 ◇ q2) ◇ q2))) ◇ q2)) ◇ q2)))))
  have apc15 : forall (q12 q13 q14 q15 : G), (q15 ◇ (q14 ◇ (q13 ◇ (q12 ◇ q14)))) = q14 := by
    intro q12 q13 q14 q15
    exact ((rfl).symm).trans ((((cg (fun t => q15 ◇ t) (cg (fun t => q14 ◇ t) (cg (fun t => q13 ◇ t) (apc5 q12 q14 (q14 ◇ q14))))).symm).trans (apc6 q13 q14 q15)).trans (rfl))
  exact (calc
    x = x := rfl
    _ = (y ◇ (x ◇ (z ◇ ((x ◇ w) ◇ x)))) := (((cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (cg (fun t => z ◇ t) (cg (fun t => t ◇ x) (apc14 w x))))).trans (cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (cg (fun t => z ◇ t) (apc14 x (w ◇ w)))))).trans (apc15 x z x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5775_to_5861 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5775_to_5861
