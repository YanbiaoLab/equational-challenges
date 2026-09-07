-- Equation20046 → Equation62546
-- Recorded verdict: true
-- Premise: x = (y ◇ y) ◇ ((z ◇ (x ◇ w)) ◇ z)
-- Conclusion: (x ◇ y) ◇ z = ((w ◇ u) ◇ y) ◇ x
-- Original submission SHA-256: 7c7d7eb5a9a870698d5510665299daaa704d86e7800a8108bc2d22729bf8d600
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ y) ◇ ((z ◇ (x ◇ w)) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = ((w ◇ u) ◇ y) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ (q1 ◇ q0)) = ((q3 ◇ q3) ◇ q1):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => (q3 ◇ q3) ◇ t) ((h q1 ((q2 ◇ (q1 ◇ q0)) ◇ q2) q2 q0).symm)).symm).trans ((h (q2 ◇ (q1 ◇ q0)) q3 ((q2 ◇ (q1 ◇ q0)) ◇ q2) q2).symm)).symm
  have apc3 : forall (q0 q1 q2 q3:G), (q2 ◇ (q1 ◇ q0)) = (q1 ◇ (q1 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact (apc0 q0 q1 q2 q3).trans ((apc0 q1 q1 q1 q3).symm)
  have apc4 : forall (q4 q5 q6:G), (q4 ◇ (q4 ◇ q4)) = q4:=by
    intro q4 q5 q6
    exact ((((((congrArg (fun t => (q5 ◇ (q4 ◇ q6)) ◇ t) (congrArg (fun t => t ◇ (q5 ◇ (q4 ◇ q6))) (apc3 q6 q4 q5 (q5 ◇ (q4 ◇ q6))))).trans (congrArg (fun t => (q5 ◇ (q4 ◇ q6)) ◇ t) (congrArg (fun t => (q4 ◇ (q4 ◇ q4)) ◇ t) (apc3 q6 q4 q5 (q5 ◇ (q4 ◇ q6)))))).trans (congrArg (fun t => t ◇ ((q4 ◇ (q4 ◇ q4)) ◇ (q4 ◇ (q4 ◇ q4)))) (apc3 q6 q4 q5 (q5 ◇ (q4 ◇ q6))))).trans (congrArg (fun t => (q4 ◇ (q4 ◇ q4)) ◇ t) (apc3 (q4 ◇ q4) q4 (q4 ◇ (q4 ◇ q4)) ((q4 ◇ (q4 ◇ q4)) ◇ (q4 ◇ (q4 ◇ q4)))))).trans (apc3 (q4 ◇ q4) q4 (q4 ◇ (q4 ◇ q4)) ((q4 ◇ (q4 ◇ q4)) ◇ (q4 ◇ (q4 ◇ q4))))).symm).trans (((apc3 q5 (q5 ◇ (q4 ◇ q6)) (q6 ◇ q6) q6).symm).trans ((h q4 q6 q5 q6).symm))
  have apc5 : forall (x y z w:G), ((y ◇ y) ◇ ((z ◇ (x ◇ w)) ◇ z)) = ((x ◇ x) ◇ (x ◇ x)):=by
    intro x y z w
    exact (((h x y z w).symm).trans (h x x x x)).trans (congrArg (fun t => (x ◇ x) ◇ t) (congrArg (fun t => t ◇ x) (apc4 x (x ◇ (x ◇ x)) (x ◇ (x ◇ x)))))
  have apc6 : forall (q7:G), ((q7 ◇ q7) ◇ (q7 ◇ q7)) = q7:=by
    intro q7
    exact ((apc5 q7 q7 q7 q7).symm).trans ((h q7 q7 q7 q7).symm)
  have apc7 : forall (q8 q9:G), ((q9 ◇ q9) ◇ q8) = q8:=by
    intro q8 q9
    exact ((congrArg (fun t => (q9 ◇ q9) ◇ t) (apc4 q8 (q8 ◇ (q8 ◇ q8)) (q8 ◇ (q8 ◇ q8)))).symm).trans (((congrArg (fun t => (q9 ◇ q9) ◇ t) (congrArg (fun t => t ◇ (q8 ◇ q8)) (apc6 q8))).symm).trans ((h q8 q9 (q8 ◇ q8) q8).symm))
  have apc8 : forall (q10 q11 q12:G), (q11 ◇ q10) = q11:=by
    intro q10 q11 q12
    exact ((apc7 (q11 ◇ q10) q12).symm).trans (((congrArg (fun t => (q12 ◇ q12) ◇ t) (apc7 (q11 ◇ q10) (q11 ◇ q10))).symm).trans ((h q11 q12 (q11 ◇ q10) q10).symm))
  have apc9 : forall (q8 q9:G), q9 = q8:=by
    intro q8 q9
    exact (((congrArg (fun t => t ◇ q8) (apc8 q9 q9 (q9 ◇ q9))).trans (apc8 q8 q9 (q9 ◇ q8))).symm).trans (apc7 q8 q9)
  exact (apc9 ((x ◇ y) ◇ z) ((x ◇ y) ◇ z)).trans ((apc9 ((x ◇ y) ◇ z) (((w ◇ u) ◇ y) ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20046_to_62546 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20046_to_62546
