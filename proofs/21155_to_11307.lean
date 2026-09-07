-- Equation21155 → Equation11307
-- Recorded verdict: true
-- Premise: x = (y ◇ z) ◇ (((z ◇ x) ◇ w) ◇ w)
-- Conclusion: x = y ◇ ((y ◇ (z ◇ z)) ◇ (z ◇ w))
-- Original submission SHA-256: 2be4a58e17e11a6a543898966fdfb99e15c2689e6c0f17e1c3910cdb20001efb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ (((z ◇ x) ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((y ◇ (z ◇ z)) ◇ (z ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q3 ◇ q4) ◇ (q1 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0))) = q2:=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => (q3 ◇ q4) ◇ t) (congrArg (fun t => t ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)) ((h q1 q4 q2 q0).symm))).symm).trans ((h q2 q3 q4 (((q2 ◇ q1) ◇ q0) ◇ q0)).symm)
  have apc1 : forall (q5 q6 q7 q8:G), (q5 ◇ (q7 ◇ (((q8 ◇ q7) ◇ q6) ◇ q6))) = q8:=by
    intro q5 q6 q7 q8
    exact ((congrArg (fun t => t ◇ (q7 ◇ (((q8 ◇ q7) ◇ q6) ◇ q6))) ((h q5 q5 q5 q5).symm)).symm).trans (apc0 q6 q7 q8 (q5 ◇ q5) (((q5 ◇ q5) ◇ q5) ◇ q5))
  have apc2 : forall (q9 q10 q11 q12 q13:G), (q9 ◇ q10) = q11:=by
    intro q9 q10 q11 q12 q13
    exact ((congrArg (fun t => q9 ◇ t) (apc1 q10 q12 q13 q10)).symm).trans (((congrArg (fun t => q9 ◇ t) (congrArg (fun t => q10 ◇ t) (congrArg (fun t => t ◇ (((q10 ◇ q13) ◇ q12) ◇ q12)) ((h q13 q11 q10 q12).symm)))).symm).trans (apc1 q9 (((q10 ◇ q13) ◇ q12) ◇ q12) q10 q11))
  exact ((apc2 z x x x x).symm).trans ((apc2 y ((y ◇ (z ◇ z)) ◇ (z ◇ w)) (z ◇ x) x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_21155_to_11307 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_21155_to_11307
