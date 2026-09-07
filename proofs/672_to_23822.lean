-- Equation672 → Equation23822
-- Recorded verdict: true
-- Premise: x = y * (x * ((x * z) * x))
-- Conclusion: x = ((y * z) * z) * (w * (x * x))
-- Original submission SHA-256: 9f8c7156f708700d892586429abf9563705044f0d07a5d8ac2aad5d380d5b9b4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((x ◇ z) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ z) ◇ (w ◇ (x ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ (q0 ◇ q1))) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => q1 ◇ t) (congrArg (fun t => t ◇ q1) ((h q0 q1 q0).symm)))).symm).trans ((h q1 q2 (q0 ◇ ((q0 ◇ q0) ◇ q0))).symm)
  have apc1 : forall (q3 q4 q5:G), ((q4 ◇ q3) ◇ q4) = (q5 ◇ q4):=by
    intro q3 q4 q5
    exact (((congrArg (fun t => q5 ◇ t) ((h q4 ((q4 ◇ q3) ◇ q4) q3).symm)).symm).trans (apc0 q4 ((q4 ◇ q3) ◇ q4) q5)).symm
  have apc2 : forall (q6 q7 q8 q9:G), (((q7 ◇ q6) ◇ q7) ◇ q8) = (q9 ◇ q8):=by
    intro q6 q7 q8 q9
    exact ((congrArg (fun t => t ◇ q8) ((apc1 q6 q7 q8).symm)).symm).trans (apc1 q7 q8 q9)
  have apc6 : forall (q10 q11 q12 q13 q14:G), (q14 ◇ (((q11 ◇ q10) ◇ q11) ◇ (q12 ◇ q13))) = q13:=by
    intro q10 q11 q12 q13 q14
    exact ((congrArg (fun t => q14 ◇ t) ((apc2 q10 q11 (q12 ◇ q13) q13).symm)).symm).trans (apc0 q12 q13 q14)
  have apc7 : forall (q15 q16 q17 q18:G), (q18 ◇ (q15 ◇ (q16 ◇ q17))) = q17:=by
    intro q15 q16 q17 q18
    exact ((congrArg (fun t => q18 ◇ t) (congrArg (fun t => t ◇ (q16 ◇ q17)) (apc0 q15 q15 ((q15 ◇ (q15 ◇ q15)) ◇ q15)))).symm).trans (apc6 q15 (q15 ◇ (q15 ◇ q15)) q16 q17 q18)
  exact (calc
    x = x:=rfl
    _ = (((y ◇ z) ◇ z) ◇ (w ◇ (x ◇ x))):=(apc7 w x x ((y ◇ z) ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_672_to_23822 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_672_to_23822
