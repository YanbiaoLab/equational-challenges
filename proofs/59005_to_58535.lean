-- Equation59005 → Equation58535
-- Recorded verdict: true
-- Premise: (x * y) * z = w * (z * (u * v))
-- Conclusion: (x * y) * x = z * (w * (w * x))
-- Original submission SHA-256: aeeb58ca811382319ee35c89c1b3513c935d35c3e5aea72f1a7770baf52c99c8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), (x ◇ y) ◇ z = w ◇ (z ◇ (u ◇ v))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ x = z ◇ (w ◇ (w ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc5 : forall (q0 q1 q2 q3 q4 q5 q6:G), (q3 ◇ ((q0 ◇ q1) ◇ q2)) = ((q4 ◇ q5) ◇ q6):=by
    intro q0 q1 q2 q3 q4 q5 q6
    exact ((congrArg (fun t => q3 ◇ t) ((h q0 q1 q2 q6 q0 q0).symm)).symm).trans ((h q4 q5 q6 q3 q2 (q0 ◇ q0)).symm)
  have apc7 : forall (q7 q8 q9 q10 q11 q12:G), ((q10 ◇ q11) ◇ q12) = ((q7 ◇ q8) ◇ q9):=by
    intro q7 q8 q9 q10 q11 q12
    exact (((apc5 q7 q7 q7 q7 q7 q8 q9).symm).trans (apc5 q7 q7 q7 q7 q10 q11 q12)).symm
  exact (calc
    ((x ◇ y) ◇ x) = ((w ◇ x) ◇ w):=(apc7 x y x w x w).symm
    _ = (z ◇ (w ◇ (w ◇ x))):=((h w x w z w x).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_59005_to_58535 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_59005_to_58535
