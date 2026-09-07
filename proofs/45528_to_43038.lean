-- Equation45528 → Equation43038
-- Recorded verdict: true
-- Premise: x * y = y * (((z * w) * z) * z)
-- Conclusion: x * y = z * (y * ((z * w) * u))
-- Original submission SHA-256: fb48acc1e067e30aae6a39333855572120edf158e688be8517b8dfa18f5bafc3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (((z ◇ w) ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = z ◇ (y ◇ ((z ◇ w) ◇ u))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc10 : forall (q0 q1 q2:G), (q1 ◇ (q2 ◇ q2)) = (q0 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q1 ◇ t) ((apc0 ((q2 ◇ q0) ◇ q2) q2 q0 q0).symm)).symm).trans ((h q0 q1 q2 q0).symm)
  have apc11 : forall (q3 q4 q5:G), (q4 ◇ q5) = (q3 ◇ q5):=by
    intro q3 q4 q5
    exact ((h q3 q5 q3 q3).trans ((h q4 q5 q3 q3).symm)).symm
  have apc13 : forall (q6 q7 q8 q9:G), (q6 ◇ (q9 ◇ q9)) = (q7 ◇ q8):=by
    intro q6 q7 q8 q9
    exact ((apc11 q6 q8 (q9 ◇ q9)).symm).trans (apc10 q7 q8 q9)
  have apc16 : forall (q6 q7 q8 q9:G), (q7 ◇ q8) = (q6 ◇ q6):=by
    intro q6 q7 q8 q9
    exact ((apc13 q6 q7 q8 q9).symm).trans (apc13 q6 q6 q6 q9)
  exact (apc16 (x ◇ y) x y (x ◇ y)).trans ((apc16 (x ◇ y) z (y ◇ ((z ◇ w) ◇ u)) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45528_to_43038 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45528_to_43038
