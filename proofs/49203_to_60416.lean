-- Equation49203 → Equation60416
-- Recorded verdict: true
-- Premise: x * y = ((z * y) * w) * (u * v)
-- Conclusion: (x * y) * y = (z * z) * (z * x)
-- Original submission SHA-256: f2bfba8e8deb5435f1fa4a33a8e3a7456afc1d54a1a72e510a8986e70bd056bb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ y = ((z ◇ y) ◇ w) ◇ (u ◇ v)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ y = (z ◇ z) ◇ (z ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), ((q0 ◇ q1) ◇ (q2 ◇ q3)) = (q4 ◇ q5):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => t ◇ (q2 ◇ q3)) ((h q0 q1 q0 q5 q0 q0).symm)).symm).trans ((h q4 q5 (q0 ◇ q1) (q0 ◇ q0) q2 q3).symm)
  have apc1 : forall (q0 q1 q2 q3 q4 q5:G), ((q4 ◇ q4) ◇ (q4 ◇ q4)) = ((q0 ◇ q1) ◇ (q2 ◇ q3)):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((apc0 q0 q1 q2 q3 q4 q5).trans ((apc0 q4 q4 q4 q4 q4 q5).symm)).symm
  have apc2 : forall (q6 q7 q8:G), ((q6 ◇ q6) ◇ (q6 ◇ q6)) = (q7 ◇ q8):=by
    intro q6 q7 q8
    exact (apc1 q6 q6 q6 q6 q6 q6).trans (apc0 q6 q6 q6 q6 q7 q8)
  exact ((apc2 ((x ◇ y) ◇ y) (x ◇ y) y).symm).trans (apc2 ((x ◇ y) ◇ y) (z ◇ z) (z ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49203_to_60416 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49203_to_60416
