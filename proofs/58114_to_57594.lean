-- Equation58114 → Equation57594
-- Recorded verdict: true
-- Premise: x * (y * z) = ((w * z) * z) * y
-- Conclusion: x * (y * x) = ((z * x) * x) * z
-- Original submission SHA-256: 8f333c59890c27b5e813892bab8956efb2ec7cf4221a29ee82114f4953d91545
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = ((w ◇ z) ◇ z) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ x) = ((z ◇ x) ◇ x) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w:G), (y ◇ (y ◇ z)) = (x ◇ (y ◇ z)):=by
    intro x y z w
    exact ((h x y z x).trans ((h y y z x).symm)).symm
  have apc5 : forall (q0 q1 q2 q3:G), (q2 ◇ ((q0 ◇ q1) ◇ q3)) = (q0 ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((apc0 ((q0 ◇ q3) ◇ q3) q0 q1 q0).trans ((h q2 (q0 ◇ q1) q3 q0).symm)).symm
  have apc6 : forall (q4 q5 q6 q7:G), (q6 ◇ (q6 ◇ q7)) = (q4 ◇ (q4 ◇ q5)):=by
    intro q4 q5 q6 q7
    exact ((((apc5 (q4 ◇ q5) q5 q4 q4).trans (apc5 q4 q5 (q4 ◇ q5) q5)).symm).trans (((congrArg (fun t => q4 ◇ t) (h (q6 ◇ q7) q4 q5 q4)).symm).trans (apc5 q6 q7 q4 (q4 ◇ q5)))).symm
  have apc9 : forall (q8 q9 q10 q11 q12:G), (q10 ◇ (q11 ◇ q12)) = (q8 ◇ (q8 ◇ q9)):=by
    intro q8 q9 q10 q11 q12
    exact (((apc6 q8 q9 q11 q12).symm).trans (apc0 q10 q11 q12 q8)).symm
  exact (calc
    (x ◇ (y ◇ x)) = (z ◇ (z ◇ x)):=apc9 z x x y x
    _ = (((z ◇ x) ◇ x) ◇ z):=((h z z x z).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_58114_to_57594 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_58114_to_57594
