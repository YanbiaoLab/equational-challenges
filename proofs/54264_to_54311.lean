-- Equation54264 → Equation54311
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ y) = z ◇ (y ◇ (w ◇ x))
-- Conclusion: x ◇ (y ◇ y) = z ◇ (w ◇ (u ◇ v))
-- Original submission SHA-256: a662ce85f98e3041558f35e8ce1052975b1a8fca9152d931432d3944042c9406
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = z ◇ (y ◇ (w ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x ◇ (y ◇ y) = z ◇ (w ◇ (u ◇ v))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u v
  have apc0 : forall (x y z w:G), (z ◇ (y ◇ (w ◇ x))) = (x ◇ (y ◇ (x ◇ x))):=by
    intro x y z w
    exact ((h x y z w).symm).trans (h x y x x)
  have apc1 : forall (q0 q1 q2 q3:G), (q2 ◇ (q1 ◇ (q2 ◇ q2))) = ((q0 ◇ q1) ◇ (q3 ◇ q3)):=by
    intro q0 q1 q2 q3
    exact ((apc0 q2 q1 q0 q2).symm).trans (((congrArg (fun t => q0 ◇ t) ((h q1 q2 q3 q0).symm)).symm).trans ((h (q0 ◇ q1) q3 q0 q2).symm))
  have apc2 : forall (q4 q5 q6 q7:G), ((q4 ◇ q7) ◇ (q5 ◇ q5)) = (q6 ◇ (q7 ◇ q7)):=by
    intro q4 q5 q6 q7
    exact ((apc1 q4 q7 q6 q5).symm).trans ((h q6 q7 q6 q6).symm)
  have apc3 : forall (q4 q5 q6 q7:G), (q6 ◇ (q7 ◇ q7)) = (q4 ◇ (q7 ◇ q7)):=by
    intro q4 q5 q6 q7
    exact ((apc2 q4 q4 q6 q7).symm).trans (apc2 q4 q4 q4 q7)
  have apc4 : forall (q8 q9 q10 q11:G), (q10 ◇ (q11 ◇ q11)) = (q8 ◇ (q9 ◇ q9)):=by
    intro q8 q9 q10 q11
    exact (((apc3 q8 q8 (q8 ◇ q11) q9).symm).trans (apc2 q8 q9 q10 q11)).symm
  exact (calc
    (x ◇ (y ◇ y)) = (v ◇ (w ◇ w)):=apc4 v w x y
    _ = (z ◇ (w ◇ (u ◇ v))):=((h v w z u).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_54264_to_54311 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_54264_to_54311
