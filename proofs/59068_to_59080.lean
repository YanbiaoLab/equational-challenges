-- Equation59068 → Equation59080
-- Recorded verdict: true
-- Premise: (x ◇ y) ◇ z = w ◇ (u ◇ (v ◇ r))
-- Conclusion: (x ◇ x) ◇ x = x ◇ ((y ◇ z) ◇ x)
-- Original submission SHA-256: 4986f9a5d2e8bb877ce62647c76133e98fc57bf61b02802e66d21b5faad4b521
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G) (r : G), (x ◇ y) ◇ z = w ◇ (u ◇ (v ◇ r))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ x = x ◇ ((y ◇ z) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have p0 : forall (x y z w u v r:G), ((x ◇ y) ◇ z) = ((w ◇ w) ◇ w):=by
    intro x y z w u v r
    exact (h x y z w u v r).trans ((h w w w w u v r).symm)
  have p1 : forall (x w y z u v r:G), ((x ◇ x) ◇ x) = ((w ◇ w) ◇ w):=by
    intro x w y z u v r
    exact (((p0 x y z w u v r).symm).trans (p0 x y z x u v r)).symm
  have p2 : forall (q0 q1 q2 q3 q4 q5 q6:G), (q3 ◇ ((q0 ◇ q1) ◇ q2)) = ((q4 ◇ q5) ◇ q6):=by
    intro q0 q1 q2 q3 q4 q5 q6
    exact ((congrArg (fun t => q3 ◇ t) ((h q0 q1 q2 q0 q0 q0 q0).symm)).symm).trans ((h q4 q5 q6 q3 q0 q0 (q0 ◇ q0)).symm)
  have p3 : forall (q7 q8 q9 q10 q11:G), (q10 ◇ ((q7 ◇ q8) ◇ q9)) = ((q11 ◇ q11) ◇ q11):=by
    intro q7 q8 q9 q10 q11
    exact (p2 q7 q8 q9 q10 q7 q7 q7).trans (p1 q7 q11 q7 q7 q7 q7 q7)
  exact (p3 y z x x x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_59068_to_59080 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_59068_to_59080
