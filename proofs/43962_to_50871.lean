-- Equation43962 → Equation50871
-- Recorded verdict: true
-- Premise: x * y = z * ((z * y) * (x * w))
-- Conclusion: x * y = (z * ((x * w) * w)) * y
-- Original submission SHA-256: 0b13658ca3bcc24a4e62bb24f282f4232bf8db7552f2a4a2b3670ade200da5c2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((z ◇ y) ◇ (x ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ ((x ◇ w) ◇ w)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (((q3 ◇ q2) ◇ q1) ◇ q2) = (q3 ◇ (q0 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact (((congrArg (fun t => q3 ◇ t) ((h q0 q1 (q3 ◇ q2) q0).symm)).symm).trans ((h ((q3 ◇ q2) ◇ q1) q2 q3 (q0 ◇ q0)).symm)).symm
  have apc1 : forall (q4 q5 q6 q7:G), (q7 ◇ (q5 ◇ q6)) = (q7 ◇ (q4 ◇ q6)):=by
    intro q4 q5 q6 q7
    exact (((apc0 q4 q6 q4 q7).symm).trans (apc0 q5 q6 q4 q7)).symm
  have apc3 : forall (q8 q9 q10 q11 q12:G), (q12 ◇ (q8 ◇ (q10 ◇ q9))) = (q10 ◇ q11):=by
    intro q8 q9 q10 q11 q12
    exact ((apc1 q8 (q12 ◇ q11) (q10 ◇ q9) q12).symm).trans ((h q10 q11 q12 q9).symm)
  have apc4 : forall (q8 q10 q11 q9 q12:G), (q10 ◇ q11) = (q10 ◇ q8):=by
    intro q8 q10 q11 q9 q12
    exact ((apc3 q8 q9 q10 q11 q12).symm).trans (apc3 q8 q9 q10 q8 q12)
  have apc6 : forall (q13 q14 q15 q16:G), (q16 ◇ q13) = (q14 ◇ q15):=by
    intro q13 q14 q15 q16
    exact ((apc4 q13 q16 (q13 ◇ (q14 ◇ q13)) q13 q13).symm).trans (apc3 q13 q13 q14 q15 q16)
  exact (apc6 y (x ◇ y) ((z ◇ ((x ◇ w) ◇ w)) ◇ y) x).trans ((apc6 y (x ◇ y) ((z ◇ ((x ◇ w) ◇ w)) ◇ y) (z ◇ ((x ◇ w) ◇ w))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43962_to_50871 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43962_to_50871
