-- Equation60571 → Equation62407
-- Recorded verdict: true
-- Premise: (x * y) * z = (y * z) * (z * y)
-- Conclusion: (x * y) * z = ((z * z) * w) * z
-- Original submission SHA-256: 4a105ca06f843aac7d0a51a94d26e40173af1f78f352e8b3a57d171dc32e1b7f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = (y ◇ z) ◇ (z ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = ((z ◇ z) ◇ w) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), ((q1 ◇ q2) ◇ q3) = ((q0 ◇ q2) ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((h q0 q2 q3).trans ((h q1 q2 q3).symm)).symm
  have apc1 : forall (x y z:G), ((y ◇ y) ◇ z) = ((x ◇ y) ◇ z):=by
    intro x y z
    exact ((h x y z).trans ((h y y z).symm)).symm
  have apc9 : forall (q4 q5 q6 q7:G), ((q4 ◇ q5) ◇ (q5 ◇ q4)) = ((q4 ◇ q4) ◇ q5):=by
    intro q4 q5 q6 q7
    exact ((h (q6 ◇ q7) q4 q5).symm).trans (((congrArg (fun t => t ◇ q5) (apc1 q6 q7 q4)).symm).trans ((apc1 (q7 ◇ q7) q4 q5).symm))
  have apc10 : forall (q8 q9 q10 q11:G), ((q10 ◇ (q9 ◇ q8)) ◇ q11) = ((q9 ◇ q9) ◇ q11):=by
    intro q8 q9 q10 q11
    exact ((((h (q8 ◇ q8) q9 q11).trans (apc9 q9 q11 ((q9 ◇ q11) ◇ (q11 ◇ q9)) ((q9 ◇ q11) ◇ (q11 ◇ q9)))).symm).trans (((congrArg (fun t => t ◇ q11) (apc9 q8 q9 q8 q8)).symm).trans (apc0 q10 (q8 ◇ q9) (q9 ◇ q8) q11))).symm
  have apc12 : forall (q12 q13 q14 q15 q16:G), ((q13 ◇ q13) ◇ q14) = ((q12 ◇ q12) ◇ q14):=by
    intro q12 q13 q14 q15 q16
    exact ((((apc10 q15 (q12 ◇ q13) q16 q14).trans (apc10 q13 q12 (q12 ◇ q13) q14)).symm).trans ((((congrArg (fun t => t ◇ q14) (congrArg (fun t => q16 ◇ t) (apc1 q12 q13 q15))).symm).trans (apc10 q15 (q13 ◇ q13) q16 q14)).trans (((congrArg (fun t => t ◇ q14) (apc9 q13 q13 ((q13 ◇ q13) ◇ (q13 ◇ q13)) ((q13 ◇ q13) ◇ (q13 ◇ q13)))).trans (h (q13 ◇ q13) q13 q14)).trans (apc9 q13 q14 ((q13 ◇ q14) ◇ (q14 ◇ q13)) ((q13 ◇ q14) ◇ (q14 ◇ q13)))))).symm
  have apc13 : forall (q17 q18 q19 q20:G), ((q18 ◇ q19) ◇ q20) = ((q17 ◇ q17) ◇ q20):=by
    intro q17 q18 q19 q20
    exact (((apc12 q17 q19 q20 q17 q17).symm).trans (apc1 q18 q19 q20)).symm
  exact (apc13 ((x ◇ y) ◇ z) x y z).trans ((apc13 ((x ◇ y) ◇ z) (z ◇ z) w z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_60571_to_62407 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_60571_to_62407
