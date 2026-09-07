-- Equation30525 → Equation2836
-- Recorded verdict: true
-- Premise: x = (y ◇ (y ◇ ((y ◇ x) ◇ z))) ◇ x
-- Conclusion: x = ((y ◇ z) ◇ (w ◇ w)) ◇ x
-- Original submission SHA-256: a182e87a7b9145ce755ed9ee2bd5e86400df3a77c4836a9c6da1507c75d88d82
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Tactic

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (y ◇ ((y ◇ x) ◇ z))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ z) ◇ (w ◇ w)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (x y z:G), ((y ◇ (y ◇ ((y ◇ x) ◇ z))) ◇ x) = ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc1 : forall (x y z:G), ((x ◇ (x ◇ ((x ◇ x) ◇ x))) ◇ x) = x:=by
    intro x y z
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2 : forall (q0 q1 q2:G), ((q1 ◇ (q1 ◇ q2)) ◇ (q1 ◇ ((q1 ◇ q2) ◇ q0))) = (q1 ◇ ((q1 ◇ q2) ◇ q0)):=by
    intro q0 q1 q2
    exact ((cg (fun t => t ◇ (q1 ◇ ((q1 ◇ q2) ◇ q0))) (cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) ((h q2 q1 q0).symm)))).symm).trans ((h (q1 ◇ ((q1 ◇ q2) ◇ q0)) q1 q2).symm)
  have apc3 : forall (q3 q4 q5:G), ((q5 ◇ (q5 ◇ (q5 ◇ ((q5 ◇ q4) ◇ q3)))) ◇ (q5 ◇ q4)) = (q5 ◇ q4):=by
    intro q3 q4 q5
    exact ((cg (fun t => t ◇ (q5 ◇ q4)) (cg (fun t => q5 ◇ t) (cg (fun t => q5 ◇ t) (apc2 q3 q5 q4)))).symm).trans ((h (q5 ◇ q4) q5 (q5 ◇ ((q5 ◇ q4) ◇ q3))).symm)
  have apc4 : forall (q6 q7 q8:G), (q8 ◇ ((q8 ◇ (q8 ◇ ((q8 ◇ q7) ◇ q6))) ◇ q7)) = (q8 ◇ q7):=by
    intro q6 q7 q8
    exact (((apc3 q6 q7 q8).symm).trans (((cg (fun t => (q8 ◇ (q8 ◇ (q8 ◇ ((q8 ◇ q7) ◇ q6)))) ◇ t) (cg (fun t => q8 ◇ t) ((h q7 q8 q6).symm))).symm).trans (apc2 q7 q8 (q8 ◇ ((q8 ◇ q7) ◇ q6))))).symm
  have apc15 : forall (q9 q10 q11 q12:G), ((q11 ◇ (q11 ◇ ((q11 ◇ q10) ◇ q12))) ◇ ((q11 ◇ (q11 ◇ ((q11 ◇ q10) ◇ q9))) ◇ q10)) = ((q11 ◇ (q11 ◇ ((q11 ◇ q10) ◇ q9))) ◇ q10):=by
    intro q9 q10 q11 q12
    exact ((cg (fun t => t ◇ ((q11 ◇ (q11 ◇ ((q11 ◇ q10) ◇ q9))) ◇ q10)) (cg (fun t => q11 ◇ t) (cg (fun t => q11 ◇ t) (cg (fun t => t ◇ q12) (apc4 q9 q10 q11))))).symm).trans ((h ((q11 ◇ (q11 ◇ ((q11 ◇ q10) ◇ q9))) ◇ q10) q11 q12).symm)
  have apc16 : forall (q13 q14:G), ((q13 ◇ (q13 ◇ ((q13 ◇ q13) ◇ q14))) ◇ q13) = q13:=by
    intro q13 q14
    exact (((cg (fun t => (q13 ◇ (q13 ◇ ((q13 ◇ q13) ◇ q14))) ◇ t) (apc1 q13 q13 q13)).symm).trans (apc15 q13 q13 q13 q14)).trans (apc1 q13 ((q13 ◇ (q13 ◇ ((q13 ◇ q13) ◇ q13))) ◇ q13) ((q13 ◇ (q13 ◇ ((q13 ◇ q13) ◇ q13))) ◇ q13))
  have apc21 : forall (q15 q16 q17:G), (q17 ◇ ((q17 ◇ (q17 ◇ ((q17 ◇ q17) ◇ q15))) ◇ (q17 ◇ q16))) = ((q17 ◇ (q17 ◇ ((q17 ◇ q17) ◇ q15))) ◇ (q17 ◇ q16)):=by
    intro q15 q16 q17
    exact (((cg (fun t => ((q17 ◇ (q17 ◇ ((q17 ◇ q17) ◇ q15))) ◇ q17) ◇ t) (cg (fun t => (q17 ◇ (q17 ◇ ((q17 ◇ q17) ◇ q15))) ◇ t) (cg (fun t => t ◇ q16) (apc16 q17 q15)))).trans (cg (fun t => t ◇ ((q17 ◇ (q17 ◇ ((q17 ◇ q17) ◇ q15))) ◇ (q17 ◇ q16))) (apc16 q17 q15))).symm).trans ((((cg (fun t => t ◇ ((q17 ◇ (q17 ◇ ((q17 ◇ q17) ◇ q15))) ◇ (((q17 ◇ (q17 ◇ ((q17 ◇ q17) ◇ q15))) ◇ q17) ◇ q16))) (cg (fun t => (q17 ◇ (q17 ◇ ((q17 ◇ q17) ◇ q15))) ◇ t) (apc16 q17 q15))).symm).trans (apc2 q16 (q17 ◇ (q17 ◇ ((q17 ◇ q17) ◇ q15))) q17)).trans (cg (fun t => (q17 ◇ (q17 ◇ ((q17 ◇ q17) ◇ q15))) ◇ t) (cg (fun t => t ◇ q16) (apc16 q17 q15))))
  have apc22 : forall (q18 q19 q20:G), (q20 ◇ (q20 ◇ ((q20 ◇ ((q20 ◇ q20) ◇ q19)) ◇ q18))) = (q20 ◇ ((q20 ◇ ((q20 ◇ q20) ◇ q19)) ◇ q18)):=by
    intro q18 q19 q20
    exact (((cg (fun t => q20 ◇ t) (apc2 q18 q20 ((q20 ◇ q20) ◇ q19))).symm).trans (apc21 q19 ((q20 ◇ ((q20 ◇ q20) ◇ q19)) ◇ q18) q20)).trans (apc2 q18 q20 ((q20 ◇ q20) ◇ q19))
  have apc25 : forall (q21 q22 q23:G), ((q23 ◇ ((q23 ◇ ((q23 ◇ q23) ◇ q21)) ◇ q22)) ◇ (q23 ◇ ((q23 ◇ q23) ◇ q21))) = (q23 ◇ ((q23 ◇ q23) ◇ q21)):=by
    intro q21 q22 q23
    exact ((cg (fun t => t ◇ (q23 ◇ ((q23 ◇ q23) ◇ q21))) (apc22 q22 q21 q23)).symm).trans (((cg (fun t => t ◇ (q23 ◇ ((q23 ◇ q23) ◇ q21))) (cg (fun t => q23 ◇ t) (apc22 q22 q21 q23))).symm).trans (apc3 q22 ((q23 ◇ q23) ◇ q21) q23))
  have apc26 : forall (q24 q0 q25 q2:G), (((q24 ◇ (q24 ◇ ((q24 ◇ q25) ◇ q0))) ◇ ((q24 ◇ (q24 ◇ ((q24 ◇ q25) ◇ q0))) ◇ (q25 ◇ q2))) ◇ q25) = q25:=by
    intro q24 q0 q25 q2
    exact ((cg (fun t => t ◇ q25) (cg (fun t => (q24 ◇ (q24 ◇ ((q24 ◇ q25) ◇ q0))) ◇ t) (cg (fun t => (q24 ◇ (q24 ◇ ((q24 ◇ q25) ◇ q0))) ◇ t) (cg (fun t => t ◇ q2) ((h q25 q24 q0).symm))))).symm).trans ((h q25 (q24 ◇ (q24 ◇ ((q24 ◇ q25) ◇ q0))) q2).symm)
  have apc27 : forall (q26 q27 q28:G), ((q28 ◇ ((q28 ◇ ((q28 ◇ q28) ◇ q27)) ◇ q26)) ◇ q28) = q28:=by
    intro q26 q27 q28
    exact ((cg (fun t => t ◇ q28) (apc2 q26 q28 ((q28 ◇ q28) ◇ q27))).symm).trans (((cg (fun t => t ◇ q28) (cg (fun t => (q28 ◇ (q28 ◇ ((q28 ◇ q28) ◇ q27))) ◇ t) (apc2 q26 q28 ((q28 ◇ q28) ◇ q27)))).symm).trans (apc26 q28 q27 q28 ((q28 ◇ ((q28 ◇ q28) ◇ q27)) ◇ q26)))
  have apc28 : forall (q29 q30 q31:G), ((q31 ◇ ((q31 ◇ ((q31 ◇ q31) ◇ q30)) ◇ q29)) ◇ (q31 ◇ q31)) = (q31 ◇ q31):=by
    intro q29 q30 q31
    exact ((cg (fun t => t ◇ (q31 ◇ q31)) (apc22 q29 q30 q31)).symm).trans ((((cg (fun t => (q31 ◇ (q31 ◇ ((q31 ◇ ((q31 ◇ q31) ◇ q30)) ◇ q29))) ◇ t) (cg (fun t => q31 ◇ t) (apc27 q29 q30 q31))).symm).trans (apc2 q31 q31 ((q31 ◇ ((q31 ◇ q31) ◇ q30)) ◇ q29))).trans (cg (fun t => q31 ◇ t) (apc27 q29 q30 q31)))
  have apc32 : forall (q29 q30 q31 q32:G), (q32 ◇ ((q32 ◇ ((q32 ◇ ((q32 ◇ q32) ◇ q30)) ◇ q29)) ◇ (q32 ◇ q31))) = ((q32 ◇ ((q32 ◇ ((q32 ◇ q32) ◇ q30)) ◇ q29)) ◇ (q32 ◇ q31)):=by
    intro q29 q30 q31 q32
    exact (((cg (fun t => ((q32 ◇ ((q32 ◇ ((q32 ◇ q32) ◇ q30)) ◇ q29)) ◇ q32) ◇ t) (cg (fun t => (q32 ◇ ((q32 ◇ ((q32 ◇ q32) ◇ q30)) ◇ q29)) ◇ t) (cg (fun t => t ◇ q31) (apc27 q29 q30 q32)))).trans (cg (fun t => t ◇ ((q32 ◇ ((q32 ◇ ((q32 ◇ q32) ◇ q30)) ◇ q29)) ◇ (q32 ◇ q31))) (apc27 q29 q30 q32))).symm).trans ((((cg (fun t => t ◇ ((q32 ◇ ((q32 ◇ ((q32 ◇ q32) ◇ q30)) ◇ q29)) ◇ (((q32 ◇ ((q32 ◇ ((q32 ◇ q32) ◇ q30)) ◇ q29)) ◇ q32) ◇ q31))) (cg (fun t => (q32 ◇ ((q32 ◇ ((q32 ◇ q32) ◇ q30)) ◇ q29)) ◇ t) (apc27 q29 q30 q32))).symm).trans (apc2 q31 (q32 ◇ ((q32 ◇ ((q32 ◇ q32) ◇ q30)) ◇ q29)) q32)).trans (cg (fun t => (q32 ◇ ((q32 ◇ ((q32 ◇ q32) ◇ q30)) ◇ q29)) ◇ t) (cg (fun t => t ◇ q31) (apc27 q29 q30 q32))))
  have apc33 : forall (q33:G), (q33 ◇ (q33 ◇ q33)) = (q33 ◇ q33):=by
    intro q33
    exact (((cg (fun t => q33 ◇ t) (apc28 q33 q33 q33)).symm).trans (apc32 q33 q33 q33 q33)).trans (apc28 q33 q33 q33)
  have apc34 : forall (q34 q35:G), (q35 ◇ (q35 ◇ ((q35 ◇ q35) ◇ q34))) = (q35 ◇ ((q35 ◇ q35) ◇ q34)):=by
    intro q34 q35
    exact (((cg (fun t => q35 ◇ t) (apc25 q34 q34 q35)).symm).trans (apc32 q34 q34 ((q35 ◇ q35) ◇ q34) q35)).trans (apc25 q34 q34 q35)
  have apc35 : forall (q34 q35 q13 q14:G), ((q13 ◇ ((q13 ◇ q13) ◇ q14)) ◇ q13) = q13:=by
    intro q34 q35 q13 q14
    exact ((cg (fun t => t ◇ q13) (apc34 q14 q13)).symm).trans (apc16 q13 q14)
  have apc37 : forall (q36:G), ((q36 ◇ q36) ◇ (q36 ◇ q36)) = (q36 ◇ q36):=by
    intro q36
    exact ((cg (fun t => t ◇ (q36 ◇ q36)) (cg (fun t => q36 ◇ t) (apc35 q36 q36 q36 q36))).symm).trans (apc28 q36 q36 q36)
  have apc40 : forall (q37 q38:G), ((q38 ◇ q38) ◇ ((q38 ◇ q38) ◇ q37)) = ((q38 ◇ q38) ◇ q37):=by
    intro q37 q38
    exact ((cg (fun t => t ◇ ((q38 ◇ q38) ◇ q37)) (apc33 q38)).symm).trans (((cg (fun t => t ◇ ((q38 ◇ q38) ◇ q37)) (cg (fun t => q38 ◇ t) (cg (fun t => q38 ◇ t) (apc35 q37 q37 q38 q37)))).symm).trans ((h ((q38 ◇ q38) ◇ q37) q38 q38).symm))
  have apc41 : forall (q39 q40:G), ((q39 ◇ ((q39 ◇ q39) ◇ q40)) ◇ (q39 ◇ q39)) = (q39 ◇ q39):=by
    intro q39 q40
    exact ((cg (fun t => t ◇ (q39 ◇ q39)) (apc34 q40 q39)).symm).trans (((cg (fun t => t ◇ (q39 ◇ q39)) (cg (fun t => q39 ◇ t) (cg (fun t => q39 ◇ t) (cg (fun t => t ◇ q40) (apc33 q39))))).symm).trans ((h (q39 ◇ q39) q39 q40).symm))
  have apc42 : forall (q41 q42:G), (((q41 ◇ q41) ◇ q42) ◇ (q41 ◇ q41)) = (q41 ◇ q41):=by
    intro q41 q42
    exact (((cg (fun t => ((q41 ◇ q41) ◇ ((q41 ◇ q41) ◇ q42)) ◇ t) (apc37 q41)).trans (cg (fun t => t ◇ (q41 ◇ q41)) (apc40 q42 q41))).symm).trans ((((cg (fun t => t ◇ ((q41 ◇ q41) ◇ (q41 ◇ q41))) (cg (fun t => (q41 ◇ q41) ◇ t) (cg (fun t => t ◇ q42) (apc37 q41)))).symm).trans (apc41 (q41 ◇ q41) q42)).trans (apc37 q41))
  have apc43 : forall (q43 q44:G), ((q43 ◇ q43) ◇ q44) = q44:=by
    intro q43 q44
    exact (((cg (fun t => t ◇ q44) (cg (fun t => (q43 ◇ q43) ◇ t) (apc37 q43))).trans (cg (fun t => t ◇ q44) (apc37 q43))).symm).trans (((cg (fun t => t ◇ q44) (cg (fun t => (q43 ◇ q43) ◇ t) (cg (fun t => (q43 ◇ q43) ◇ t) (apc42 q43 q44)))).symm).trans ((h q44 (q43 ◇ q43) (q43 ◇ q43)).symm))
  have apc46 : forall (q41 q42 q43 q44:G), (q42 ◇ (q41 ◇ q41)) = (q41 ◇ q41):=by
    intro q41 q42 q43 q44
    exact ((cg (fun t => t ◇ (q41 ◇ q41)) (apc43 q41 q42)).symm).trans (apc42 q41 q42)
  exact (calc
    x = x:=rfl
    _ = (((y ◇ z) ◇ (w ◇ w)) ◇ x):=((cg (fun t => t ◇ x) (apc46 w (y ◇ z) ((y ◇ z) ◇ (w ◇ w)) ((y ◇ z) ◇ (w ◇ w)))).trans (apc43 w x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_30525_to_2836 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_30525_to_2836
