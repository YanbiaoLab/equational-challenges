-- Equation32791 → Equation51524
-- Recorded verdict: true
-- Premise: x = (x * (((x * y) * y) * z)) * y
-- Conclusion: x * y = ((x * z) * (w * u)) * x
-- Original submission SHA-256: 3d16696cefd6a57cf2ce0b73b19627d63f40f33cc81f6af7c02cd1993dfb1a58
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (((x ◇ y) ◇ y) ◇ z)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((x ◇ z) ◇ (w ◇ u)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have apc0:=fun (x y z:G)=>by
    exact ((h x y z).symm).trans (h x x x)
  have apc1:=fun (x y z:G)=>by
    exact ((h x x x).trans (apc0 x x x)).symm
  have apc2:=fun (q0 q1 q2 q3:G)=>by
    exact ((cg (fun t => t ◇ q2) (cg (fun t => (q0 ◇ (((q0 ◇ q2) ◇ q2) ◇ q1)) ◇ t) (cg (fun t => t ◇ q3) (cg (fun t => t ◇ q2) ((h q0 q2 q1).symm))))).symm).trans ((h (q0 ◇ (((q0 ◇ q2) ◇ q2) ◇ q1)) q2 q3).symm)
  have apc4:=fun (q4 q5 q6 q7 q8:G)=>by
    exact ((cg (fun t => t ◇ q7) (cg (fun t => ((q4 ◇ (((q4 ◇ q7) ◇ q7) ◇ q5)) ◇ ((q4 ◇ q7) ◇ q6)) ◇ t) (cg (fun t => t ◇ q8) (cg (fun t => t ◇ q7) (apc2 q4 q5 q7 q6))))).symm).trans ((h ((q4 ◇ (((q4 ◇ q7) ◇ q7) ◇ q5)) ◇ ((q4 ◇ q7) ◇ q6)) q7 q8).symm)
  have apc5:=fun (q9 q10 q11 q12 q13:G)=>by
    exact ((cg (fun t => t ◇ q12) (cg (fun t => ((q9 ◇ (((q9 ◇ q12) ◇ q12) ◇ q10)) ◇ ((q9 ◇ q12) ◇ q11)) ◇ t) (cg (fun t => t ◇ q13) ((h q9 q12 q10).symm)))).symm).trans (apc4 q9 q10 q11 q12 q13)
  have apc6:=fun (q14 q15 q16 q17:G)=>by
    exact (((cg (fun t => t ◇ (q14 ◇ q17)) (apc2 q14 q15 (q14 ◇ q17) q16)).symm).trans (apc5 q14 q15 q16 (q14 ◇ q17) q17)).symm
  have apc7:=fun (q18 q19 q20:G)=>by
    exact (((((cg (fun t => t ◇ (((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20)) ◇ q19)) (cg (fun t => (q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ t) (cg (fun t => t ◇ q18) (cg (fun t => t ◇ ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20)) (apc1 q20 ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20) ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20)))))).trans (cg (fun t => t ◇ (((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20)) ◇ q19)) (cg (fun t => (q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ t) (cg (fun t => t ◇ q18) (cg (fun t => q20 ◇ t) (apc1 q20 ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20) ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20))))))).trans (cg (fun t => ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ ((q20 ◇ q20) ◇ q18)) ◇ t) (cg (fun t => t ◇ q19) (cg (fun t => (q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ t) (apc1 q20 ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20) ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20)))))).trans (cg (fun t => ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ ((q20 ◇ q20) ◇ q18)) ◇ t) (cg (fun t => t ◇ q19) (apc1 q20 ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20) ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20))))).symm).trans ((((cg (fun t => t ◇ (((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20)) ◇ q19)) (cg (fun t => (q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ t) (cg (fun t => t ◇ q18) (cg (fun t => t ◇ ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20)) (cg (fun t => (q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ t) (apc1 q20 q18 q18)))))).symm).trans (apc6 (q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) q18 q19 q20)).trans (((((cg (fun t => t ◇ ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20)) (cg (fun t => (q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ t) (cg (fun t => t ◇ q18) (cg (fun t => t ◇ ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20)) (cg (fun t => (q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ t) (apc1 q20 ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20) ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20))))))).trans (cg (fun t => t ◇ ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20)) (cg (fun t => (q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ t) (cg (fun t => t ◇ q18) (cg (fun t => t ◇ ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20)) (apc1 q20 ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20) ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20))))))).trans (cg (fun t => t ◇ ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20)) (cg (fun t => (q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ t) (cg (fun t => t ◇ q18) (cg (fun t => q20 ◇ t) (apc1 q20 ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20) ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20))))))).trans (cg (fun t => ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ ((q20 ◇ q20) ◇ q18)) ◇ t) (apc1 q20 ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20) ((q20 ◇ (((q20 ◇ q20) ◇ q20) ◇ q20)) ◇ q20)))).trans (apc2 q20 q20 q20 q18)))
  have apc8:=fun (q21 q22:G)=>by
    exact (((apc1 q21 ((q21 ◇ (((q21 ◇ q21) ◇ q21) ◇ q21)) ◇ q21) ((q21 ◇ (((q21 ◇ q21) ◇ q21) ◇ q21)) ◇ q21)).symm).trans (((cg (fun t => t ◇ q21) (apc7 q22 q21 q21)).symm).trans (apc5 q21 q21 q22 q21 q21))).symm
  have apc9:=fun (q23 q24:G)=>by
    exact ((((((cg (fun t => t ◇ (((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ ((q23 ◇ q23) ◇ q23))) ◇ q24)) (cg (fun t => (q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ t) (cg (fun t => t ◇ q23) (cg (fun t => t ◇ ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ ((q23 ◇ q23) ◇ q23))) (apc1 q23 ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ q23) ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ q23)))))).trans (cg (fun t => t ◇ (((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ ((q23 ◇ q23) ◇ q23))) ◇ q24)) (cg (fun t => (q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ t) (cg (fun t => t ◇ q23) (cg (fun t => q23 ◇ t) (apc8 q23 q23)))))).trans (cg (fun t => ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ ((q23 ◇ q23) ◇ q23)) ◇ t) (cg (fun t => t ◇ q24) (cg (fun t => (q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ t) (apc8 q23 q23))))).trans (cg (fun t => ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ ((q23 ◇ q23) ◇ q23)) ◇ t) (cg (fun t => t ◇ q24) (apc1 q23 ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ q23) ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ q23))))).trans (cg (fun t => t ◇ (q23 ◇ q24)) (apc8 q23 q23))).symm).trans ((((cg (fun t => t ◇ (((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ ((q23 ◇ q23) ◇ q23))) ◇ q24)) (cg (fun t => (q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ t) (cg (fun t => t ◇ q23) (cg (fun t => t ◇ ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ ((q23 ◇ q23) ◇ q23))) (cg (fun t => (q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ t) (apc8 q23 q23)))))).symm).trans (apc6 (q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) q23 q24 ((q23 ◇ q23) ◇ q23))).trans (((((cg (fun t => t ◇ ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ ((q23 ◇ q23) ◇ q23))) (cg (fun t => (q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ t) (cg (fun t => t ◇ q23) (cg (fun t => t ◇ ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ ((q23 ◇ q23) ◇ q23))) (cg (fun t => (q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ t) (apc8 q23 q23)))))).trans (cg (fun t => t ◇ ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ ((q23 ◇ q23) ◇ q23))) (cg (fun t => (q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ t) (cg (fun t => t ◇ q23) (cg (fun t => t ◇ ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ ((q23 ◇ q23) ◇ q23))) (apc1 q23 ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ q23) ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ q23))))))).trans (cg (fun t => t ◇ ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ ((q23 ◇ q23) ◇ q23))) (cg (fun t => (q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ t) (cg (fun t => t ◇ q23) (cg (fun t => q23 ◇ t) (apc8 q23 q23)))))).trans (cg (fun t => ((q23 ◇ (((q23 ◇ q23) ◇ q23) ◇ q23)) ◇ ((q23 ◇ q23) ◇ q23)) ◇ t) (apc8 q23 q23))).trans (cg (fun t => t ◇ q23) (apc8 q23 q23))))
  have apc10:=fun (q25:G)=>by
    exact ((cg (fun t => t ◇ q25) (apc9 q25 q25)).symm).trans ((((cg (fun t => t ◇ q25) (cg (fun t => t ◇ (q25 ◇ q25)) (apc8 q25 q25))).symm).trans (apc5 q25 q25 q25 q25 q25)).trans (apc8 q25 q25))
  have apc13:=fun (q26 q27 q28:G)=>by
    exact ((cg (fun t => t ◇ (q27 ◇ q26)) (cg (fun t => q27 ◇ t) (cg (fun t => t ◇ q28) (cg (fun t => t ◇ (q27 ◇ q26)) (apc9 q27 q26))))).symm).trans ((h q27 (q27 ◇ q26) q28).symm)
  have apc16:=fun (q14 q15 q16 q17 q23 q24:G)=>by
    exact ((((cg (fun t => t ◇ ((q14 ◇ (q14 ◇ q17)) ◇ q16)) (cg (fun t => q14 ◇ t) (cg (fun t => t ◇ q15) (cg (fun t => t ◇ (q14 ◇ q17)) (apc9 q14 q17))))).trans (cg (fun t => (q14 ◇ (((q14 ◇ q14) ◇ (q14 ◇ q17)) ◇ q15)) ◇ t) (cg (fun t => t ◇ q16) (apc9 q14 q17)))).symm).trans ((apc6 q14 q15 q16 q17).trans (cg (fun t => t ◇ (q14 ◇ q17)) (cg (fun t => q14 ◇ t) (cg (fun t => t ◇ q15) (cg (fun t => t ◇ (q14 ◇ q17)) (apc9 q14 q17))))))).trans (apc13 q17 q14 q15)
  have apc17:=fun (q29 q30 q31:G)=>by
    exact ((cg (fun t => (q30 ◇ (((q30 ◇ q30) ◇ (q30 ◇ q31)) ◇ q29)) ◇ t) (apc10 q30)).symm).trans (apc16 q30 q29 q30 q31 q29 q29)
  have apc18:=fun (q32 q33 q34:G)=>by
    exact (((cg (fun t => t ◇ q34) (apc16 q34 q32 q32 q33 ((q34 ◇ (((q34 ◇ q34) ◇ (q34 ◇ q33)) ◇ q32)) ◇ ((q34 ◇ q34) ◇ q32)) ((q34 ◇ (((q34 ◇ q34) ◇ (q34 ◇ q33)) ◇ q32)) ◇ ((q34 ◇ q34) ◇ q32)))).symm).trans (((cg (fun t => t ◇ q34) (cg (fun t => (q34 ◇ (((q34 ◇ q34) ◇ (q34 ◇ q33)) ◇ q32)) ◇ t) (cg (fun t => t ◇ q32) (cg (fun t => t ◇ q34) (apc17 q32 q34 q33))))).symm).trans ((h (q34 ◇ (((q34 ◇ q34) ◇ (q34 ◇ q33)) ◇ q32)) q34 q32).symm))).symm
  have apc19:=fun (q26 q27 q28 q32 q33 q34:G)=>by
    exact ((cg (fun t => t ◇ (q27 ◇ q26)) (apc18 q26 q26 q27)).symm).trans (apc13 q26 q27 q26)
  have apc21:=fun (q35 q36 q37:G)=>by
    exact (((cg (fun t => (q35 ◇ (((q35 ◇ q37) ◇ q37) ◇ q36)) ◇ t) ((h q35 q37 q36).symm)).symm).trans (apc9 (q35 ◇ (((q35 ◇ q37) ◇ q37) ◇ q36)) q37)).symm
  have apc22:=fun (q38 q39 q40:G)=>by
    exact ((cg (fun t => t ◇ (q38 ◇ (((q38 ◇ q40) ◇ q40) ◇ q39))) (apc21 q38 q39 q40)).symm).trans (apc10 (q38 ◇ (((q38 ◇ q40) ◇ q40) ◇ q39)))
  have apc28:=fun (q41 q42 q43 q44:G)=>by
    exact ((cg (fun t => t ◇ (((q42 ◇ q44) ◇ q44) ◇ q41)) (cg (fun t => (q42 ◇ (((q42 ◇ (((q42 ◇ q44) ◇ q44) ◇ q41)) ◇ (((q42 ◇ q44) ◇ q44) ◇ q41)) ◇ q43)) ◇ t) ((h q42 q44 q41).symm))).symm).trans (apc2 q42 q43 (((q42 ◇ q44) ◇ q44) ◇ q41) q44)
  have apc37:=fun (q45 q46 q47 q48 q49:G)=>by
    exact ((cg (fun t => t ◇ (((q46 ◇ q48) ◇ q48) ◇ q45)) (cg (fun t => t ◇ (q46 ◇ q49)) (cg (fun t => (q46 ◇ (((q46 ◇ (((q46 ◇ q48) ◇ q48) ◇ q45)) ◇ (((q46 ◇ q48) ◇ q48) ◇ q45)) ◇ q47)) ◇ t) ((h q46 q48 q45).symm)))).symm).trans (apc5 q46 q47 q48 (((q46 ◇ q48) ◇ q48) ◇ q45) q49)
  have apc38:=fun (q50 q51 q52 q53:G)=>by
    exact (((cg (fun t => t ◇ (((q51 ◇ q53) ◇ q53) ◇ q50)) (apc22 q51 q52 (((q51 ◇ q53) ◇ q53) ◇ q50))).symm).trans (apc37 q50 q51 q52 q53 (((q51 ◇ (((q51 ◇ q53) ◇ q53) ◇ q50)) ◇ (((q51 ◇ q53) ◇ q53) ◇ q50)) ◇ q52))).symm
  have apc39:=fun (q54 q55 q56 q57:G)=>by
    exact (((cg (fun t => (q55 ◇ (((q55 ◇ (((q55 ◇ q57) ◇ q57) ◇ q54)) ◇ (((q55 ◇ q57) ◇ q57) ◇ q54)) ◇ q56)) ◇ t) ((h q55 q57 q54).symm)).symm).trans (apc38 q54 q55 q56 q57)).symm
  have apc40:=fun (q58 q59 q60 q61:G)=>by
    exact ((apc39 q58 q60 q61 q59).symm).trans ((h q60 (((q60 ◇ q59) ◇ q59) ◇ q58) q61).symm)
  have apc41:=fun (q62 q63 q64 q65:G)=>by
    exact ((((cg (fun t => t ◇ q65) (apc21 q65 q64 (((q65 ◇ q63) ◇ q63) ◇ q62))).trans (cg (fun t => t ◇ q65) (apc40 q62 q63 q65 q64))).symm).trans (((cg (fun t => ((q65 ◇ (((q65 ◇ (((q65 ◇ q63) ◇ q63) ◇ q62)) ◇ (((q65 ◇ q63) ◇ q63) ◇ q62)) ◇ q64)) ◇ (q65 ◇ (((q65 ◇ (((q65 ◇ q63) ◇ q63) ◇ q62)) ◇ (((q65 ◇ q63) ◇ q63) ◇ q62)) ◇ q64))) ◇ t) (apc40 q62 q63 q65 q64)).symm).trans (apc19 q65 (q65 ◇ (((q65 ◇ (((q65 ◇ q63) ◇ q63) ◇ q62)) ◇ (((q65 ◇ q63) ◇ q63) ◇ q62)) ◇ q64)) q62 q62 q62 q62))).symm
  have apc47:=fun (q41 q42 q43 q44 q58 q59 q60 q61:G)=>by
    exact (((cg (fun t => t ◇ (((q42 ◇ q44) ◇ q44) ◇ q41)) (apc40 q41 q44 q42 q43)).symm).trans (apc28 q41 q42 q43 q44)).trans (apc41 q41 q44 q43 q42)
  have apc48:=fun (x y z q41 q42 q43 q44 q58 q59 q60 q61:G)=>by
    exact ((h x y x).trans (cg (fun t => t ◇ y) (apc47 x x (x ◇ (((x ◇ y) ◇ y) ◇ x)) y (x ◇ (((x ◇ y) ◇ y) ◇ x)) (x ◇ (((x ◇ y) ◇ y) ◇ x)) (x ◇ (((x ◇ y) ◇ y) ◇ x)) (x ◇ (((x ◇ y) ◇ y) ◇ x))))).symm
  have apc49:=fun (q66 q67:G)=>by
    exact ((cg (fun t => t ◇ q67) (apc48 q66 ((((q66 ◇ q66) ◇ q67) ◇ q67) ◇ q66) q66 q66 q66 q66 q66 q66 q66 q66 q66)).symm).trans ((h (q66 ◇ q66) q67 q66).symm)
  exact (calc
    (x ◇ y)=(x ◇ x):=apc49 x y
    _=(((x ◇ z) ◇ (w ◇ u)) ◇ x):=((cg (fun t => t ◇ x) (cg (fun t => t ◇ (w ◇ u)) (apc49 x z))).trans (cg (fun t => t ◇ x) (apc48 x (w ◇ u) ((x ◇ x) ◇ (w ◇ u)) ((x ◇ x) ◇ (w ◇ u)) ((x ◇ x) ◇ (w ◇ u)) ((x ◇ x) ◇ (w ◇ u)) ((x ◇ x) ◇ (w ◇ u)) ((x ◇ x) ◇ (w ◇ u)) ((x ◇ x) ◇ (w ◇ u)) ((x ◇ x) ◇ (w ◇ u)) ((x ◇ x) ◇ (w ◇ u))))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32791_to_51524 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_32791_to_51524
