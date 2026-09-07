-- Equation6681 → Equation47
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ ((x ◇ z) ◇ (z ◇ y)))
-- Conclusion: x = x ◇ (x ◇ (x ◇ x))
-- Original submission SHA-256: 295389db45375edac1e92f5c1a282fe42c4b8c51c5f1dfacbda9a45edac8b757
-- Aurora-accepted correction SHA-256: 178751217891fc19c3c9203db74c793de644629f33ac66a75dfaf0337621ab5c
-- Generator: equational-challenges standalone v2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((x ◇ z) ◇ (z ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = x ◇ (x ◇ (x ◇ x))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

namespace Countermodel

def linA (x : BitVec 4) : BitVec 4 :=
  (if x.getLsbD 0 then 11#4 else 0#4) ^^^
  (if x.getLsbD 1 then 13#4 else 0#4) ^^^
  (if x.getLsbD 2 then 12#4 else 0#4) ^^^
  (if x.getLsbD 3 then 14#4 else 0#4)

def linB (x : BitVec 4) : BitVec 4 :=
  (if x.getLsbD 0 then 15#4 else 0#4) ^^^
  (if x.getLsbD 1 then 7#4 else 0#4) ^^^
  (if x.getLsbD 2 then 9#4 else 0#4) ^^^
  (if x.getLsbD 3 then 12#4 else 0#4)

def op (x y : BitVec 4) : BitVec 4 := linA x ^^^ linB y

instance instMagma : Magma (BitVec 4) where
  op := op

theorem source_holds : @EquationLHS (BitVec 4) instMagma := by
  intro x y z
  change x = op y (op x (op (op x z) (op z y)))
  simp only [op, linA, linB]
  decide +revert

theorem target_fails : ¬ @EquationRHS (BitVec 4) instMagma := by
  intro target
  have bad := target (1#4)
  change (1#4) = op (1#4) (op (1#4) (op (1#4) (1#4))) at bad
  simp [op, linA, linB] at bad

end Countermodel

def certificate : Goal :=
  ⟨BitVec 4, Countermodel.instMagma,
    Countermodel.source_holds, Countermodel.target_fails⟩

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6681_to_47 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_6681_to_47
