-- Equation7721 → Equation5967
-- Recorded verdict: false
-- Premise: x = y ◇ (y ◇ ((y ◇ (x ◇ y)) ◇ y))
-- Conclusion: x = y ◇ (y ◇ (y ◇ ((x ◇ y) ◇ y)))
-- Original submission SHA-256: 1b8f0f5f849653bccb299286af32c3873e8a41e575d91c17bba9a71d96ced9c8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (y ◇ ((y ◇ (x ◇ y)) ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (y ◇ (y ◇ ((x ◇ y) ◇ y)))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   

set_option maxRecDepth 10000

namespace submission

inductive T where
  | g : Nat → T
  | p : T → T → T
deriving DecidableEq

namespace T

def sz : T → Nat
  | g _ => 0
  | p a b => sz a + sz b + 1

def H (owner tail : T) : T :=
  p owner (p (p owner tail) owner)

inductive Code : T → T → T → Prop
  | base (owner output : T) :
      Code owner (H owner (p output owner)) output
  | hit {owner output hitValue : T}
      (h : Code output owner hitValue) :
      Code owner (H owner hitValue) output

theorem code_spine {first second output : T}
    (h : Code first second output) :
    ∃ tail, second = H first tail := by
  cases h with
  | base owner output =>
      exact ⟨p output _, rfl⟩
  | @hit owner output hitValue h =>
      exact ⟨hitValue, rfl⟩

theorem code_cases {first second output : T}
    (h : Code first second output) :
    (second = H first (p output first)) ∨
    (∃ hitValue,
      second = H first hitValue ∧
      Code output first hitValue) := by
  cases h with
  | base owner output =>
      exact Or.inl rfl
  | @hit owner output hitValue h =>
      exact Or.inr ⟨hitValue, rfl, h⟩

theorem code_first_small {first second output : T}
    (h : Code first second output) :
    sz first < sz second := by
  rcases code_spine h with ⟨tail, rfl⟩
  simp [H, sz] <;> omega

theorem code_output_small {first second output : T}
    (h : Code first second output) :
    sz output < sz second := by
  cases h with
  | base owner output =>
      simp [H, sz] <;> omega
  | @hit owner output hitValue h =>
      have hsmall := code_first_small h
      simp [H, sz] at ⊢
      omega

theorem code_output_unique {first second output₁ output₂ : T}
    (h₁ : Code first second output₁)
    (h₂ : Code first second output₂) :
    output₁ = output₂ := by
  rcases code_cases h₁ with
      hbase₁ |
      ⟨hitValue₁, hhit₁, hrec₁⟩
  · rcases code_cases h₂ with
        hbase₂ |
        ⟨hitValue₂, hhit₂, hrec₂⟩
    · have houter :
          H first (p output₁ first) =
            H first (p output₂ first) :=
        hbase₁.symm.trans hbase₂
      have hright :=
        (p.inj houter).2
      have hmiddle :=
        (p.inj hright).1
      have htail :
          p output₁ first = p output₂ first :=
        (p.inj hmiddle).2
      exact (p.inj htail).1
    · have houter :
          H first (p output₁ first) =
            H first hitValue₂ :=
        hbase₁.symm.trans hhit₂
      have hright :=
        (p.inj houter).2
      have hmiddle :=
        (p.inj hright).1
      have htail :
          p output₁ first = hitValue₂ :=
        (p.inj hmiddle).2
      have hsmall := code_output_small hrec₂
      rw [← htail] at hsmall
      simp [sz] at hsmall <;> omega
  · rcases code_cases h₂ with
        hbase₂ |
        ⟨hitValue₂, hhit₂, hrec₂⟩
    · have houter :
          H first hitValue₁ =
            H first (p output₂ first) :=
        hhit₁.symm.trans hbase₂
      have hright :=
        (p.inj houter).2
      have hmiddle :=
        (p.inj hright).1
      have htail :
          hitValue₁ = p output₂ first :=
        (p.inj hmiddle).2
      have hsmall := code_output_small hrec₁
      rw [htail] at hsmall
      simp [sz] at hsmall <;> omega
    · rcases code_spine hrec₁ with
        ⟨tail₁, hshape₁⟩
      rcases code_spine hrec₂ with
        ⟨tail₂, hshape₂⟩
      have hshape :
          H output₁ tail₁ = H output₂ tail₂ :=
        hshape₁.symm.trans hshape₂
      exact (p.inj hshape).1

noncomputable def eval (first second : T) : T := by
  classical
  exact if h : ∃ output, Code first second output
    then Classical.choose h
    else p first second

theorem eval_hit {first second output : T}
    (h : Code first second output) :
    eval first second = output := by
  rw [eval, dif_pos ⟨output, h⟩]
  exact code_output_unique
    (Classical.choose_spec ⟨output, h⟩) h

theorem eval_raw {first second : T}
    (h : ¬ ∃ output, Code first second output) :
    eval first second = p first second := by
  simp [eval, h]

theorem no_code_same (q : T) :
    ¬ ∃ output, Code q q output := by
  rintro ⟨output, h⟩
  have hsmall := code_first_small h
  omega

theorem no_code_y_pairxy (x y : T) :
    ¬ ∃ output, Code y (p x y) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨tail, hshape⟩
  have hcycle :
      y = p (p y tail) y :=
    (p.inj hshape).2
  have hsize := congrArg sz hcycle
  simp [sz] at hsize <;> omega

theorem no_code_pair_first (owner tail : T) :
    ¬ ∃ output, Code (p owner tail) owner output := by
  rintro ⟨output, h⟩
  have hsmall := code_first_small h
  simp [sz] at hsmall <;> omega

theorem no_code_left_mismatch (owner tail : T) :
    ¬ ∃ output,
      Code owner (p (p owner tail) owner) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨codeTail, hshape⟩
  have hcycle :
      p owner tail = owner :=
    (p.inj hshape).1
  have hsize := congrArg sz hcycle
  simp [sz] at hsize <;> omega

theorem no_code_after_hit
    {x y hitValue : T}
    (h : Code x y hitValue) :
    ¬ ∃ output, Code y hitValue output := by
  rintro ⟨output, k⟩
  have hsmall := code_output_small h
  have ksmall := code_first_small k
  omega

theorem source_eval (x y : T) :
    eval y
      (eval y
        (eval
          (eval y (eval x y))
          y)) = x := by
  by_cases hcollision :
      ∃ hitValue, Code x y hitValue
  · let hitValue := Classical.choose hcollision
    have hhit : Code x y hitValue :=
      Classical.choose_spec hcollision
    rw [eval_hit hhit]
    rw [eval_raw (no_code_after_hit hhit)]
    rw [eval_raw (no_code_pair_first y hitValue)]
    rw [eval_raw (no_code_left_mismatch y hitValue)]
    exact eval_hit (Code.hit hhit)
  · rw [eval_raw hcollision]
    rw [eval_raw (no_code_y_pairxy x y)]
    rw [eval_raw (no_code_pair_first y (p x y))]
    rw [eval_raw (no_code_left_mismatch y (p x y))]
    exact eval_hit (Code.base y x)

noncomputable instance instMagma : Magma T where
  op := eval

theorem source_holds (x y : T) :
    x = y ◇ (y ◇ ((y ◇ (x ◇ y)) ◇ y)) := by
  change
    x =
      eval y
        (eval y
          (eval
            (eval y (eval x y))
            y))
  exact (source_eval x y).symm

def g0 : T := g 0
def t1 : T := p g0 g0
def t2 : T := p t1 g0
def t3 : T := p g0 t2
def t4 : T := p g0 t3
def t5 : T := p g0 t4

theorem no_code_H_atom :
    ¬ ∃ output, Code g0 (H g0 g0) output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      hbase |
      ⟨hitValue, hhit, hrec⟩
  · have hright :=
      (p.inj hbase).2
    have hmiddle :=
      (p.inj hright).1
    have hbad :
        g0 = p output g0 :=
      (p.inj hmiddle).2
    cases hbad
  · have hright :=
      (p.inj hhit).2
    have hmiddle :=
      (p.inj hright).1
    have hhitValue :
        g0 = hitValue :=
      (p.inj hmiddle).2
    subst hitValue
    have hsmall := code_first_small hrec
    simp [g0, sz] at hsmall

theorem no_code_outer_atom :
    ¬ ∃ output, Code g0 (p g0 (H g0 g0)) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨tail, hshape⟩
  have hright :
      H g0 g0 = p (p g0 tail) g0 :=
    (p.inj hshape).2
  have hbad :
      g0 = p g0 tail :=
    (p.inj hright).1
  cases hbad

theorem target_rhs_value :
    g0 ◇ (g0 ◇ (g0 ◇ ((g0 ◇ g0) ◇ g0))) = t5 := by
  change
    eval g0
      (eval g0
        (eval g0
          (eval (eval g0 g0) g0))) = t5
  rw [eval_raw (no_code_same g0)]
  rw [eval_raw (no_code_pair_first g0 g0)]
  rw [eval_raw (no_code_left_mismatch g0 g0)]
  change eval g0 (eval g0 (H g0 g0)) = t5
  rw [eval_raw no_code_H_atom]
  rw [eval_raw no_code_outer_atom]
  rfl

theorem bad5967 :
    g0 ≠ g0 ◇ (g0 ◇ (g0 ◇ ((g0 ◇ g0) ◇ g0))) := by
  rw [target_rhs_value]
  intro h
  cases h

end T

end submission

open submission

noncomputable def submission : Goal := by
  refine ⟨T, T.instMagma, ?_, ?_⟩
  · intro x y
    exact T.source_holds x y
  · intro target
    exact T.bad5967 (target T.g0 T.g0)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_7721_to_5967 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_7721_to_5967
