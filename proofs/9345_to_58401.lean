-- Equation9345 → Equation58401
-- Recorded verdict: false
-- Premise: x = y * ((x * y) * (z * (y * y)))
-- Conclusion: (x * y) * x = x * (x * (z * x))
-- Original submission SHA-256: 2c9d1063d1c64f42e320f98edc75cb7bb0e1e9e1e970955a787d6ec374c06ad4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ y) ◇ (z ◇ (y ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = x ◇ (x ◇ (z ◇ x))
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

inductive Code : T → T → T → Prop
  | base (output owner z : T) :
      Code owner
        (p (p output owner)
          (p z (p owner owner))) output
  | hit {output owner z hitValue : T}
      (h : Code output owner hitValue) :
      Code owner
        (p hitValue
          (p z (p owner owner))) output

theorem code_tail {first second output : T}
    (h : Code first second output) :
    ∃ head z,
      second = p head (p z (p first first)) := by
  cases h with
  | base output owner z =>
      exact ⟨p output _, z, rfl⟩
  | @hit output owner z hitValue h =>
      exact ⟨hitValue, z, rfl⟩

theorem code_cases {first second output : T}
    (h : Code first second output) :
    (∃ z,
      second =
        p (p output first)
          (p z (p first first))) ∨
    (∃ z hitValue,
      second =
          p hitValue (p z (p first first)) ∧
        Code output first hitValue) := by
  cases h with
  | base output owner z =>
      exact Or.inl ⟨z, rfl⟩
  | @hit output owner z hitValue h =>
      exact Or.inr ⟨z, hitValue, rfl, h⟩

theorem code_first_small {first second output : T}
    (h : Code first second output) :
    sz first < sz second := by
  rcases code_tail h with ⟨head, z, rfl⟩
  simp [sz] <;> omega

theorem code_output_small {first second output : T}
    (h : Code first second output) :
    sz output < sz second := by
  cases h with
  | base output owner z =>
      simp [sz] <;> omega
  | @hit output owner z hitValue h =>
      have hsmall := code_first_small h
      simp [sz] <;> omega

theorem code_first_unique
    {first₁ first₂ second output : T}
    (h₁ : Code first₁ second output)
    (h₂ : Code first₂ second output) :
    first₁ = first₂ := by
  rcases code_tail h₁ with ⟨head₁, z₁, hshape₁⟩
  rcases code_tail h₂ with ⟨head₂, z₂, hshape₂⟩
  have htail :
      p z₁ (p first₁ first₁) =
        p z₂ (p first₂ first₂) :=
    (p.inj (hshape₁.symm.trans hshape₂)).2
  exact (p.inj (p.inj htail).2).1

theorem code_output_unique
    {first second output₁ output₂ : T}
    (h₁ : Code first second output₁)
    (h₂ : Code first second output₂) :
    output₁ = output₂ := by
  rcases code_cases h₁ with
      ⟨z₁, hbase₁⟩ |
      ⟨z₁, hitValue₁, hhit₁, hrec₁⟩
  · rcases code_cases h₂ with
        ⟨z₂, hbase₂⟩ |
        ⟨z₂, hitValue₂, hhit₂, hrec₂⟩
    · have hhead :
          p output₁ first = p output₂ first :=
        (p.inj (hbase₁.symm.trans hbase₂)).1
      exact (p.inj hhead).1
    · have hhead :
          p output₁ first = hitValue₂ :=
        (p.inj (hbase₁.symm.trans hhit₂)).1
      have hsmall := code_output_small hrec₂
      rw [← hhead] at hsmall
      simp [sz] at hsmall <;> omega
  · rcases code_cases h₂ with
        ⟨z₂, hbase₂⟩ |
        ⟨z₂, hitValue₂, hhit₂, hrec₂⟩
    · have hhead :
          hitValue₁ = p output₂ first :=
        (p.inj (hhit₁.symm.trans hbase₂)).1
      have hsmall := code_output_small hrec₁
      rw [hhead] at hsmall
      simp [sz] at hsmall <;> omega
    · have hhead : hitValue₁ = hitValue₂ :=
        (p.inj (hhit₁.symm.trans hhit₂)).1
      subst hitValue₂
      exact code_first_unique hrec₁ hrec₂

theorem no_code_if_second_le_first {first second : T}
    (hsize : sz second ≤ sz first) :
    ¬ ∃ output, Code first second output := by
  rintro ⟨output, h⟩
  have hsmall := code_first_small h
  omega

theorem no_code_same (q : T) :
    ¬ ∃ output, Code q q output :=
  no_code_if_second_le_first (Nat.le_refl _)

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

theorem no_code_square_tail (first owner : T) :
    ¬ ∃ output, Code first (p owner owner) output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨z, hshape⟩ |
      ⟨z, hitValue, hshape, hrec⟩
  · have hleft :
        owner = p output first :=
      (p.inj hshape).1
    have hright :
        owner = p z (p first first) :=
      (p.inj hshape).2
    have hcycle :
        first = p first first :=
      (p.inj (hleft.symm.trans hright)).2
    have hsize := congrArg sz hcycle
    simp [sz] at hsize <;> omega
  · have hhit : owner = hitValue :=
      (p.inj hshape).1
    have hright :
        owner = p z (p first first) :=
      (p.inj hshape).2
    have hsmall := code_output_small hrec
    rw [← hhit, hright] at hsmall
    simp [sz] at hsmall <;> omega

theorem no_code_raw_middle (x owner z : T) :
    ¬ ∃ output,
      Code (p x owner)
        (p z (p owner owner)) output := by
  rintro ⟨output, h⟩
  rcases code_tail h with ⟨head, tail, hshape⟩
  have hright :
      p owner owner =
        p tail (p (p x owner) (p x owner)) :=
    (p.inj hshape).2
  have hcycle :
      owner = p (p x owner) (p x owner) :=
    (p.inj hright).2
  have hsize := congrArg sz hcycle
  simp [sz] at hsize <;> omega

theorem code_second_ne_double_output
    {x owner hitValue : T}
    (h : Code x owner hitValue) :
    owner ≠ p hitValue hitValue := by
  intro hdouble
  rcases code_cases h with
      ⟨z, hshape⟩ |
      ⟨z, recValue, hshape, hrec⟩
  · rw [hdouble] at hshape
    have hleft :
        hitValue = p hitValue x :=
      (p.inj hshape).1
    have hsize := congrArg sz hleft
    simp [sz] at hsize <;> omega
  · rw [hdouble] at hshape
    have hvalue : hitValue = recValue :=
      (p.inj hshape).1
    have hright :
        hitValue = p z (p x x) :=
      (p.inj hshape).2
    subst recValue
    have hsmall := code_first_small hrec
    rw [hright] at hsmall
    simp [sz] at hsmall <;> omega

theorem no_code_after_hit_middle
    {x owner hitValue : T}
    (h : Code x owner hitValue) (z : T) :
    ¬ ∃ output,
      Code hitValue
        (p z (p owner owner)) output := by
  rintro ⟨output, k⟩
  rcases code_tail k with ⟨head, tail, hshape⟩
  have hright :
      p owner owner =
        p tail (p hitValue hitValue) :=
    (p.inj hshape).2
  have hdouble :
      owner = p hitValue hitValue :=
    (p.inj hright).2
  exact code_second_ne_double_output h hdouble

theorem source_eval (x owner z : T) :
    eval owner
      (eval (eval x owner)
        (eval z (eval owner owner))) = x := by
  rw [eval_raw (no_code_same owner)]
  rw [eval_raw (no_code_square_tail z owner)]
  by_cases hcollision :
      ∃ hitValue, Code x owner hitValue
  · let hitValue := Classical.choose hcollision
    have hhit : Code x owner hitValue :=
      Classical.choose_spec hcollision
    rw [eval_hit hhit]
    rw [eval_raw (no_code_after_hit_middle hhit z)]
    exact eval_hit (Code.hit hhit)
  · rw [eval_raw hcollision]
    rw [eval_raw (no_code_raw_middle x owner z)]
    exact eval_hit (Code.base x owner z)

noncomputable instance instMagma : Magma T where
  op := eval

theorem source_holds (x y z : T) :
    x = y ◇ ((x ◇ y) ◇ (z ◇ (y ◇ y))) := by
  change
    x =
      eval y
        (eval (eval x y)
          (eval z (eval y y)))
  exact (source_eval x y z).symm

def g0 : T := g 0
def q : T := p g0 g0
def leftValue : T := p q g0
def innerRight : T := p g0 q
def rightValue : T := p g0 innerRight

theorem gg_value : eval g0 g0 = q := by
  exact eval_raw (no_code_same g0)

theorem qg_value : eval q g0 = leftValue := by
  apply eval_raw
  apply no_code_if_second_le_first
  simp [q, g0, sz]

theorem gq_value : eval g0 q = innerRight := by
  exact eval_raw (no_code_square_tail g0 g0)

theorem no_code_g0_innerRight :
    ¬ ∃ output, Code g0 innerRight output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨z, hshape⟩ |
      ⟨z, hitValue, hshape, hrec⟩
  · have hleft :
        g0 = p output g0 := by
      simpa [innerRight, q] using (p.inj hshape).1
    cases hleft
  · have hhit : g0 = hitValue := by
      simpa [innerRight, q] using (p.inj hshape).1
    subst hitValue
    exact no_code_if_second_le_first
      (first := output) (second := g0)
      (by simp [g0, sz]) ⟨g0, hrec⟩

theorem g_inner_value :
    eval g0 innerRight = rightValue := by
  exact eval_raw no_code_g0_innerRight

theorem target_left_value :
    (g0 ◇ g0) ◇ g0 = leftValue := by
  change eval (eval g0 g0) g0 = leftValue
  rw [gg_value]
  exact qg_value

theorem target_right_value :
    g0 ◇ (g0 ◇ (g0 ◇ g0)) = rightValue := by
  change eval g0 (eval g0 (eval g0 g0)) = rightValue
  rw [gg_value, gq_value]
  exact g_inner_value

theorem bad58401 :
    (g0 ◇ g0) ◇ g0 ≠
      g0 ◇ (g0 ◇ (g0 ◇ g0)) := by
  rw [target_left_value, target_right_value]
  intro h
  cases h

end T

end submission

open submission

noncomputable def submission : Goal := by
  refine ⟨T, T.instMagma, ?_, ?_⟩
  · intro x y z
    exact T.source_holds x y z
  · intro target
    exact T.bad58401 (target T.g0 T.g0 T.g0)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_9345_to_58401 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_9345_to_58401
