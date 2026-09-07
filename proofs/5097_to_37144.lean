-- Equation5097 → Equation37144
-- Recorded verdict: false
-- Premise: x = y ◇ (y ◇ (y ◇ (y ◇ (x ◇ y))))
-- Conclusion: x = ((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ x
-- Original submission SHA-256: 11b053f2061055d55e3abd5cdf13db0ac0e1670b9c27b5266384511a52a8d6a5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (y ◇ (y ◇ (y ◇ (x ◇ y))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = ((x ◇ (x ◇ (x ◇ x))) ◇ x) ◇ x
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
  | base (output owner : T) :
      Code owner
        (p owner
          (p owner
            (p owner (p output owner)))) output
  | hit {output owner hitValue : T}
      (h : Code output owner hitValue) :
      Code owner
        (p owner
          (p owner
            (p owner hitValue))) output

theorem code_spine {first second output : T}
    (h : Code first second output) :
    ∃ tail,
      second =
        p first (p first (p first tail)) := by
  cases h with
  | base output owner =>
      exact ⟨p output _, rfl⟩
  | @hit output owner hitValue h =>
      exact ⟨hitValue, rfl⟩

theorem code_cases {first second output : T}
    (h : Code first second output) :
    (second =
      p first
        (p first
          (p first (p output first)))) ∨
    (∃ hitValue,
      second =
          p first
            (p first
              (p first hitValue)) ∧
        Code output first hitValue) := by
  cases h with
  | base output owner =>
      exact Or.inl rfl
  | @hit output owner hitValue h =>
      exact Or.inr ⟨hitValue, rfl, h⟩

theorem code_first_small {first second output : T}
    (h : Code first second output) :
    sz first < sz second := by
  rcases code_spine h with ⟨tail, rfl⟩
  simp [sz] <;> omega

theorem code_output_small {first second output : T}
    (h : Code first second output) :
    sz output < sz second := by
  cases h with
  | base output owner =>
      simp [sz] <;> omega
  | @hit output owner hitValue h =>
      have hsmall := code_first_small h
      simp [sz] <;> omega

theorem code_first_unique
    {first₁ first₂ second output : T}
    (h₁ : Code first₁ second output)
    (h₂ : Code first₂ second output) :
    first₁ = first₂ := by
  rcases code_spine h₁ with ⟨tail₁, hshape₁⟩
  rcases code_spine h₂ with ⟨tail₂, hshape₂⟩
  exact (p.inj (hshape₁.symm.trans hshape₂)).1

theorem code_output_unique
    {first second output₁ output₂ : T}
    (h₁ : Code first second output₁)
    (h₂ : Code first second output₂) :
    output₁ = output₂ := by
  rcases code_cases h₁ with
      hbase₁ |
      ⟨hitValue₁, hhit₁, hrec₁⟩
  · rcases code_cases h₂ with
        hbase₂ |
        ⟨hitValue₂, hhit₂, hrec₂⟩
    · have htail :
          p output₁ first = p output₂ first :=
        (p.inj
          (p.inj
            (p.inj
              (hbase₁.symm.trans hbase₂)).2).2).2
      exact (p.inj htail).1
    · have htail :
          p output₁ first = hitValue₂ :=
        (p.inj
          (p.inj
            (p.inj
              (hbase₁.symm.trans hhit₂)).2).2).2
      have hsmall := code_output_small hrec₂
      rw [← htail] at hsmall
      simp [sz] at hsmall <;> omega
  · rcases code_cases h₂ with
        hbase₂ |
        ⟨hitValue₂, hhit₂, hrec₂⟩
    · have htail :
          hitValue₁ = p output₂ first :=
        (p.inj
          (p.inj
            (p.inj
              (hhit₁.symm.trans hbase₂)).2).2).2
      have hsmall := code_output_small hrec₁
      rw [htail] at hsmall
      simp [sz] at hsmall <;> omega
    · have htail : hitValue₁ = hitValue₂ :=
        (p.inj
          (p.inj
            (p.inj
              (hhit₁.symm.trans hhit₂)).2).2).2
      subst hitValue₂
      exact code_first_unique hrec₁ hrec₂

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

theorem no_code_after_inner_hit
    {x y hitValue : T}
    (h : Code x y hitValue) :
    ¬ ∃ output, Code y hitValue output := by
  rintro ⟨output, k⟩
  have hsmall := code_output_small h
  have ksmall := code_first_small k
  omega

theorem no_code_level1_after_inner_hit
    {x y hitValue : T}
    (h : Code x y hitValue) :
    ¬ ∃ output, Code y (p y hitValue) output := by
  rintro ⟨output, k⟩
  rcases code_spine k with ⟨tail, hshape⟩
  have hhit :
      hitValue = p y (p y tail) :=
    (p.inj hshape).2
  have hsmall := code_output_small h
  rw [hhit] at hsmall
  simp [sz] at hsmall <;> omega

theorem no_code_level2_after_inner_hit
    {x y hitValue : T}
    (h : Code x y hitValue) :
    ¬ ∃ output,
      Code y (p y (p y hitValue)) output := by
  rintro ⟨output, k⟩
  rcases code_spine k with ⟨tail, hshape⟩
  have hlevel1 :
      p y hitValue = p y (p y tail) :=
    (p.inj hshape).2
  have hhit : hitValue = p y tail :=
    (p.inj hlevel1).2
  have hsmall := code_output_small h
  rw [hhit] at hsmall
  simp [sz] at hsmall <;> omega

theorem no_code_y_raw_inner (x y : T) :
    ¬ ∃ output, Code y (p x y) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨tail, hshape⟩
  have hx : x = y :=
    (p.inj hshape).1
  have hy :
      y = p y (p y tail) :=
    (p.inj hshape).2
  have hsize := congrArg sz hy
  simp [sz] at hsize <;> omega

theorem no_code_y_raw_level1 (x y : T) :
    ¬ ∃ output,
      Code y (p y (p x y)) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨tail, hshape⟩
  have hright :
      p x y = p y (p y tail) :=
    (p.inj hshape).2
  have hx : x = y :=
    (p.inj hright).1
  have hy : y = p y tail :=
    (p.inj hright).2
  have hsize := congrArg sz hy
  simp [sz] at hsize <;> omega

theorem no_code_y_raw_level2 (x y : T) :
    ¬ ∃ output,
      Code y (p y (p y (p x y))) output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      hbase |
      ⟨hitValue, hhit, hrec⟩
  · have hlevel1 :
        p y (p x y) =
          p y (p y (p output y)) :=
      (p.inj hbase).2
    have hlevel2 :
        p x y = p y (p output y) :=
      (p.inj hlevel1).2
    have hy : y = p output y :=
      (p.inj hlevel2).2
    have hsize := congrArg sz hy
    simp [sz] at hsize <;> omega
  · have hlevel1 :
        p y (p x y) =
          p y (p y hitValue) :=
      (p.inj hhit).2
    have hlevel2 :
        p x y = p y hitValue :=
      (p.inj hlevel1).2
    have hy : y = hitValue :=
      (p.inj hlevel2).2
    have hsmall := code_output_small hrec
    rw [← hy] at hsmall
    omega

theorem source_eval (x y : T) :
    eval y
      (eval y
        (eval y
          (eval y (eval x y)))) = x := by
  by_cases hcollision :
      ∃ hitValue, Code x y hitValue
  · let hitValue := Classical.choose hcollision
    have hhit : Code x y hitValue :=
      Classical.choose_spec hcollision
    rw [eval_hit hhit]
    rw [eval_raw (no_code_after_inner_hit hhit)]
    rw [eval_raw (no_code_level1_after_inner_hit hhit)]
    rw [eval_raw (no_code_level2_after_inner_hit hhit)]
    exact eval_hit (Code.hit hhit)
  · rw [eval_raw hcollision]
    rw [eval_raw (no_code_y_raw_inner x y)]
    rw [eval_raw (no_code_y_raw_level1 x y)]
    rw [eval_raw (no_code_y_raw_level2 x y)]
    exact eval_hit (Code.base x y)

noncomputable instance instMagma : Magma T where
  op := eval

theorem source_holds (x y : T) :
    x = y ◇ (y ◇ (y ◇ (y ◇ (x ◇ y)))) := by
  change
    x =
      eval y
        (eval y
          (eval y
            (eval y (eval x y))))
  exact (source_eval x y).symm

def x0 : T := g 0
def p1 : T := p x0 x0
def p2 : T := p x0 p1
def p3 : T := p x0 p2
def p4 : T := p p3 x0
def targetValue : T := p p4 x0

theorem no_code_second_atom (first : T) (index : Nat) :
    ¬ ∃ output, Code first (g index) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨tail, hshape⟩
  cases hshape

theorem no_code_target_p1 :
    ¬ ∃ output, Code x0 p1 output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨tail, hshape⟩
  have hright :
      x0 = p x0 (p x0 tail) :=
    (p.inj hshape).2
  cases hright

theorem no_code_target_p2 :
    ¬ ∃ output, Code x0 p2 output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨tail, hshape⟩
  have hright1 :
      p x0 x0 = p x0 (p x0 tail) :=
    (p.inj hshape).2
  have hright2 :
      x0 = p x0 tail :=
    (p.inj hright1).2
  cases hright2

theorem target_rhs_value :
    ((x0 ◇ (x0 ◇ (x0 ◇ x0))) ◇ x0) ◇ x0 =
      targetValue := by
  change
    eval
      (eval x0
        (eval x0
          (eval x0 x0)))
      x0 ◇ x0 = targetValue
  have h₁ : eval x0 x0 = p1 := by
    exact eval_raw (no_code_second_atom x0 0)
  rw [h₁]
  have h₂ : eval x0 p1 = p2 := by
    exact eval_raw no_code_target_p1
  rw [h₂]
  have h₃ : eval x0 p2 = p3 := by
    exact eval_raw no_code_target_p2
  rw [h₃]
  have h₄ : eval p3 x0 = p4 := by
    exact eval_raw (no_code_second_atom p3 0)
  rw [h₄]
  exact eval_raw (no_code_second_atom p4 0)

theorem bad37144 :
    x0 ≠ ((x0 ◇ (x0 ◇ (x0 ◇ x0))) ◇ x0) ◇ x0 := by
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
    exact T.bad37144 (target T.x0)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5097_to_37144 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_5097_to_37144
