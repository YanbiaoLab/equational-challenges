-- Equation5141 → Equation33945
-- Recorded verdict: false
-- Premise: x = y * (y * (z * (y * (x * y))))
-- Conclusion: x = ((y * x) * (z * (y * w))) * w
-- Original submission SHA-256: 827b9f6be998301a12a7eadbc1a0721a7d41ac3ac87fc5a8d0c2d1df540844a5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (y ◇ (z ◇ (y ◇ (x ◇ y))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ x) ◇ (z ◇ (y ◇ w))) ◇ w
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
  | base (output owner parameter : T) :
      Code owner
        (p owner
          (p parameter
            (p owner (p output owner)))) output
  | hit {output owner parameter hitValue : T}
      (h : Code output owner hitValue) :
      Code owner
        (p owner
          (p parameter
            (p owner hitValue))) output

theorem code_spine {first second output : T}
    (h : Code first second output) :
    ∃ parameter tail,
      second =
        p first (p parameter (p first tail)) := by
  cases h with
  | base output owner parameter =>
      exact ⟨parameter, p output _, rfl⟩
  | @hit output owner parameter hitValue h =>
      exact ⟨parameter, hitValue, rfl⟩

theorem code_cases {first second output : T}
    (h : Code first second output) :
    (∃ parameter,
      second =
        p first
          (p parameter
            (p first (p output first)))) ∨
    (∃ parameter hitValue,
      second =
          p first
            (p parameter
              (p first hitValue)) ∧
        Code output first hitValue) := by
  cases h with
  | base output owner parameter =>
      exact Or.inl ⟨parameter, rfl⟩
  | @hit output owner parameter hitValue h =>
      exact Or.inr ⟨parameter, hitValue, rfl, h⟩

theorem code_first_small {first second output : T}
    (h : Code first second output) :
    sz first < sz second := by
  rcases code_spine h with ⟨parameter, tail, rfl⟩
  simp [sz] <;> omega

theorem code_output_small {first second output : T}
    (h : Code first second output) :
    sz output < sz second := by
  cases h with
  | base output owner parameter =>
      simp [sz] <;> omega
  | @hit output owner parameter hitValue h =>
      have hsmall := code_first_small h
      simp [sz] <;> omega

theorem code_first_unique
    {first₁ first₂ second output : T}
    (h₁ : Code first₁ second output)
    (h₂ : Code first₂ second output) :
    first₁ = first₂ := by
  rcases code_spine h₁ with
    ⟨parameter₁, tail₁, hshape₁⟩
  rcases code_spine h₂ with
    ⟨parameter₂, tail₂, hshape₂⟩
  exact
    (p.inj (hshape₁.symm.trans hshape₂)).1

theorem code_output_unique
    {first second output₁ output₂ : T}
    (h₁ : Code first second output₁)
    (h₂ : Code first second output₂) :
    output₁ = output₂ := by
  rcases code_cases h₁ with
      ⟨parameter₁, hbase₁⟩ |
      ⟨parameter₁, hitValue₁, hhit₁, hrec₁⟩
  · rcases code_cases h₂ with
        ⟨parameter₂, hbase₂⟩ |
        ⟨parameter₂, hitValue₂, hhit₂, hrec₂⟩
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
        ⟨parameter₂, hbase₂⟩ |
        ⟨parameter₂, hitValue₂, hhit₂, hrec₂⟩
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

theorem no_code_z_after_inner_hit
    {x y hitValue : T}
    (h : Code x y hitValue) (z : T) :
    ¬ ∃ output, Code z (p y hitValue) output := by
  rintro ⟨output, k⟩
  rcases code_spine k with
    ⟨parameter, tail, hshape⟩
  have hz : y = z :=
    (p.inj hshape).1
  have hhit :
      hitValue = p parameter (p z tail) :=
    (p.inj hshape).2
  have hsmall := code_output_small h
  rw [hz, hhit] at hsmall
  simp [sz] at hsmall <;> omega

theorem no_code_y_after_inner_hit
    {x y hitValue : T}
    (h : Code x y hitValue) (z : T) :
    ¬ ∃ output,
      Code y (p z (p y hitValue)) output := by
  rintro ⟨output, k⟩
  rcases code_spine k with
    ⟨parameter, tail, hshape⟩
  have hz : z = y :=
    (p.inj hshape).1
  have hright :
      p y hitValue =
        p parameter (p y tail) :=
    (p.inj hshape).2
  have hhit : hitValue = p y tail :=
    (p.inj hright).2
  have hsmall := code_output_small h
  rw [hhit] at hsmall
  simp [sz] at hsmall <;> omega

theorem no_code_y_raw_inner (x y : T) :
    ¬ ∃ output, Code y (p x y) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with
    ⟨parameter, tail, hshape⟩
  have hx : x = y :=
    (p.inj hshape).1
  have hy :
      y = p parameter (p y tail) :=
    (p.inj hshape).2
  have hsize := congrArg sz hy
  simp [sz] at hsize <;> omega

theorem no_code_z_raw_inner (x y z : T) :
    ¬ ∃ output,
      Code z (p y (p x y)) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with
    ⟨parameter, tail, hshape⟩
  have hz : y = z :=
    (p.inj hshape).1
  have hright :
      p x y =
        p parameter (p z tail) :=
    (p.inj hshape).2
  have hy : y = p z tail :=
    (p.inj hright).2
  rw [← hz] at hy
  have hsize := congrArg sz hy
  simp [sz] at hsize <;> omega

theorem no_code_y_raw_spine (x y z : T) :
    ¬ ∃ output,
      Code y
        (p z (p y (p x y))) output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨parameter, hshape⟩ |
      ⟨parameter, hitValue, hshape, hrec⟩
  · have hz : z = y :=
      (p.inj hshape).1
    have hlevel1 :
        p y (p x y) =
          p parameter
            (p y (p output y)) :=
      (p.inj hshape).2
    have hlevel2 :
        p x y = p y (p output y) :=
      (p.inj hlevel1).2
    have hy : y = p output y :=
      (p.inj hlevel2).2
    have hsize := congrArg sz hy
    simp [sz] at hsize <;> omega
  · have hz : z = y :=
      (p.inj hshape).1
    have hlevel1 :
        p y (p x y) =
          p parameter (p y hitValue) :=
      (p.inj hshape).2
    have hlevel2 :
        p x y = p y hitValue :=
      (p.inj hlevel1).2
    have hhit : y = hitValue :=
      (p.inj hlevel2).2
    have hsmall := code_output_small hrec
    rw [← hhit] at hsmall
    omega

theorem source_eval (x y z : T) :
    eval y
      (eval y
        (eval z
          (eval y (eval x y)))) = x := by
  by_cases hcollision :
      ∃ hitValue, Code x y hitValue
  · let hitValue := Classical.choose hcollision
    have hhit : Code x y hitValue :=
      Classical.choose_spec hcollision
    rw [eval_hit hhit]
    rw [eval_raw (no_code_after_inner_hit hhit)]
    rw [eval_raw (no_code_z_after_inner_hit hhit z)]
    rw [eval_raw (no_code_y_after_inner_hit hhit z)]
    exact eval_hit (Code.hit hhit)
  · rw [eval_raw hcollision]
    rw [eval_raw (no_code_y_raw_inner x y)]
    rw [eval_raw (no_code_z_raw_inner x y z)]
    rw [eval_raw (no_code_y_raw_spine x y z)]
    exact eval_hit (Code.base x y z)

noncomputable instance instMagma : Magma T where
  op := eval

theorem source_holds (x y z : T) :
    x = y ◇ (y ◇ (z ◇ (y ◇ (x ◇ y)))) := by
  change
    x =
      eval y
        (eval y
          (eval z
            (eval y (eval x y))))
  exact (source_eval x y z).symm

def x0 : T := g 0
def y0 : T := g 1
def z0 : T := g 2
def w0 : T := g 3
def yx : T := p y0 x0
def yw : T := p y0 w0
def zyw : T := p z0 yw
def middle : T := p yx zyw
def targetValue : T := p middle w0

theorem no_code_second_atom (first : T) (index : Nat) :
    ¬ ∃ output, Code first (g index) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with
    ⟨parameter, tail, hshape⟩
  cases hshape

theorem no_code_bad_head
    {first left right : T}
    (hbad : left ≠ first) :
    ¬ ∃ output, Code first (p left right) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with
    ⟨parameter, tail, hshape⟩
  exact hbad ((p.inj hshape).1)

theorem target_rhs_value :
    ((y0 ◇ x0) ◇ (z0 ◇ (y0 ◇ w0))) ◇ w0 =
      targetValue := by
  change
    eval
      (eval (eval y0 x0)
        (eval z0 (eval y0 w0)))
      w0 = targetValue
  have h₁ : eval y0 x0 = yx := by
    exact eval_raw (no_code_second_atom y0 0)
  rw [h₁]
  have h₂ : eval y0 w0 = yw := by
    exact eval_raw (no_code_second_atom y0 3)
  rw [h₂]
  have hyz : y0 ≠ z0 := by
    intro h
    cases h
  have h₃ : eval z0 yw = zyw := by
    exact eval_raw (no_code_bad_head hyz)
  rw [h₃]
  have hzmiddle : z0 ≠ yx := by
    intro h
    cases h
  have h₄ : eval yx zyw = middle := by
    exact eval_raw (no_code_bad_head hzmiddle)
  rw [h₄]
  exact eval_raw (no_code_second_atom middle 3)

theorem bad33945 :
    x0 ≠ ((y0 ◇ x0) ◇ (z0 ◇ (y0 ◇ w0))) ◇ w0 := by
  rw [target_rhs_value]
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
    exact
      T.bad33945
        (target T.x0 T.y0 T.z0 T.w0)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5141_to_33945 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_5141_to_33945
