-- Equation883 → Equation2304
-- Recorded verdict: false
-- Premise: x = y ◇ ((x ◇ y) ◇ (y ◇ y))
-- Conclusion: x = (y ◇ (x ◇ (y ◇ y))) ◇ y
-- Original submission SHA-256: 3593dadc544728201e6689866e608d8a606d620fed106157cd5bff88b22cbbc0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ ((x ◇ y) ◇ (y ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ (x ◇ (y ◇ y))) ◇ y
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
      Code owner (p (p output owner) (p owner owner)) output
  | hit {output owner hitValue : T}
      (h : Code output owner hitValue) :
      Code owner (p hitValue (p owner owner)) output

theorem owner_tail {left right output : T}
    (h : Code left right output) :
    ∃ head, right = p head (p left left) := by
  cases h with
  | base output _ =>
      exact ⟨p output _, rfl⟩
  | @hit _ _ hitValue _ =>
      exact ⟨hitValue, rfl⟩

theorem code_left_unique
    {left₁ left₂ right output₁ output₂ : T}
    (h₁ : Code left₁ right output₁)
    (h₂ : Code left₂ right output₂) :
    left₁ = left₂ := by
  rcases owner_tail h₁ with ⟨head₁, hshape₁⟩
  rcases owner_tail h₂ with ⟨head₂, hshape₂⟩
  have htail :
      p left₁ left₁ = p left₂ left₂ :=
    (p.inj (hshape₁.symm.trans hshape₂)).2
  exact (p.inj htail).1

theorem code_first_small {left right output : T}
    (h : Code left right output) :
    sz left < sz right := by
  rcases owner_tail h with ⟨head, rfl⟩
  simp [sz] <;> omega

theorem code_output_small {left right output : T}
    (h : Code left right output) :
    sz output < sz right := by
  cases h with
  | base output owner =>
      simp [sz] <;> omega
  | @hit output owner hitValue h =>
      have hsmall := code_first_small h
      simp [sz] at hsmall ⊢ <;> omega

theorem code_cases {left right output : T}
    (h : Code left right output) :
    right = p (p output left) (p left left) ∨
      ∃ hitValue,
        right = p hitValue (p left left) ∧
          Code output left hitValue := by
  cases h with
  | base output owner =>
      exact Or.inl rfl
  | @hit output owner hitValue h =>
      exact Or.inr ⟨hitValue, rfl, h⟩

theorem code_output_unique {left right output₁ output₂ : T}
    (h₁ : Code left right output₁)
    (h₂ : Code left right output₂) :
    output₁ = output₂ := by
  rcases code_cases h₁ with hbase₁ | ⟨hitValue₁, hhit₁, hrec₁⟩
  · rcases code_cases h₂ with hbase₂ | ⟨hitValue₂, hhit₂, hrec₂⟩
    · have hhead :
          p output₁ left = p output₂ left :=
        (p.inj (hbase₁.symm.trans hbase₂)).1
      exact (p.inj hhead).1
    · have hhitValue :
          hitValue₂ = p output₁ left :=
        (p.inj (hhit₂.symm.trans hbase₁)).1
      subst hitValue₂
      have hsmall := code_output_small hrec₂
      simp [sz] at hsmall <;> omega
  · rcases code_cases h₂ with hbase₂ | ⟨hitValue₂, hhit₂, hrec₂⟩
    · have hhitValue :
          hitValue₁ = p output₂ left :=
        (p.inj (hhit₁.symm.trans hbase₂)).1
      subst hitValue₁
      have hsmall := code_output_small hrec₁
      simp [sz] at hsmall <;> omega
    · exact code_left_unique hrec₁ hrec₂

noncomputable def eval (left right : T) : T := by
  classical
  exact if h : ∃ output, Code left right output
    then Classical.choose h
    else p left right

theorem eval_hit {left right output : T}
    (h : Code left right output) :
    eval left right = output := by
  rw [eval, dif_pos ⟨output, h⟩]
  exact code_output_unique (Classical.choose_spec ⟨output, h⟩) h

theorem eval_raw {left right : T}
    (h : ¬ ∃ output, Code left right output) :
    eval left right = p left right := by
  simp [eval, h]

theorem no_code_same (q : T) :
    ¬ ∃ output, Code q q output := by
  rintro ⟨output, h⟩
  have hsmall := code_first_small h
  omega

theorem no_code_raw_collision (x y : T) :
    ¬ ∃ output, Code (p x y) (p y y) output := by
  rintro ⟨output, h⟩
  rcases owner_tail h with ⟨head, hshape⟩
  have hy :
      y = p (p x y) (p x y) :=
    (p.inj hshape).2
  have hsize := congrArg sz hy
  simp [sz] at hsize <;> omega

theorem no_code_hit_square {x y hitValue : T}
    (h : Code x y hitValue) :
    ¬ ∃ output, Code hitValue (p y y) output := by
  rintro ⟨output, k⟩
  rcases owner_tail k with ⟨head, hshape⟩
  have hy : y = p hitValue hitValue :=
    (p.inj hshape).2
  subst y
  rcases code_cases h with hbase | ⟨inner, hhit, hrec⟩
  · have hcycle : hitValue = p hitValue x :=
      (p.inj hbase).1
    have hsize := congrArg sz hcycle
    simp [sz] at hsize <;> omega
  · have hinner : hitValue = inner :=
      (p.inj hhit).1
    have hx : hitValue = p x x :=
      (p.inj hhit).2
    subst inner
    subst hitValue
    have hsmall := code_output_small hrec
    simp [sz] at hsmall <;> omega

theorem source_eval (x y : T) :
    eval y (eval (eval x y) (eval y y)) = x := by
  rw [eval_raw (no_code_same y)]
  by_cases hcollision : ∃ hitValue, Code x y hitValue
  · let hitValue := Classical.choose hcollision
    have hhit : Code x y hitValue :=
      Classical.choose_spec hcollision
    rw [eval_hit hhit]
    rw [eval_raw (no_code_hit_square hhit)]
    exact eval_hit (Code.hit hhit)
  · rw [eval_raw hcollision]
    rw [eval_raw (no_code_raw_collision x y)]
    exact eval_hit (Code.base x y)

noncomputable instance instMagma : Magma T where
  op := eval

theorem source_holds (x y : T) :
    x = y ◇ ((x ◇ y) ◇ (y ◇ y)) := by
  change x = eval y (eval (eval x y) (eval y y))
  exact (source_eval x y).symm

def gx : T := g 0
def gy : T := g 1

theorem no_code_gx_gy_square :
    ¬ ∃ output, Code gx (p gy gy) output := by
  rintro ⟨output, h⟩
  rcases owner_tail h with ⟨head, hshape⟩
  have hy : gy = p gx gx :=
    (p.inj hshape).2
  cases hy

theorem no_code_gy_target_inner :
    ¬ ∃ output, Code gy (p gx (p gy gy)) output := by
  rintro ⟨output, h⟩
  rcases code_cases h with hbase | ⟨hitValue, hhit, hrec⟩
  · have hx : gx = p output gy :=
      (p.inj hbase).1
    cases hx
  · have hx : gx = hitValue :=
      (p.inj hhit).1
    subst hitValue
    have hsmall := code_output_small hrec
    simp [gx, gy, sz] at hsmall <;> omega

theorem no_code_target_root :
    ¬ ∃ output,
      Code (p gy (p gx (p gy gy))) gy output := by
  rintro ⟨output, h⟩
  have hsmall := code_first_small h
  simp [gy, sz] at hsmall <;> omega

theorem target2304_value :
    (gy ◇ (gx ◇ (gy ◇ gy))) ◇ gy =
      p (p gy (p gx (p gy gy))) gy := by
  change
    eval (eval gy (eval gx (eval gy gy))) gy =
      p (p gy (p gx (p gy gy))) gy
  rw [eval_raw (no_code_same gy)]
  rw [eval_raw no_code_gx_gy_square]
  rw [eval_raw no_code_gy_target_inner]
  rw [eval_raw no_code_target_root]

theorem bad2304 :
    gx ≠ (gy ◇ (gx ◇ (gy ◇ gy))) ◇ gy := by
  rw [target2304_value]
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
    exact T.bad2304 (target T.gx T.gy)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_883_to_2304 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_883_to_2304
