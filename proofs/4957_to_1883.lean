-- Equation4957 → Equation1883
-- Recorded verdict: false
-- Premise: x = y * (x * (y * (z * (x * z))))
-- Conclusion: x = (x * (y * z)) * (w * u)
-- Original submission SHA-256: 2c4fb209ebedf5c5832205d7994ff28e7dfb9cc1f564588a5643a346ee68dacc
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (y ◇ (z ◇ (x ◇ z))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (x ◇ (y ◇ z)) ◇ (w ◇ u)
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
        (p output (p owner (p z (p output z)))) output
  | hit {output owner z hitValue : T}
      (h : Code output z hitValue) :
      Code owner
        (p output (p owner (p z hitValue))) output

theorem code_spine {first second output : T}
    (h : Code first second output) :
    ∃ z last,
      second = p output (p first (p z last)) := by
  cases h with
  | base output owner z =>
      exact ⟨z, p output z, rfl⟩
  | @hit output owner z hitValue h =>
      exact ⟨z, hitValue, rfl⟩

theorem code_cases {first second output : T}
    (h : Code first second output) :
    (∃ z,
      second =
        p output (p first (p z (p output z)))) ∨
    (∃ z hitValue,
      second =
          p output (p first (p z hitValue)) ∧
        Code output z hitValue) := by
  cases h with
  | base output owner z =>
      exact Or.inl ⟨z, rfl⟩
  | @hit output owner z hitValue h =>
      exact Or.inr ⟨z, hitValue, rfl, h⟩

theorem code_output_unique {first second output₁ output₂ : T}
    (h₁ : Code first second output₁)
    (h₂ : Code first second output₂) :
    output₁ = output₂ := by
  rcases code_spine h₁ with ⟨z₁, last₁, hshape₁⟩
  rcases code_spine h₂ with ⟨z₂, last₂, hshape₂⟩
  exact (p.inj (hshape₁.symm.trans hshape₂)).1

theorem code_output_small {first second output : T}
    (h : Code first second output) :
    sz output < sz second := by
  rcases code_spine h with ⟨z, last, rfl⟩
  simp [sz] <;> omega

theorem code_first_small {first second output : T}
    (h : Code first second output) :
    sz first < sz second := by
  rcases code_spine h with ⟨z, last, rfl⟩
  simp [sz] <;> omega

theorem no_code_if_second_le_first {first second : T}
    (hsize : sz second ≤ sz first) :
    ¬ ∃ output, Code first second output := by
  rintro ⟨output, h⟩
  have hsmall := code_first_small h
  omega

theorem no_code_same (q : T) :
    ¬ ∃ output, Code q q output :=
  no_code_if_second_le_first (Nat.le_refl _)

theorem no_code_output_second {first second : T} :
    ¬ Code first second second := by
  intro h
  have hsmall := code_output_small h
  omega

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

theorem no_code_raw_first (x z : T) :
    ¬ ∃ output, Code z (p x z) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨q, last, hshape⟩
  have hz : z = p z (p q last) :=
    (p.inj hshape).2
  have hsize := congrArg sz hz
  simp [sz] at hsize <;> omega

theorem no_code_after_hit_first {x z hitValue : T}
    (h : Code x z hitValue) :
    ¬ ∃ output, Code z hitValue output := by
  rintro ⟨output, k⟩
  have hsmall := code_output_small h
  have ksmall := code_first_small k
  omega

theorem no_code_raw_second (x y z : T) :
    ¬ ∃ output, Code y (p z (p x z)) output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨q, hshape⟩ |
      ⟨q, hitValue, hshape, hrec⟩
  · have hout : z = output := (p.inj hshape).1
    subst output
    have htail :
        p x z = p y (p q (p z q)) :=
      (p.inj hshape).2
    have hz : z = p q (p z q) :=
      (p.inj htail).2
    have hsize := congrArg sz hz
    simp [sz] at hsize <;> omega
  · have hout : z = output := (p.inj hshape).1
    subst output
    have htail :
        p x z = p y (p q hitValue) :=
      (p.inj hshape).2
    have hz : z = p q hitValue :=
      (p.inj htail).2
    have hsize := congrArg sz hz
    have hsmall := code_first_small hrec
    simp [sz] at hsize <;> omega

theorem no_code_after_hit_second {x z hitValue : T}
    (h : Code x z hitValue) (y : T) :
    ¬ ∃ output, Code y (p z hitValue) output := by
  rintro ⟨output, k⟩
  rcases code_cases k with
      ⟨q, hshape⟩ |
      ⟨q, nextValue, hshape, hrec⟩
  · have hout : z = output := (p.inj hshape).1
    subst output
    have hhit :
        hitValue = p y (p q (p z q)) :=
      (p.inj hshape).2
    have hsize := congrArg sz hhit
    have hsmall := code_output_small h
    simp [sz] at hsize <;> omega
  · have hout : z = output := (p.inj hshape).1
    subst output
    have hhit :
        hitValue = p y (p q nextValue) :=
      (p.inj hshape).2
    have hsize := congrArg sz hhit
    have hsmall := code_output_small h
    have hrecsmall := code_first_small hrec
    simp [sz] at hsize <;> omega

theorem no_code_after_hit_third {x z hitValue : T}
    (h : Code x z hitValue) (y : T) :
    ¬ ∃ output,
      Code x (p y (p z hitValue)) output := by
  rintro ⟨output, k⟩
  rcases code_spine k with ⟨q, last, hshape⟩
  have htail :
      p z hitValue = p x (p q last) :=
    (p.inj hshape).2
  have hzx : z = x := (p.inj htail).1
  subst z
  exact no_code_same x ⟨hitValue, h⟩

theorem no_code_raw_third (x y z : T) :
    ¬ ∃ output,
      Code x (p y (p z (p x z))) output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨q, hshape⟩ |
      ⟨q, hitValue, hshape, hrec⟩
  · have hout : y = output := (p.inj hshape).1
    subst output
    have htail :
        p z (p x z) =
          p x (p q (p y q)) :=
      (p.inj hshape).2
    have hzx : z = x := (p.inj htail).1
    subst z
    have hrest :
        p x x = p q (p y q) :=
      (p.inj htail).2
    have hq : x = q := (p.inj hrest).1
    subst q
    have hx : x = p y x := (p.inj hrest).2
    have hsize := congrArg sz hx
    simp [sz] at hsize <;> omega
  · have hout : y = output := (p.inj hshape).1
    subst output
    have htail :
        p z (p x z) =
          p x (p q hitValue) :=
      (p.inj hshape).2
    have hzx : z = x := (p.inj htail).1
    subst z
    have hrest :
        p x x = p q hitValue :=
      (p.inj htail).2
    have hq : x = q := (p.inj hrest).1
    subst q
    have hhit : x = hitValue := (p.inj hrest).2
    subst hitValue
    exact no_code_output_second hrec

theorem source_eval (x y z : T) :
    eval y
      (eval x
        (eval y
          (eval z (eval x z)))) = x := by
  by_cases hcollision : ∃ hitValue, Code x z hitValue
  · let hitValue := Classical.choose hcollision
    have hhit : Code x z hitValue :=
      Classical.choose_spec hcollision
    rw [eval_hit hhit]
    rw [eval_raw (no_code_after_hit_first hhit)]
    rw [eval_raw (no_code_after_hit_second hhit y)]
    rw [eval_raw (no_code_after_hit_third hhit y)]
    exact eval_hit (Code.hit (output := x) hhit)
  · rw [eval_raw hcollision]
    rw [eval_raw (no_code_raw_first x z)]
    rw [eval_raw (no_code_raw_second x y z)]
    rw [eval_raw (no_code_raw_third x y z)]
    exact eval_hit (Code.base x y z)

noncomputable instance instMagma : Magma T where
  op := eval

theorem source_holds (x y z : T) :
    x = y ◇ (x ◇ (y ◇ (z ◇ (x ◇ z)))) := by
  change
    x =
      eval y
        (eval x
          (eval y
            (eval z (eval x z))))
  exact (source_eval x y z).symm

def g0 : T := g 0
def q : T := p g0 g0
def r : T := p g0 q

theorem no_code_g0_pair :
    ¬ ∃ output, Code g0 q output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨z, last, hshape⟩
  have htail :
      g0 = p g0 (p z last) :=
    (p.inj hshape).2
  cases htail

theorem gg_value : eval g0 g0 = q := by
  exact eval_raw (no_code_same g0)

theorem gq_value : eval g0 q = r := by
  exact eval_raw no_code_g0_pair

theorem rq_value : eval r q = p r q := by
  apply eval_raw
  apply no_code_if_second_le_first
  simp [r, q, g0, sz]

theorem target_rhs_value :
    (g0 ◇ (g0 ◇ g0)) ◇ (g0 ◇ g0) =
      p r q := by
  change
    eval (eval g0 (eval g0 g0)) (eval g0 g0) =
      p r q
  simp only [gg_value, gq_value, rq_value]

theorem bad1883 :
    g0 ≠ (g0 ◇ (g0 ◇ g0)) ◇ (g0 ◇ g0) := by
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
    exact T.bad1883
      (target T.g0 T.g0 T.g0 T.g0 T.g0)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4957_to_1883 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_4957_to_1883
