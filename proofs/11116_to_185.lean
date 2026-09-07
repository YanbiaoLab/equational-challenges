-- Equation11116 → Equation185
-- Recorded verdict: false
-- Premise: x = y ◇ ((x ◇ (z ◇ x)) ◇ (y ◇ y))
-- Conclusion: x = (y ◇ y) ◇ (z ◇ w)
-- Original submission SHA-256: fe768962bb72c583d50fc361de57571233249fdaef61b863d774b2cf926bd46c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ (z ◇ x)) ◇ (y ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ y) ◇ (z ◇ w)
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
        (p (p output (p z output)) (p owner owner)) output
  | hit {output owner z hitValue : T}
      (h : Code z output hitValue) :
      Code owner
        (p (p output hitValue) (p owner owner)) output

theorem code_spine {first second output : T}
    (h : Code first second output) :
    ∃ tail, second = p (p output tail) (p first first) := by
  cases h with
  | base output _ z =>
      exact ⟨p z output, rfl⟩
  | @hit output _ _ hitValue h =>
      exact ⟨hitValue, rfl⟩

theorem code_output_unique {first second output₁ output₂ : T}
    (h₁ : Code first second output₁)
    (h₂ : Code first second output₂) :
    output₁ = output₂ := by
  rcases code_spine h₁ with ⟨tail₁, hshape₁⟩
  rcases code_spine h₂ with ⟨tail₂, hshape₂⟩
  have hleft :
      p output₁ tail₁ = p output₂ tail₂ :=
    (p.inj (hshape₁.symm.trans hshape₂)).1
  exact (p.inj hleft).1

theorem code_output_small {first second output : T}
    (h : Code first second output) :
    sz output < sz second := by
  rcases code_spine h with ⟨tail, rfl⟩
  simp [sz] <;> omega

theorem code_first_small {first second output : T}
    (h : Code first second output) :
    sz first < sz second := by
  rcases code_spine h with ⟨tail, rfl⟩
  simp [sz] <;> omega

theorem code_cases {first second output : T}
    (h : Code first second output) :
    (∃ z,
      second =
        p (p output (p z output)) (p first first)) ∨
    (∃ z hitValue,
      second =
          p (p output hitValue) (p first first) ∧
        Code z output hitValue) := by
  cases h with
  | base output _ z =>
      exact Or.inl ⟨z, rfl⟩
  | @hit output _ z hitValue h =>
      exact Or.inr ⟨z, hitValue, rfl, h⟩

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

theorem no_code_output_second {first second : T} :
    ¬ Code first second second := by
  intro h
  have hsmall := code_output_small h
  omega

theorem no_code_raw_overlap (x z : T) :
    ¬ ∃ output, Code x (p z x) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨tail, hshape⟩
  have hx : x = p x x := (p.inj hshape).2
  have hsize := congrArg sz hx
  simp [sz] at hsize <;> omega

theorem no_code_square (first y : T) :
    ¬ ∃ output, Code first (p y y) output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨z, hshape⟩ |
      ⟨z, hitValue, hshape, hrec⟩
  · have hleft :
        y = p output (p z output) :=
      (p.inj hshape).1
    have hright :
        y = p first first :=
      (p.inj hshape).2
    have hpair :
        p output (p z output) = p first first :=
      hleft.symm.trans hright
    have hout : output = first := (p.inj hpair).1
    have htail : p z output = first := (p.inj hpair).2
    rw [hout] at htail
    have hsize := congrArg sz htail
    simp [sz] at hsize <;> omega
  · have hleft :
        y = p output hitValue :=
      (p.inj hshape).1
    have hright :
        y = p first first :=
      (p.inj hshape).2
    have hpair :
        p output hitValue = p first first :=
      hleft.symm.trans hright
    have hout : output = first := (p.inj hpair).1
    have hhit : hitValue = first := (p.inj hpair).2
    rw [hout, hhit] at hrec
    exact no_code_output_second hrec

theorem no_code_after_hit {z x hitValue : T}
    (h : Code z x hitValue) :
    ¬ ∃ output, Code x hitValue output := by
  rintro ⟨output, k⟩
  have hsmall := code_output_small h
  have ksmall := code_first_small k
  omega

theorem source_eval (x y z : T) :
    eval y
      (eval (eval x (eval z x)) (eval y y)) = x := by
  rw [eval_raw (no_code_same y)]
  by_cases hcollision : ∃ hitValue, Code z x hitValue
  · let hitValue := Classical.choose hcollision
    have hhit : Code z x hitValue :=
      Classical.choose_spec hcollision
    rw [eval_hit hhit]
    rw [eval_raw (no_code_after_hit hhit)]
    rw [eval_raw (no_code_square (p x hitValue) y)]
    exact eval_hit (Code.hit (output := x) hhit)
  · rw [eval_raw hcollision]
    rw [eval_raw (no_code_raw_overlap x z)]
    rw [eval_raw (no_code_square (p x (p z x)) y)]
    exact eval_hit (Code.base x y z)

noncomputable instance instMagma : Magma T where
  op := eval

theorem source_holds (x y z : T) :
    x = y ◇ ((x ◇ (z ◇ x)) ◇ (y ◇ y)) := by
  change
    x =
      eval y
        (eval (eval x (eval z x)) (eval y y))
  exact (source_eval x y z).symm

def g0 : T := g 0

theorem target_rhs_value :
    (g0 ◇ g0) ◇ (g0 ◇ g0) =
      p (p g0 g0) (p g0 g0) := by
  change
    eval (eval g0 g0) (eval g0 g0) =
      p (p g0 g0) (p g0 g0)
  have hraw :
      eval g0 g0 = p g0 g0 :=
    eval_raw (no_code_same g0)
  simp only [hraw]
  exact eval_raw (no_code_same (p g0 g0))

theorem bad185 :
    g0 ≠ (g0 ◇ g0) ◇ (g0 ◇ g0) := by
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
    exact T.bad185 (target T.g0 T.g0 T.g0 T.g0)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_11116_to_185 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_11116_to_185
