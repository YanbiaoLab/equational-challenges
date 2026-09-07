-- Equation9667 → Equation58891
-- Recorded verdict: false
-- Premise: x = y * ((z * y) * (x * (y * y)))
-- Conclusion: (x * y) * z = z * (z * (y * z))
-- Original submission SHA-256: 1eb613bc7b4b5247cdd8af7a30e21bf21d3e6c004dcf5f3e5d51c4fd0f7eb532
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ y) ◇ (x ◇ (y ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = z ◇ (z ◇ (y ◇ z))
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
        (p (p z owner) (p output (p owner owner))) output
  | hit {output owner z hitValue : T}
      (h : Code z owner hitValue) :
      Code owner
        (p hitValue (p output (p owner owner))) output

theorem code_spine {first second output : T}
    (h : Code first second output) :
    ∃ head, second = p head (p output (p first first)) := by
  cases h with
  | base output _ z =>
      exact ⟨p z _, rfl⟩
  | @hit output _ _ hitValue h =>
      exact ⟨hitValue, rfl⟩

theorem code_output_unique {first second output₁ output₂ : T}
    (h₁ : Code first second output₁)
    (h₂ : Code first second output₂) :
    output₁ = output₂ := by
  rcases code_spine h₁ with ⟨head₁, hshape₁⟩
  rcases code_spine h₂ with ⟨head₂, hshape₂⟩
  have htail :
      p output₁ (p first first) =
        p output₂ (p first first) :=
    (p.inj (hshape₁.symm.trans hshape₂)).2
  exact (p.inj htail).1

theorem code_output_small {first second output : T}
    (h : Code first second output) :
    sz output < sz second := by
  rcases code_spine h with ⟨head, rfl⟩
  simp [sz] <;> omega

theorem code_first_small {first second output : T}
    (h : Code first second output) :
    sz first < sz second := by
  rcases code_spine h with ⟨head, rfl⟩
  simp [sz] <;> omega

theorem code_cases {first second output : T}
    (h : Code first second output) :
    (∃ z,
      second =
        p (p z first) (p output (p first first))) ∨
    (∃ z hitValue,
      second =
          p hitValue (p output (p first first)) ∧
        Code z first hitValue) := by
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

theorem no_code_x_square (x y : T) :
    ¬ ∃ output, Code x (p y y) output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨z, hshape⟩ |
      ⟨z, hitValue, hshape, hrec⟩
  · have hfirst : y = p z x := (p.inj hshape).1
    have hsecond :
        y = p output (p x x) :=
      (p.inj hshape).2
    have hx : x = p x x :=
      (p.inj (hfirst.symm.trans hsecond)).2
    have hsize := congrArg sz hx
    simp [sz] at hsize <;> omega
  · have hhit : y = hitValue := (p.inj hshape).1
    have hy :
        y = p output (p x x) :=
      (p.inj hshape).2
    subst hitValue
    have hsmall := code_output_small hrec
    have hsize := congrArg sz hy
    simp [sz] at hsize <;> omega

theorem no_code_raw_middle (x y z : T) :
    ¬ ∃ output,
      Code (p z y) (p x (p y y)) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨head, hshape⟩
  have htail :
      p y y =
        p output (p (p z y) (p z y)) :=
    (p.inj hshape).2
  have hy :
      y = p (p z y) (p z y) :=
    (p.inj htail).2
  have hsize := congrArg sz hy
  simp [sz] at hsize <;> omega

theorem no_code_output_square (first output : T) :
    ¬ Code first (p output output) output := by
  intro h
  rcases code_spine h with ⟨head, hshape⟩
  have hcycle :
      output = p output (p first first) :=
    (p.inj hshape).2
  have hsize := congrArg sz hcycle
  simp [sz] at hsize <;> omega

theorem no_code_hit_middle {z y hitValue : T}
    (h : Code z y hitValue) (x : T) :
    ¬ ∃ output,
      Code hitValue (p x (p y y)) output := by
  rintro ⟨output, k⟩
  rcases code_spine k with ⟨head, hshape⟩
  have htail :
      p y y =
        p output (p hitValue hitValue) :=
    (p.inj hshape).2
  have hy : y = p hitValue hitValue :=
    (p.inj htail).2
  rw [hy] at h
  exact no_code_output_square z hitValue h

theorem source_eval (x y z : T) :
    eval y
      (eval (eval z y) (eval x (eval y y))) = x := by
  rw [eval_raw (no_code_same y)]
  rw [eval_raw (no_code_x_square x y)]
  by_cases hcollision : ∃ hitValue, Code z y hitValue
  · let hitValue := Classical.choose hcollision
    have hhit : Code z y hitValue :=
      Classical.choose_spec hcollision
    rw [eval_hit hhit]
    rw [eval_raw (no_code_hit_middle hhit x)]
    exact eval_hit (Code.hit (output := x) hhit)
  · rw [eval_raw hcollision]
    rw [eval_raw (no_code_raw_middle x y z)]
    exact eval_hit (Code.base x y z)

noncomputable instance instMagma : Magma T where
  op := eval

theorem source_holds (x y z : T) :
    x = y ◇ ((z ◇ y) ◇ (x ◇ (y ◇ y))) := by
  change
    x =
      eval y
        (eval (eval z y) (eval x (eval y y)))
  exact (source_eval x y z).symm

def g0 : T := g 0

theorem no_code_lhs_root :
    ¬ ∃ output, Code (p g0 g0) g0 output := by
  rintro ⟨output, h⟩
  have hsmall := code_first_small h
  simp [g0, sz] at hsmall <;> omega

theorem no_code_rhs_root :
    ¬ ∃ output,
      Code g0 (p g0 (p g0 g0)) output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨z, hshape⟩ |
      ⟨z, hitValue, hshape, hrec⟩
  · have hg : g0 = p z g0 := (p.inj hshape).1
    cases hg
  · have hhit : g0 = hitValue := (p.inj hshape).1
    subst hitValue
    exact no_code_output_second hrec

theorem target_lhs_value :
    (g0 ◇ g0) ◇ g0 =
      p (p g0 g0) g0 := by
  change
    eval (eval g0 g0) g0 =
      p (p g0 g0) g0
  rw [eval_raw (no_code_same g0)]
  rw [eval_raw no_code_lhs_root]

theorem target_rhs_value :
    g0 ◇ (g0 ◇ (g0 ◇ g0)) =
      p g0 (p g0 (p g0 g0)) := by
  change
    eval g0 (eval g0 (eval g0 g0)) =
      p g0 (p g0 (p g0 g0))
  rw [eval_raw (no_code_same g0)]
  rw [eval_raw (no_code_x_square g0 g0)]
  rw [eval_raw no_code_rhs_root]

theorem bad58891 :
    (g0 ◇ g0) ◇ g0 ≠
      g0 ◇ (g0 ◇ (g0 ◇ g0)) := by
  rw [target_lhs_value, target_rhs_value]
  intro h
  have hfirst : p g0 g0 = g0 := (p.inj h).1
  cases hfirst

end T

end submission

open submission

noncomputable def submission : Goal := by
  refine ⟨T, T.instMagma, ?_, ?_⟩
  · intro x y z
    exact T.source_holds x y z
  · intro target
    exact T.bad58891 (target T.g0 T.g0 T.g0)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_9667_to_58891 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_9667_to_58891
