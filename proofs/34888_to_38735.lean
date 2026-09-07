-- Equation34888 → Equation38735
-- Recorded verdict: false
-- Premise: x = ((y * y) * ((x * z) * x)) * y
-- Conclusion: x = ((y * ((z * z) * w)) * x) * u
-- Original submission SHA-256: 50eb3eb78c0d7125c3bdfca9ba8f91fb60176d57ced74bb39f7bb9e2b20f9fd7
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ y) ◇ ((x ◇ z) ◇ x)) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((y ◇ ((z ◇ z) ◇ w)) ◇ x) ◇ u
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
      Code
        (p (p owner owner)
          (p (p output parameter) output))
        owner output
  | hit {output owner parameter hitValue : T}
      (h : Code output parameter hitValue) :
      Code
        (p (p owner owner) (p hitValue output))
        owner output

theorem code_spine {first second output : T}
    (h : Code first second output) :
    ∃ head,
      first = p (p second second) (p head output) := by
  cases h with
  | base output owner parameter =>
      exact ⟨p output parameter, rfl⟩
  | @hit output owner parameter hitValue h =>
      exact ⟨hitValue, rfl⟩

theorem code_output_unique {first second output₁ output₂ : T}
    (h₁ : Code first second output₁)
    (h₂ : Code first second output₂) :
    output₁ = output₂ := by
  rcases code_spine h₁ with ⟨head₁, hshape₁⟩
  rcases code_spine h₂ with ⟨head₂, hshape₂⟩
  have hright :
      p head₁ output₁ = p head₂ output₂ :=
    (p.inj (hshape₁.symm.trans hshape₂)).2
  exact (p.inj hright).2

theorem code_output_small {first second output : T}
    (h : Code first second output) :
    sz output < sz first := by
  rcases code_spine h with ⟨head, rfl⟩
  simp [sz] <;> omega

theorem code_second_small {first second output : T}
    (h : Code first second output) :
    sz second < sz first := by
  rcases code_spine h with ⟨head, rfl⟩
  simp [sz] <;> omega

theorem code_cases {first second output : T}
    (h : Code first second output) :
    (∃ parameter,
      first =
        p (p second second)
          (p (p output parameter) output)) ∨
    (∃ parameter hitValue,
      first =
          p (p second second) (p hitValue output) ∧
        Code output parameter hitValue) := by
  cases h with
  | base output owner parameter =>
      exact Or.inl ⟨parameter, rfl⟩
  | @hit output owner parameter hitValue h =>
      exact Or.inr ⟨parameter, hitValue, rfl, h⟩

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
  have hsmall := code_second_small h
  omega

theorem no_code_output_first {first second : T} :
    ¬ Code first second first := by
  intro h
  have hsmall := code_output_small h
  omega

theorem no_code_after_hit {x z hitValue : T}
    (h : Code x z hitValue) :
    ¬ ∃ output, Code hitValue x output := by
  rintro ⟨output, k⟩
  have hsmall := code_output_small h
  have ksmall := code_second_small k
  omega

theorem no_code_square_first (y second : T) :
    ¬ ∃ output, Code (p y y) second output := by
  rintro ⟨output, h⟩
  rcases code_cases h with
      ⟨parameter, hshape⟩ |
      ⟨parameter, hitValue, hshape, hrec⟩
  · have hleft :
        y = p second second :=
      (p.inj hshape).1
    have hright :
        y = p (p output parameter) output :=
      (p.inj hshape).2
    have hpair :
        p second second =
          p (p output parameter) output :=
      hleft.symm.trans hright
    have hhead :
        second = p output parameter :=
      (p.inj hpair).1
    have hout :
        second = output :=
      (p.inj hpair).2
    rw [← hout] at hhead
    have hsize := congrArg sz hhead
    simp [sz] at hsize <;> omega
  · have hleft :
        y = p second second :=
      (p.inj hshape).1
    have hright :
        y = p hitValue output :=
      (p.inj hshape).2
    have hpair :
        p second second =
          p hitValue output :=
      hleft.symm.trans hright
    have hhit :
        second = hitValue :=
      (p.inj hpair).1
    have hout :
        second = output :=
      (p.inj hpair).2
    rw [← hout, ← hhit] at hrec
    exact no_code_output_first hrec

theorem no_code_raw_overlap (x z : T) :
    ¬ ∃ output, Code (p x z) x output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨head, hshape⟩
  have hx : x = p x x := (p.inj hshape).1
  have hsize := congrArg sz hx
  simp [sz] at hsize <;> omega

theorem no_code_atom_first (index : Nat) (second : T) :
    ¬ ∃ output, Code (g index) second output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨head, hshape⟩
  cases hshape

theorem no_code_bad_left
    {left right second : T}
    (hbad : left ≠ p second second) :
    ¬ ∃ output, Code (p left right) second output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨head, hshape⟩
  exact hbad ((p.inj hshape).1)

theorem source_eval (x y z : T) :
    eval
      (eval (eval y y) (eval (eval x z) x))
      y = x := by
  rw [eval_raw (no_code_same y)]
  by_cases hcollision : ∃ hitValue, Code x z hitValue
  · let hitValue := Classical.choose hcollision
    have hhit : Code x z hitValue :=
      Classical.choose_spec hcollision
    rw [eval_hit hhit]
    rw [eval_raw (no_code_after_hit hhit)]
    rw [eval_raw (no_code_square_first y (p hitValue x))]
    exact eval_hit (Code.hit (owner := y) hhit)
  · rw [eval_raw hcollision]
    rw [eval_raw (no_code_raw_overlap x z)]
    rw [
      eval_raw
        (no_code_square_first y (p (p x z) x))
    ]
    exact eval_hit (Code.base x y z)

noncomputable instance instMagma : Magma T where
  op := eval

theorem source_holds (x y z : T) :
    x = ((y ◇ y) ◇ ((x ◇ z) ◇ x)) ◇ y := by
  change
    x =
      eval
        (eval (eval y y) (eval (eval x z) x))
        y
  exact (source_eval x y z).symm

def g0 : T := g 0

theorem target_rhs_value :
    ((g0 ◇ ((g0 ◇ g0) ◇ g0)) ◇ g0) ◇ g0 =
      p
        (p
          (p g0 (p (p g0 g0) g0))
          g0)
        g0 := by
  change
    eval
      (eval
        (eval g0 (eval (eval g0 g0) g0))
        g0)
      g0 =
        p
          (p
            (p g0 (p (p g0 g0) g0))
            g0)
          g0
  have h₁ :
      eval g0 g0 = p g0 g0 :=
    eval_raw (no_code_atom_first 0 g0)
  rw [h₁]
  have h₂ :
      eval (p g0 g0) g0 =
        p (p g0 g0) g0 :=
    eval_raw (no_code_square_first g0 g0)
  rw [h₂]
  have h₃ :
      eval g0 (p (p g0 g0) g0) =
        p g0 (p (p g0 g0) g0) :=
    eval_raw
      (no_code_atom_first 0 (p (p g0 g0) g0))
  rw [h₃]
  have hleft₄ : g0 ≠ p g0 g0 := by
    intro h
    cases h
  have h₄ :
      eval
        (p g0 (p (p g0 g0) g0))
        g0 =
          p
            (p g0 (p (p g0 g0) g0))
            g0 :=
    eval_raw (no_code_bad_left hleft₄)
  rw [h₄]
  have hleft₅ :
      p g0 (p (p g0 g0) g0) ≠ p g0 g0 := by
    intro h
    have hright :
        p (p g0 g0) g0 = g0 :=
      (p.inj h).2
    cases hright
  exact
    eval_raw
      (no_code_bad_left hleft₅)

theorem bad38735 :
    g0 ≠ ((g0 ◇ ((g0 ◇ g0) ◇ g0)) ◇ g0) ◇ g0 := by
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
      T.bad38735
        (target T.g0 T.g0 T.g0 T.g0 T.g0)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_34888_to_38735 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_34888_to_38735
