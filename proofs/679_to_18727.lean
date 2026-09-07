-- Equation679 → Equation18727
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ ((y ◇ y) ◇ x))
-- Conclusion: x = (x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))
-- Original submission SHA-256: d197b4b332a798e263e476ba48df7338454ae880e1a4e31835c79e25c0384333
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (x ◇ ((y ◇ y) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = (x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))
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
      Code owner (p output (p (p owner owner) output)) output
  | rrHit {output owner hitValue : T}
      (h : Code (p owner owner) output hitValue) :
      Code owner (p output hitValue) output

theorem code_output_head {left right output : T}
    (h : Code left right output) :
    ∃ tail, right = p output tail := by
  cases h with
  | base output owner =>
      exact ⟨_, rfl⟩
  | @rrHit output owner hitValue h =>
      exact ⟨hitValue, rfl⟩

theorem code_output_is_left {left first second output : T}
    (h : Code left (p first second) output) :
    output = first := by
  rcases code_output_head h with ⟨tail, hshape⟩
  exact (p.inj hshape).1.symm

theorem code_output_unique {left right output₁ output₂ : T}
    (h₁ : Code left right output₁)
    (h₂ : Code left right output₂) :
    output₁ = output₂ := by
  rcases code_output_head h₁ with ⟨tail₁, hshape₁⟩
  rcases code_output_head h₂ with ⟨tail₂, hshape₂⟩
  exact (p.inj (hshape₁.symm.trans hshape₂)).1

theorem code_output_small {left right output : T}
    (h : Code left right output) :
    sz output < sz right := by
  rcases code_output_head h with ⟨tail, rfl⟩
  simp [sz] <;> omega

theorem code_first_small {left right output : T}
    (h : Code left right output) :
    sz left < sz right := by
  induction h with
  | base output owner =>
      simp [sz] <;> omega
  | @rrHit output owner hitValue h ih =>
      simp [sz] at ih ⊢ <;> omega

theorem code_cases {left right output : T}
    (h : Code left right output) :
    right = p output (p (p left left) output) ∨
      ∃ hitValue,
        right = p output hitValue ∧
          Code (p left left) output hitValue := by
  cases h with
  | base output owner =>
      exact Or.inl rfl
  | @rrHit output owner hitValue h =>
      exact Or.inr ⟨hitValue, rfl, h⟩

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

theorem no_code_after_hit {left right hitValue : T}
    (h : Code left right hitValue) :
    ¬ ∃ output, Code right hitValue output := by
  rintro ⟨output, k⟩
  have hhit := code_output_small h
  have hright := code_first_small k
  omega

theorem no_code_raw_post_collision (x y : T) :
    ¬ ∃ output, Code x (p (p y y) x) output := by
  rintro ⟨output, h⟩
  rcases code_cases h with hbase | ⟨hitValue, hkey, hrec⟩
  · have hx : x = p (p x x) output := (p.inj hbase).2
    have hs := congrArg sz hx
    simp [sz] at hs <;> omega
  · have houtput : output = p y y :=
      code_output_is_left h
    have hhit : hitValue = x := (p.inj hkey).2.symm
    subst output
    subst hitValue
    have hxy : x = y := code_output_is_left hrec
    subst y
    exact no_code_same (p x x) ⟨x, hrec⟩

theorem source_eval (x y : T) :
    eval y (eval x (eval (eval y y) x)) = x := by
  rw [eval_raw (no_code_same y)]
  by_cases hcollision : ∃ hitValue, Code (p y y) x hitValue
  · let hitValue := Classical.choose hcollision
    have hhit : Code (p y y) x hitValue :=
      Classical.choose_spec hcollision
    rw [eval_hit hhit]
    rw [eval_raw (no_code_after_hit hhit)]
    exact eval_hit (Code.rrHit hhit)
  · rw [eval_raw hcollision]
    rw [eval_raw (no_code_raw_post_collision x y)]
    exact eval_hit (Code.base x y)

noncomputable instance instMagma : Magma T where
  op := eval

theorem source_holds (x y : T) :
    x = y ◇ (x ◇ ((y ◇ y) ◇ x)) := by
  change x = eval y (eval x (eval (eval y y) x))
  exact (source_eval x y).symm

theorem eval_self (q : T) :
    eval q q = p q q :=
  eval_raw (no_code_same q)

theorem no_code_self_square (q : T) :
    ¬ ∃ output, Code q (p q q) output := by
  rintro ⟨output, h⟩
  rcases code_cases h with hbase | ⟨hitValue, hkey, hrec⟩
  · have hq : q = p (p q q) output := (p.inj hbase).2
    have hs := congrArg sz hq
    simp [sz] at hs <;> omega
  · have houtput : output = q := code_output_is_left h
    have hhit : hitValue = q := (p.inj hkey).2.symm
    subst output
    subst hitValue
    have hsmall := code_first_small hrec
    simp [sz] at hsmall <;> omega

theorem eval_self_square (q : T) :
    eval q (p q q) = p q (p q q) :=
  eval_raw (no_code_self_square q)

def gx : T := g 0

theorem target18727_value :
    (gx ◇ gx) ◇ ((gx ◇ gx) ◇ (gx ◇ gx)) =
      p (p gx gx) (p (p gx gx) (p gx gx)) := by
  change
    eval (eval gx gx) (eval (eval gx gx) (eval gx gx)) =
      p (p gx gx) (p (p gx gx) (p gx gx))
  simp only [eval_self, eval_self_square]

theorem bad18727 :
    gx ≠ (gx ◇ gx) ◇ ((gx ◇ gx) ◇ (gx ◇ gx)) := by
  rw [target18727_value]
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
    exact T.bad18727 (target T.gx)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_679_to_18727 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_679_to_18727
