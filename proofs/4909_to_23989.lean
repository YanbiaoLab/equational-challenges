-- Equation4909 → Equation23989
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ (x ◇ (y ◇ (x ◇ y))))
-- Conclusion: x = ((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)
-- Original submission SHA-256: 14ef4377c22691678a09a40a5b0730b3cd88743dd6375a957b695a9eda58c790
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (x ◇ (x ◇ (y ◇ (x ◇ y))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = ((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x)
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
        (p output (p output (p owner (p output owner)))) output
  | hit {output owner hitValue : T}
      (h : Code output owner hitValue) :
      Code owner
        (p output (p output (p owner hitValue))) output

theorem code_spine {first second output : T}
    (h : Code first second output) :
    ∃ tail, second = p output (p output (p first tail)) := by
  cases h with
  | base output _ =>
      exact ⟨p output _, rfl⟩
  | @hit output owner hitValue h =>
      exact ⟨hitValue, rfl⟩

theorem code_output_unique {first second output₁ output₂ : T}
    (h₁ : Code first second output₁)
    (h₂ : Code first second output₂) :
    output₁ = output₂ := by
  rcases code_spine h₁ with ⟨tail₁, hshape₁⟩
  rcases code_spine h₂ with ⟨tail₂, hshape₂⟩
  exact (p.inj (hshape₁.symm.trans hshape₂)).1

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
    second =
        p output (p output (p first (p output first))) ∨
      ∃ hitValue,
        second =
            p output (p output (p first hitValue)) ∧
          Code output first hitValue := by
  cases h with
  | base output owner =>
      exact Or.inl rfl
  | @hit output owner hitValue h =>
      exact Or.inr ⟨hitValue, rfl, h⟩

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

theorem no_code_collision_owner {x y hitValue : T}
    (h : Code x y hitValue) :
    ¬ ∃ output, Code y hitValue output := by
  rintro ⟨output, k⟩
  have hxy := code_output_small h
  have hyx := code_first_small k
  omega

theorem no_code_collision_output₁ {x y hitValue : T}
    (h : Code x y hitValue) :
    ¬ ∃ output, Code x (p y hitValue) output := by
  rintro ⟨output, k⟩
  rcases code_spine k with ⟨tail, hshape⟩
  have hy : y = output := (p.inj hshape).1
  have hhit :
      hitValue = p output (p x tail) :=
    (p.inj hshape).2
  have hy_lt_hit : sz y < sz hitValue := by
    rw [hy, hhit]
    simp [sz] <;> omega
  have hhit_lt_y := code_output_small h
  omega

theorem no_code_collision_output₂ {x y hitValue : T}
    (h : Code x y hitValue) :
    ¬ ∃ output, Code x (p x (p y hitValue)) output := by
  rintro ⟨output, k⟩
  rcases code_spine k with ⟨tail, hshape⟩
  have hx : x = output := (p.inj hshape).1
  have hrest :
      p y hitValue = p output (p x tail) :=
    (p.inj hshape).2
  have hy : y = output := (p.inj hrest).1
  have hxy : x = y := hx.trans hy.symm
  rw [← hxy] at h
  exact no_code_same x ⟨hitValue, h⟩

theorem no_code_raw_owner (x y : T) :
    ¬ ∃ output, Code y (p x y) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨tail, hshape⟩
  have hy :
      y = p output (p y tail) :=
    (p.inj hshape).2
  have hsize := congrArg sz hy
  simp [sz] at hsize <;> omega

theorem no_code_raw_output₁ (x y : T) :
    ¬ ∃ output, Code x (p y (p x y)) output := by
  rintro ⟨output, h⟩
  rcases code_spine h with ⟨tail, hshape⟩
  have hy : y = output := (p.inj hshape).1
  have hrest :
      p x y = p output (p x tail) :=
    (p.inj hshape).2
  have hx : x = output := (p.inj hrest).1
  have htail : y = p x tail := (p.inj hrest).2
  have hxy : x = y := hx.trans hy.symm
  have hcycle : y = p y tail := by
    simpa [hxy] using htail
  have hsize := congrArg sz hcycle
  simp [sz] at hsize <;> omega

theorem no_code_raw_output₂ (x y : T) :
    ¬ ∃ output, Code x (p x (p y (p x y))) output := by
  rintro ⟨output, h⟩
  rcases code_cases h with hbase | hhit
  · have hx : x = output := (p.inj hbase).1
    have hrest₁ :
        p y (p x y) =
          p output (p x (p output x)) :=
      (p.inj hbase).2
    subst output
    have hy : y = x := (p.inj hrest₁).1
    subst y
    have hrest₂ :
        p x x = p x (p x x) :=
      (p.inj hrest₁).2
    have hcycle : x = p x x := (p.inj hrest₂).2
    have hsize := congrArg sz hcycle
    simp [sz] at hsize <;> omega
  · rcases hhit with ⟨hitValue, hshape, hrec⟩
    have hx : x = output := (p.inj hshape).1
    have hrest₁ :
        p y (p x y) =
          p output (p x hitValue) :=
      (p.inj hshape).2
    subst output
    have hy : y = x := (p.inj hrest₁).1
    subst y
    have hrest₂ :
        p x x = p x hitValue :=
      (p.inj hrest₁).2
    have hhit : x = hitValue := (p.inj hrest₂).2
    subst hitValue
    exact no_code_same x ⟨x, hrec⟩

theorem source_eval (x y : T) :
    eval y
      (eval x (eval x (eval y (eval x y)))) = x := by
  by_cases hcollision : ∃ hitValue, Code x y hitValue
  · let hitValue := Classical.choose hcollision
    have hhit : Code x y hitValue :=
      Classical.choose_spec hcollision
    rw [eval_hit hhit]
    rw [eval_raw (no_code_collision_owner hhit)]
    rw [eval_raw (no_code_collision_output₁ hhit)]
    rw [eval_raw (no_code_collision_output₂ hhit)]
    exact eval_hit (Code.hit hhit)
  · rw [eval_raw hcollision]
    rw [eval_raw (no_code_raw_owner x y)]
    rw [eval_raw (no_code_raw_output₁ x y)]
    rw [eval_raw (no_code_raw_output₂ x y)]
    exact eval_hit (Code.base x y)

noncomputable instance instMagma : Magma T where
  op := eval

theorem source_holds (x y : T) :
    x = y ◇ (x ◇ (x ◇ (y ◇ (x ◇ y)))) := by
  change
    x =
      eval y
        (eval x (eval x (eval y (eval x y))))
  exact (source_eval x y).symm

def g0 : T := g 0

theorem no_code_pair_g0 :
    ¬ ∃ output, Code (p g0 g0) g0 output := by
  rintro ⟨output, h⟩
  have hsmall := code_first_small h
  simp [g0, sz] at hsmall <;> omega

def a0 : T := p (p g0 g0) g0

theorem target_branch_value :
    (g0 ◇ g0) ◇ g0 = a0 := by
  change eval (eval g0 g0) g0 = a0
  rw [eval_raw (no_code_same g0)]
  rw [eval_raw no_code_pair_g0]
  rfl

theorem target_rhs_value :
    ((g0 ◇ g0) ◇ g0) ◇ ((g0 ◇ g0) ◇ g0) =
      p a0 a0 := by
  simp only [target_branch_value]
  change eval a0 a0 = p a0 a0
  exact eval_raw (no_code_same a0)

theorem bad23989 :
    g0 ≠ ((g0 ◇ g0) ◇ g0) ◇ ((g0 ◇ g0) ◇ g0) := by
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
    exact T.bad23989 (target T.g0)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4909_to_23989 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_4909_to_23989
