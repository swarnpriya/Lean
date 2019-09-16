-- Tactics are commands or instructions that describe how to build a proof.
-- Tactics are easier and shorter to write 

theorem test (p q : Prop) (hp : p) (hq : q) :
p ∧ q ∧ p := 
begin 
 apply and.intro,
 apply hp,
 apply and.intro,
 apply hq,
 apply hp
end 

#print test

example (p q r : Prop) :
p ∧ (q ∨ r) <-> (p ∧ q) ∨ (p ∧ r) :=
begin
 apply iff.intro,
 intro h,
 apply or.elim (and.right h),
 intro hq,
 apply or.inl,
 apply and.intro,
 exact and.left h,
 exact hq,
 intro h',
 apply or.inr,
 apply and.intro,
 apply and.left h,
 exact h',
 intro h'',
 apply or.elim h'',
 intro h2,
 apply and.intro,
 apply and.left h2,
 apply or.inl,
 apply and.right h2,
 intro h3,
 apply and.intro,
 apply and.left h3,
 apply or.inr,
 apply and.right h3,
end 

example (α : Type) : α -> α :=
begin 
 intro a,
 exact a
end

example (α : Type) : ∀ x : α, x = x :=
begin
 intro x,
 apply eq.refl x
end 

example : ∃ a : ℕ, 5 = a :=
begin 
 apply exists.intro,
 reflexivity
end

example : ∃ a : ℕ, a = a :=
begin 
 fapply exists.intro,
 exact 1,
 reflexivity
end

example (x : ℕ) : x = x :=
begin
 revert x,
 intro y,
 reflexivity
end 

example (x y : ℕ) (h : x = y) : y = x :=
begin 
 symmetry,
 assumption
end 

example : 3 = 3 :=
begin
reflexivity
end

example (p q : Prop) : p ∨ q -> q ∨ p :=
begin
 intro h,
 cases h with hp hq, 
 right,
 exact hp,
 left,
 exact hq
end 

example (p q : ℕ -> Prop) : (∃ x, p x) -> ∃ x, p x ∨ q x :=
begin 
intro h,
cases h with x px,
existsi x,
left,
exact px
end 

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    apply or.elim (and.right h),
      intro hq,
      apply or.inl,
      apply and.intro,
        exact and.left h,
      exact hq,
    intro hr,
    apply or.inr,
    apply and.intro,
      exact and.left h,
    exact hr,
  intro h,
  apply or.elim h,
    intro hpq,
    apply and.intro,
      exact and.left hpq,
    apply or.inl,
    exact and.right hpq,
  intro hpr,
  apply and.intro,
    exact and.left hpr,
  apply or.inr,
  exact and.right hpr
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin
  intros,
  apply eq.trans,
  apply eq.symm,
  assumption,
  assumption
end

example (y : ℕ) : (λ x : ℕ, 0) y = 0 :=
begin
  refl
end

example (x : ℕ) : x ≤ x :=
begin
  refl
end

example : ∃ a : ℕ, 5 = a :=
begin
  apply exists.intro,
  reflexivity
end

example : ∃ a : ℕ, a = a :=
begin
  fapply exists.intro,
  exact 0,
  reflexivity
end

example (x : ℕ) : x = x :=
begin
  revert x,
  -- goal is ⊢ ∀ (x : ℕ), x = x
  intro y,
  -- goal is y : ℕ ⊢ y = y
  reflexivity
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
  intro h,
   cases h with hp hqr,
   cases hqr with hq hr,
     left, constructor, repeat { assumption },
     right, constructor, repeat { assumption },
  intro h,
    cases h with hpq hpr,
      cases hpq with hp hq,
        constructor, exact hp, left, exact hq,
      cases hpr with hp hr,
        constructor, exact hp, right, exact hr
end

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin 
 intro h,
 cases h with x px,
 constructor, left, exact px
end

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin 
 intro h,
 cases h with x px,
 constructor, left, assumption
end 

example (p q : ℕ → Prop) :
  (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
begin 
  intro h,
  cases h with x hpq,
  cases hpq with hp hq,
  existsi x,
  split; assumption
end

universes u v
def swap_pair {α : Type u} {β : Type v} : α × β → β × α :=
begin
intro h,
cases h with ha hb,
constructor, assumption,
assumption
end

def swap_sum {α : Type u} {β : Type v} : α ⊕ β → β ⊕ α :=
begin
intro h,
cases h with ha hb,
right, assumption,
left, assumption
end

open nat
example (P : ℕ → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : ℕ) :
  P m :=
begin 
  cases m with m', exact h₀, exact h₁ m'
end 

example (p q : Prop) : p ∧ ¬ p → q :=
begin
  intro h, cases h, contradiction
end

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  exact
    have hp : p, from h.left,
    have hqr : q ∨ r, from h.right,
    show (p ∧ q) ∨ (p ∧ r),
    begin
      cases hqr with hq hr,
        exact or.inl ⟨hp, hq⟩,
      exact or.inr ⟨hp, hr⟩
    end
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
 apply iff.intro,
 intro h, 
 cases h.right with hq hr,
 apply or.inl,
 apply and.intro,
 apply and.left h,
 assumption,
 exact or.inr ⟨h.left, hr⟩,
 intro h,
 cases h with hpq hpr,
 exact ⟨hpq.left, or.inl hpq.right⟩,
  exact ⟨hpr.left, or.inr hpr.right⟩
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    cases h.right with hq hr,
      show (p ∧ q) ∨ (p ∧ r),
        { left, split, exact h.left, assumption },
      show (p ∧ q) ∨ (p ∧ r),
        { right, split, exact h.left, assumption },
  intro h,
  cases h with hpq hpr,
    show p ∧ (q ∨ r),
      { cases hpq, split, assumption, left, assumption },
    show p ∧ (q ∨ r),
      { cases hpr, split, assumption, right, assumption }
end

example (n : ℕ) : n + 1 = nat.succ n :=
begin
  show nat.succ n = nat.succ n,
  reflexivity
end

example (p q : Prop) : p ∧ q → q ∧ p :=
begin
  intro h,
  cases h with hp hq,
  split,
  assumption,
  assumption
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
  begin
    intro h,
    cases h.right with hq hr,
    begin
      show (p ∧ q) ∨ (p ∧ r),
        exact or.inl ⟨h.left, hq⟩
    end,
    show (p ∧ q) ∨ (p ∧ r),
      exact or.inr ⟨h.left, hr⟩
  end,
  intro h,
  cases h with hpq hpr,
  begin
    show p ∧ (q ∨ r),
      exact ⟨hpq.left, or.inl hpq.right⟩
  end,
  show p ∧ (q ∨ r),
    exact ⟨hpr.left, or.inr hpr.right⟩
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
  { intro h,
    cases h.right with hq hr,
    { show (p ∧ q) ∨ (p ∧ r),
        exact or.inl ⟨h.left, hq⟩ },
    show (p ∧ q) ∨ (p ∧ r),
      exact or.inr ⟨h.left, hr⟩ },
  intro h,
  cases h with hpq hpr,
  { show p ∧ (q ∨ r),
      exact ⟨hpq.left, or.inl hpq.right⟩ },
  show p ∧ (q ∨ r),
    exact ⟨hpr.left, or.inr hpr.right⟩
end

example (p q : Prop) (hp : p) : p ∨ q :=
begin left, assumption end

example (p q : Prop) (hp : p) : p ∨ q :=
by { left, assumption }

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
by split; assumption

example (p q : Prop) (hp : p) : p ∨ q :=
by { left, assumption } <|> { right, assumption}

meta def my_tac : tactic unit :=
`[ repeat { {left, assumption} <|> right <|> assumption } ]

example (p q r : Prop) (hp : p) : p ∨ q ∨ r :=
by my_tac

example (p q r : Prop) (hq : q) : p ∨ q ∨ r :=
by my_tac

example (p q r : Prop) (hr : r) : p ∨ q ∨ r :=
by my_tac

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  cases h with hp hqr,
  show (p ∧ q) ∨ (p ∧ r),
  cases hqr with hq hr,
    have hpq : p ∧ q,
      from and.intro hp hq,
    left, exact hpq,
  have hpr : p ∧ r,
    from and.intro hp hr,
  right, exact hpr
end

example : ∃ x, x + 2 = 8 :=
begin
  let a : ℕ := 3 * 2,
  existsi a,
  reflexivity
end

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  have hp : p := h.left,
  have hqr : q ∨ r := h.right,
  show (p ∧ q) ∨ (p ∧ r),
  cases hqr with hq hr,
    exact or.inl ⟨hp, hq⟩,
  exact or.inr ⟨hp, hr⟩
end



example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    cases h.right with hq hr,
      show (p ∧ q) ∨ (p ∧ r),
        from or.inl ⟨h.left, hq⟩,
      show (p ∧ q) ∨ (p ∧ r),
        from or.inr ⟨h.left, hr⟩,
  intro h,
  cases h with hpq hpr,
    show p ∧ (q ∨ r),
      from ⟨hpq.left, or.inl hpq.right⟩,
    show p ∧ (q ∨ r),
      from ⟨hpr.left, or.inr hpr.right⟩
end
