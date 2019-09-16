-- Chapter 3 Exercises
-- Question 1
-- Commutativity of ∧ 
example (p q : Prop) : p ∧ q <-> q ∧ p :=
begin
  apply iff.intro,
  intro h,
  have hp : p, from and.left h,
  have hq : q, from and.right h,
  show q ∧ p, from and.intro hq hp,
  intro g,
  have hq' : q, from and.left g,
  have hp' : p, from and.right g,
  show p ∧ q, from and.intro hp' hq'
end
-- Question 2
-- Commutativity of ∨  
example (p q : Prop) : p ∨ q <-> q ∨ p :=
begin
 apply iff.intro,
 intro h,
 apply or.elim h,
 intro h1,
 apply or.inr,
 exact h1,
 intro h2,
 apply or.inl,
 exact h2,
 intro h',
 apply or.elim h',
 intro h1,
 apply or.inr,
 exact h1,
 intro h2,
 apply or.inl,
 exact h2, 
end
--Question 3
-- Associativity of ∧ 
example (p q r : Prop) :
 (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
 begin
  apply iff.intro,
  intro h,
  apply and.intro,
  have hp : (p ∧ q), from and.left h,
  have hp' : p, from and.left hp,
  show p, from hp',
  apply and.intro,
  have hp : (p ∧ q), from and.left h,
  have hp' : p, from and.left hp,
  have hq : q, from and.right hp,
  show q, from hq,
  have hr : r, from and.right h,
  show r, from hr,
  intro h',
  apply and.intro,
  apply and.elim h',
  intro h1,
  intro h2,
  apply and.intro,
  exact h1,
  apply and.left h2,
  apply and.elim h',
  intro h1,
  intro h2,
  apply and.right h2
end
-- Question 4
-- Associativity of ∨ 
example (p q r : Prop) : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
begin 
 apply iff.intro,
 intro h,
 apply or.elim h,
 intro h1,
 apply or.elim h1,
 intro h2,
 apply or.inl,
 apply h2,
 intro h3,
 apply or.inr,
 apply or.inl,
 exact h3,
 intro h4,
 apply or.inr,
 apply or.inr,
 exact h4,
 intro,
 apply or.inl,
 apply or.elim a,
 intro,
 apply or.inl,
 assumption,
 intro,
 apply or.inr,
 apply or.elim a_1,
 intro,
 assumption,
 intro,
 exfalso,
 admit
end 
-- Question 5
-- Distributivity of ∧ 
example (p q r : Prop) :
p ∧ (q ∨ r) <-> (p ∧ q) ∨ (p ∧ r) :=
begin
 apply iff.intro,
 intro h,
 apply or.elim (and.right h),
 intro hq,
 apply or.inl,
 apply and.intro,
 apply and.left h,
 exact hq,
 intro hr,
 apply or.inr,
 apply and.intro,
 apply and.left h,
 exact hr,
 intro h',
 apply or.elim h',
 intro h1,
 apply and.intro,
 apply and.left h1,
 apply or.inl,
 apply and.right h1,
 intro h'',
 apply and.intro,
 apply and.left h'',
 apply or.inr,
 apply and.right h'',
end
-- Question 6
-- Distributivity  of ∨ 
example (p q r : Prop) :
p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
begin 
 apply iff.intro,
 intro h,
 apply and.intro,
 apply or.elim h,
 intro h1,
 apply or.inl,
 exact h1,
 intro h2,
 apply or.inr,
 apply and.left h2,
 apply or.elim h,
 intro h3,
 apply or.inl,
 exact h3,
 intro h4,
 apply or.inr,
 apply and.right h4,
 intro h',
 apply or.elim (and.left h'),
 intro h1,
 apply or.inl,
 exact h1,
 intro h2,
 apply or.inr,
 apply and.intro,
 exact h2,
 admit
end
--Question 7
example (p q : Prop) : p ∧ ¬q → ¬(p → q) := 
begin 
 intro h,
 intro h',
 apply and.right h,
 apply h',
 apply and.left h
end
--Question 8
example (p : Prop) : ¬(p ∧ ¬p) := 
begin 
 intro h,
 apply and.right h,
 apply and.left h
end 
--Question 9
example (p q : Prop) : ¬p ∨ ¬q → ¬(p ∧ q) := 
begin
 intro h,
 intro h',
 apply or.elim h,
 intro h'',
 apply h'',
 apply and.left h',
 intro h1,
 apply h1,
 apply and.right h'
end 
--Question 10
example (p q r : Prop) : (p → (q → r)) ↔ (p ∧ q → r) := 
begin 
 apply iff.intro,
 intros,
 apply a,
 apply a_1.left,
 apply a_1.right,
 intros,
 apply a,
 apply and.intro,
 assumption,
 assumption
end 
--Question 11
example (p q: Prop) : (p → q) → (¬q → ¬p) := 
begin 
intros,
intro,
apply a_1,
apply a,
apply a_2
end
--Question 12
example (p : Prop) : ¬(p ↔ ¬p) := 
begin 
 intro,
 apply iff.elim_left a,
 apply iff.elim_right a,
 intro,
 apply iff.elim_left a,
 assumption,
 assumption,
 apply iff.elim_right a,
 intro,
 apply iff.elim_left a,
 assumption,
 assumption
end
--Question 13
example (p : Prop) : p ∧ false ↔ false := 
begin 
 apply iff.intro,
 intro,
 apply and.right a,
 intro,
 apply and.intro,
 exfalso,
 assumption,
 assumption
end 
--Question 14
example (p : Prop) : p ∨ false ↔ p := 
begin
 apply iff.intro,
 intro,
 apply or.elim a,
 intro,
 assumption,
 intro,
 exfalso,
 assumption,
 intro,
 apply or.inl,
 assumption
end
--Question 15
example (p q : Prop) : (¬p ∨ q) → (p → q) := 
begin
 intro,
 intro,
 apply or.elim a,
 intro,
 exfalso,
 apply a_2,
 assumption,
 intro,
 apply a_2 
end
--Question 16
example (p q : Prop) : ¬p → (p → q) := 
begin
intro,
intro,
exfalso,
apply a,
assumption 
end 
--Question 17
example (p : Prop) : p ∨ ¬p := 
begin
 apply or.inr,
 admit
end 
--Question 18
example (p q : Prop) : (¬q → ¬p) → (p → q) := 
begin
 intro,
 intro,
 admit
end 
--Question 19
example (p q : Prop) : (p → q) → (¬p ∨ q) := 
begin
 intro,
 apply or.inr,
 apply a,
 admit
end 
--Question 20
example (p q : Prop) : (((p → q) → p) → p) := 
begin 
 intro,
 apply a,
 intro,
 admit
end
--Question 21
example (p q : Prop) : ¬(p → q) → p ∧ ¬q := 
begin
 intro,
 apply and.intro,
 exfalso,
 admit
end
--Question 22
example (p q : Prop) : ¬(p ∧ q) → ¬p ∨ ¬q := 
begin
 intro,
 apply or.inl, 
 intro,
 apply a,
 apply and.intro,
 assumption,
 exfalso,
 apply a,
 admit
end
--Question 23
example (p r s : Prop) : (p → r ∨ s) → ((p → r) ∨ (p → s)) := 
begin
 intro,
 apply or.inr,
 intro,
 admit 
end
--Question 24
example (p q r : Prop) : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
begin
 apply iff.intro,
 intro,
 apply and.intro,
 intro,
 apply a,
 apply or.inl,
 assumption,
 intro,
 apply a,
 apply or.inr,
 assumption,
 intro,
 intro,
 apply and.left a,
 admit
end
--Question 25
example (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
begin
 apply iff.intro,
 intro,
 apply and.intro,
 intro,
 apply a,
 apply or.inl,
 assumption,
 intro,
 apply a,
 right,
 assumption,
 intro,
 intro,
 apply and.left a,
 apply or.elim a_1,
 intro,
 assumption,
 intro,
 exfalso,
 apply and.right a,
 assumption 
end
--Question 26
example (p : Prop) : ¬(p ↔ ¬ p) :=
begin
 intro,
 apply iff.elim_left a,
 admit 
end 

--Chapter 4 Exercises
variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop
--Question 1
example : (∃ x : α, r) → r := 
begin 
 intro h,
 cases h with x r,
 assumption 
end 
--Question 2
example  : r → (∃ x : α, r) := 
begin
 intro h,
 admit
end
--Question 3
example: (∃x: α, true) → (∀x, p x ∧ r) → (∀x, p x) ∧ r :=
begin
intro h,

assume H1 : (∃x: α, true),
assume H2 : (∀x, p x ∧ r),
obtain x0 T0, from H₁,
have H₃ : p x₀ ∧ r, from H₂ x₀,
have Hpx : p x₀, from and.left H₃,
have Hr : r, from and.right H₃,
have Hapx : (∀x, p x), from 
    (take x, and.left (H₂ x)),
show (∀x, p x) ∧ r, from and.intro Hapx Hr


example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
begin 
apply iff.intro,
intro h,
apply or.inl,
apply or.elim h,
apply iff.intro
 (assume ⟨a, (h1 : p a ∨ q a)⟩,
  or.elim h1
      (assume hpa : p a, or.inl ⟨a, hpa⟩)
      (assume hqa : q a, or.inr ⟨a, hqa⟩))
  (assume h : (∃ x, p x) ∨ (∃ x, q x),
    or.elim h
      (assume ⟨a, hpa⟩, ⟨a, (or.inl hpa)⟩)
      (assume ⟨a, hqa⟩, ⟨a, (or.inr hqa)⟩)) 

