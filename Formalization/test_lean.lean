
universe u 
constant α : Type u
#check α

def foo : (ℕ → ℕ) → ℕ := λ f, f 0

#check foo
#print foo 

def double (x : ℕ) : ℕ := x + x
#print double
#check double 3
#reduce double 3

def square (x : ℕ) : ℕ := x * x
#check square 
#reduce square 3

constants p q : Prop
theorem t1 : p → q → p := λ hp : p, λ hq : q, hp 
#print t1

#check ¬p → p ↔ false

#reduce true ∧ false


theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
begin 
  apply and.intro,
  exact hp,
  apply and.intro,
  exact hq,
  exact hp
end

example : ∀ a b c : ℕ, a = b → a = c → c = b :=
begin 
intros,
transitivity a,
symmetry, 
assumption,
assumption
end 





