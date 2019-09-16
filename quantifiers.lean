variables (α : Type) (p q : α -> Prop)

example : (∀ x : α , p x ∧ q x) -> (∀ y : α, p y) :=
assume h : (∀ x : α, p x ∧  q x),
assume z : α,
show p z, from and.elim_left(h z)

variables (x y z : α) (r : α -> α -> Prop)
variable trans_r : ∀ x y z, r x y -> r y z -> r x z

variables a b c : α 
variables (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc

variables (α' : Type) (r' : α' -> α' -> Prop)
variable refl_r' : ∀ x, r' x x
variable symm_r' : ∀ {x y}, r' x y -> r' y x
variable trans_r' : ∀ {x y z}, r' x y -> r' y z -> r' x z
example (a b c d : α') (hab' : r' a b) (hcb' : r' c b) (hcd : r' c d): r' a d :=
trans_r' (trans_r' hab' (symm_r' hcb')) hcd

#check eq.refl
#check eq.trans
#check eq.symm

open eq
variables (α'' : Type) (a'' b'' c'' d'' : α'')
example (hab'' : a'' = b'') (hcb'' : c'' = b'') (hcd'' : c'' = d'') :
a'' = d'' :=
trans (trans hab'' (symm hcb'')) hcd''

example : 2 + 3 = 5 :=
rfl

variable α1 : Type
variables a1 a2 : α1
variables f g : α1 -> ℕ
variable h1 : a1 = a2
variable h2 : f = g

example : f a1 = f a2 := congr_arg f h1
example : f a1 = g a1 := congr_fun h2 a1
example : f a1 = g a2 := congr h2 h1

variables w1 x1 y1 z1 : ℤ
example : w1 + 0 = w1 := add_zero w1
example : 0 + w1 = w1 := zero_add w1
example : w1 * 1 = w1 := mul_one w1 
example : 1 * w1 = w1 := one_mul w1
example : -w1 + w1 = 0 := neg_add_self w1
example : w1 + -w1 = 0 := add_neg_self w1
example : w1 - w1 = 0 := sub_self w1
example : w1 + x1 = x1 + w1 := add_comm w1 x1
example : w1 + x1 + y1 = w1 + (x1 + y1) := add_assoc w1 x1 y1
example : w1 * x1 = x1 * w1 := mul_comm w1 x1
example : w1 * (x1 + y1) = w1 * x1 + w1 * y1 := mul_add w1 x1 y1
example : w1 * (x1 + y1) = w1 * x1 + w1 * y1 := left_distrib w1 x1 y1
example : (x1 + y1) * w1 = x1 * w1 + y1 * w1 := add_mul x1 y1 w1
example : (x1 + y1) * w1 = x1 * w1 + y1 * w1 := right_distrib x1 y1 w1
example : w1 * (x1 - y1) = w1 * x1 - w1 * y1 := mul_sub w1 x1 y1

variables x' y' z' : ℤ
example (x' y' z' : ℕ) : x' * (y' + z') = x' * y' + x' * z':= mul_add x' y' z'
example (x' y' z' : ℕ) : (x' + y') * z' = x' * z' + y' * z' := add_mul x' y' z'
example (x' y' z' : ℕ) : x' + y' + z' = x' + (y' + z') := add_assoc x' y' z'
example  (x' y' : ℕ) :
(x' + y') * (x' + y') = x' * x' + y' * x' + x' * y' + y' * y' :=
have h1 : (x' + y') * (x' + y') = (x' + y') * x' + (x' + y') * y', 
from mul_add (x' + y') x' y',
have h2 : (x' + y') * (x' + y') = x' * x' + y' * x' + (x' * y' + y' * y'),
from (add_mul x' y' x') ▸ (add_mul x' y' y') ▸ h1,
h2.trans (add_assoc (x' * x'+ y' * x') (x' * y') (y' * y')).symm

namespace hide 
variables (a' b' c' d' e' : ℕ)
variable h : a' = b'
variable hb : b' = c' + 1
variable hd : c' = d'
variable he : e' = 1 + d'
include h hb hd he
theorem T : a' = e' :=
calc 
a' = b' : by rw h
... = c' + 1 : by rw hb
... = d' + 1 : by rw hd
... = 1 + d' : by rw add_comm
... = e' : by rw he

--theorem T : a' = e' :=
--calc 
--a' = b' : h
--... = c' + 1 : hb
--... = d' + 1 : congr_arg _ hd
--... = 1 + d' : add_comm d' (1 : ℕ)
--... = e' : symm he

--theorem T' (a'' b'' c'' d'' : ℕ) 
--(h1' : a'' = b'') (h2' : b'' ≤ c'') (h3' : c'' + 1 < d'') : a'' < d'' :=
--calc
  -- a'' = b'' : h1'
   --... ≤ b'' + 1 : nat.lt_succ_self b''
   -- ... ≤ c'' + 1 : nat.succ_le_succ h2'
   -- ... < d'' : h3'

example (s p : ℕ) :
(s + p) * (s + p) = s * s + p * s + s * p + p * p :=
by simp [mul_add, add_mul]
--calc 
--(s + p) * (s + p) = (s + p) * s + (s + p) * p : by rw mul_add
--... = s * s + p * s  + (s + p) * p : by rw add_mul
--... = s * s + p * s + (s * p + p * p) : by rw add_mul
-- ... = s * s + p * s + s * p + p * p  : by rw ←add_assoc


-- Existential Quantifier 
open nat
example : ∃ x : ℕ , x > 0 :=
have h1 : 1 > 0 , from zero_lt_succ 0,
exists.intro 1 h1

example (x : ℕ) (h : x > 0) : ∃ y, y < x :=
exists.intro 0 h

example (x y z : ℕ) (hxy : x < y) (hyz : y < z) :
∃ w, x < w ∧ w < z :=
exists.intro y (and.intro hxy hyz)

def is_even (a : nat) := ∃ b, a = 2*b 

open classical
variables (α11 : Type) (p1 q1 : α11 -> Prop)
variable β : α11
variable r11 : Prop 

example : (∃ x : α11, r11) -> r11 :=
begin
exists.intro,
























 







