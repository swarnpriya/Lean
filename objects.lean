constant m : nat
#check m






#check nat

constants α β : Type
#check α 
constant f : Type -> Type 
#check f
#check fun x, f x
#check fun x, x
constant a : Type
#check (fun x : Type, f x) a
#reduce (fun x : Type, f x) a
#reduce (fun x, f x) a
#reduce tt && ff
#reduce tt && tt

constant m1 : nat 
constant n1 : nat
constant b : bool

#print "reducing pairs"
#reduce (m1, n1).2

#print "reducing boolean expressions"
#reduce b && ff
#reduce tt && ff

#print "reducing arithmatic expressions"
#reduce 2 + 3
constant n : nat
#reduce n + 3
#eval 2 * 3

#print "double-definition"
def double (x : ℕ) : ℕ := x + x
#check double 
#reduce double 3
def funDouble (x : ℕ) : ℕ -> ℕ := fun x, x + x
def do_twice (f : ℕ -> ℕ) : (ℕ -> ℕ) -> ℕ -> ℕ := fun f x, f (f x)

#print "square-definition"
def square (x : ℕ) : ℕ := x * x
#check square
#reduce square 8
def funSquare (x : ℕ) : ℕ -> ℕ := fun x, x * x

#print "local-definitions"
#check let y := 2 + 2 in y * y 
def t (x : ℕ) : ℕ := let y := x + x in y * y
#reduce t 4
#reduce let y := 2 + 2, z := y * y in z * z

def foo := let a := ℕ in fun x : a, x + 2

#print "Dependent Types" -- Dependent types are useful because they types can depend on parameters. Pi is dependent function type

namespace hide
universe u
constant list : Type u -> Type u
constant cons : Π α : Type u, α -> list α -> list α
constant nil : Π α : Type u, list α 
constant head : Π α : Type u, list α -> α 
constant tail : Π α : Type u, list α -> list α
constant append : Π α : Type u, list α -> list α -> list α 
end hide 

open list 
#check list 
#check @cons
#check @tail
#check @append
#check @nil








 

