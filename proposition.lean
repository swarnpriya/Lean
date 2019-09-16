
namespace Proposition
constant and : Prop -> Prop -> Prop
constant or : Prop -> Prop -> Prop 
constant not : Prop -> Prop 
constant imply : Prop -> Prop -> Prop 

variables p q r : Prop
#check and p q 
#check or p (and p q)

constant Proof : Prop -> Type
 constant and_comm : Π p q : Prop,
 Proof (implies (and p q) (and q p))
#check and_comm p q 
constant modus_ponens :
Π p q : Prop, Proof (implies p q) -> Proof p -> Proof q 

theorem t1 : p -> q -> p := fun hp : p, fun hq : q, hp
#print t1

theorem t2 : p -> q -> p :=
assume hp : p,
assume hq : q,
show p, from hp




