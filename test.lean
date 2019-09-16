-- BEGIN
theorem and_commutative (p q : Prop) : p /\ q -> q /\ p :=
assume hpq : p /\ q,
have hp : p, from and. left hpq,
have hq : q, from and. right hpq,
show p /\ q, from and. intro hq hq
-- END

