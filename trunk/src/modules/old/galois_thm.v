
    Axiom r1_i          : forall x:r, 0 * x = 0.
    Axiom r1_ii         : forall x:r, -x = -(1) * x.
    Axiom r1_iii        : forall x:r, -(1) * -x = x.


    Axiom r2 : forall (r:ring), (forall x a b:r, x <> 0 -> x * a = x * b -> a = b) <-> domainP r.
