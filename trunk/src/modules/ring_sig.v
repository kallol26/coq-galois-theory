
Require Import ssr.
Require Import lib.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

Module Type RING.

  Structure ring : Type := Ring {
    rbase :> eqType;
    add    : rbase -> rbase -> rbase;
    mul    : rbase -> rbase -> rbase;
    opp    : rbase -> rbase;
    zero   : rbase;
    one    : rbase;
    addC   : forall x1 x2, add x1 x2 = add x2 x1;
    addA   : forall x1 x2 x3, add x1 (add x2 x3) = add (add x1 x2) x3;
    addr0  : forall x, add x zero = x;
    oppL   : forall x, add (opp x) x = zero;
    mulC   : forall x1 x2, mul x1 x2 = mul x2 x1;
    mulA   : forall x1 x2 x3, mul x1 (mul x2 x3) = mul (mul x1 x2) x3;
    mul1r  : forall x, mul one x = x;
    distPM : forall x1 x2 x3, mul (add x1 x2) x3 = add (mul x1 x3) (mul x2 x3);
    distMP : forall x1 x2 x3, mul x1 (add x2 x3) = add (mul x1 x2) (mul x1 x3)
  }.

  Notation "x1 + x2" := (add x1 x2).
  Notation "x1 * x2" := (mul x1 x2).
  Notation "- x"     := (opp x).
  Notation "0"       := (zero _).
  Notation "1"       := (one _).
  Notation "x - y"   := (x + opp y).
  Notation addr      := (fun x y => x + y).
  Notation mulr      := (fun x y => x * y).
  Notation addrr     := (fun x y => y + x).
  Notation mulrr     := (fun x y => y * x).

  Axiom add0r          : forall (r:ring) (x:r), 0 + x = x.
  Axiom oppR           : forall (r:ring) (x:r), x + -x = 0.
  Axiom addr_injl      : forall (r:ring) (x:r), injective (addr x).
  Axiom addr_injr      : forall (r:ring) (x:r), injective (addrr x).
  Axiom addKr          : forall (r:ring) (x:r), cancel (addr x) (addr (- x)).
  Axiom addKrV         : forall (r:ring) (x:r), cancel (addr (- x)) (addr x).
  Axiom addrK          : forall (r:ring) (x:r), cancel (addrr x) (addrr (- x)).
  Axiom addrKV         : forall (r:ring) (x:r), cancel (addrr (- x)) (addrr x).
  Axiom opp_opp        : forall (r:ring) (x:r), -(-x) = x.
  Axiom opp_uniq       : forall (r:ring) (x y y':r), x + y = 0 -> x + y' = 0 -> y = y'.
  Axiom opp_def        : forall (r:ring) (x y:r), x + y = 0 -> y = - x.
  Axiom mul0r          : forall (r:ring) (x:r), 0 * x = 0.
  Axiom mulr0          : forall (r:ring) (x:r), x * 0 = 0.
  Axiom mul_oppL       : forall (r:ring) (x y:r), - x * y = - (x * y).
  Axiom mul_oppR       : forall (r:ring) (x y:r), x * - y = - (x * y).
  Axiom mul_opp_opp    : forall (r:ring) (x y : r), - x * - y = x * y.
  Axiom opp_sym        : forall (r:ring) (x y:r), - x = y -> x = - y.
  Axiom addrCA         : forall (r:ring) (m n p:r), m + (n + p) = n + (m + p).
  Axiom opp0           : forall (r:ring), - 0 = 0 :> r.
  Axiom oppr0          : forall (r:ring) (x:r), (-x == 0) = (x == 0).
  Axiom mulr1          : forall (r:ring) (x:r), x * 1 = x.
  Axiom mul_opp1r      : forall (r:ring) (x:r), -(1) * x = - x.
  Axiom mul_opp1_opp   : forall (r:ring) (x:r), -(1) * - x = x.
  Axiom mul_opp1_opp1  : forall (r:ring), -(1) * -(1) = 1 :> r.
  Axiom opp_add        : forall (r:ring) (x y : r), -(x + y) = - x - y.
  Axiom zero_ring      : forall (r:ring), 1 = 0 :> r -> forall x:r, x = 0.
  Axiom subr0          : forall (r:ring) (x:r), x - 0 = x.
  Axiom sub0r          : forall (r:ring) (x:r), 0 - x = - x.
  Axiom mulrCA         : forall (r:ring) (m n p:r), m * (n * p) = n * (m * p).

  Definition rdivides (r:ring) (a b:r) := exists a', a * a' = b.
  Notation "x |` y" := (rdivides x y) (at level 55).

  Axiom div0           : forall (r:ring) (c:r), c |` 0.
  Axiom div1           : forall (r:ring) (c:r), 1 |` c.
  Axiom div_refl       : forall (r:ring) (c:r), c |` c.
  Axiom div_add        : forall (r:ring) (a b c:r), c |` a -> c |` b -> c |` a + b.
  Axiom div_mulL       : forall (r:ring) (a b c:r), c |` a -> c |` a * b.
  Axiom div_trans      : forall (r:ring) (a b c:r), a |` b -> b |` c -> a |` c.
  Axiom div_mulR       : forall (r:ring) (a b c:r), c |` b -> c |` a * b.
  Axiom div_addP       : forall (r:ring) (a b c:r), c |` a + b -> c |` a -> c |` b.

  CoInductive gcd (r:ring) (f g d:r) : Type :=
    Gcd : (d |` f) -> (d |` g) -> 
    (forall d', (d' |` f) -> (d' |` g) -> (d' |` d)) -> gcd f g d.

  Definition unit (r:ring) (x:r) := exists x', (x * x' = 1).

  Definition associates (r:ring) x y := exists u : r, unit u /\ x = u * y.  

  Definition irreducible (r:ring) (p:r) := forall x y, x * y = p -> (unit x \/ unit y).

  Definition prime (r:ring) (p:r) := ~ (unit p) /\ irreducible p.

  Definition rel_prime (r:ring) x y := forall d:r, gcd x y d -> unit d.

  Fixpoint pow (r:ring) (x:r) (n:nat) {struct n} : r := 
    if n is S n' then x * pow x n' else 1.

  Fixpoint cmul (r:ring) (n:nat) (a:r) {struct n} : r := 
    if n is S n' then a + cmul n' a else 1.

  Fixpoint dot (r:ring) (s1 s2:seq r) {struct s1} : r := 
    match s1,s2 with 
      | seq0, seq0 => 1
      | Adds h1 t1, Adds h2 t2 => h1 * h2 + dot t1 t2
      | _, _ => 0
    end.

  Definition domainP (r:ring) := forall (x1 x2:r), x1 * x2 = 0 -> x1 = 0 \/ x2 = 0.

  Structure domain : Type := Idom {
    ibase :> ring;
    integ : domainP ibase
  }.

  Axiom domain_cancel  : forall (r:ring), (forall x a b:r, x != 0 -> x * a = x * b -> a = b) <-> domainP r.
  Axiom domain_unit    : forall (r:ring), domainP r -> forall (f g u v:r), f <> 0 -> f = u * g -> g = v * f -> u * v = 1.
  Axiom mulr_injl      : forall (r:domain) (x:r), x <> 0 -> injective (mulr x).
  Axiom mulr_injr      : forall (r:domain) (z x y:r), z <> 0 -> (x * z = y * z) -> (x = y).
  Axiom div_sym        : forall (r:domain) (a b:r), a |` b -> b |` a -> associates a b.

  Structure field : Type := Field {
    fbase  :> domain;
    inv    : fbase -> fbase;  
    unitPL : forall x : fbase, x <> 0 -> inv x * x = 1;
    nzP    : 1 <> 0 :> fbase;
    inv0   : inv 0 = 0
  }.

  Notation "x '^-1'" := (inv x) (at level 9, format "x '^-1'").

  Axiom invL         : forall (f:field) (x:f), x <> 0 -> x^-1 * x = 1.
  Axiom mulKr        : forall (f:field) (x:f), x <> 0 -> cancel (mulr x) (mulr x^-1).
  Axiom invR         : forall (f:field) (x:f), x <> 0 -> x * x^-1 = 1.
  Axiom mulrK        : forall (f:field) (x:f), x <> 0 -> cancel (mulrr x) (mulrr x^-1).
  Axiom mulKrV       : forall (f:field) (x:f), x <> 0 -> cancel (mulr x^-1) (mulr x).
  Axiom mulrKV       : forall (f:field) (x:f), x <> 0 -> cancel (mulrr x^-1) (mulrr x).
  Axiom inv_injR     : forall (f:field) (x y:f), x <> 0 -> x * y = 1 -> y = x^-1.
  Axiom inv_injL     : forall (f:field) (x y:f), x <> 0 -> y * x = 1 -> y = x^-1.
  Axiom opp1nz       : forall (f:field), -(1) != 0 :> f.
  Axiom inv1         : forall (f:field), 1^-1 = 1 :> f.
  Axiom opp_inv      : forall (f:field) (x:f), x <> 0 -> (- x)^-1 = -(x ^-1).
  Axiom add_inv0     : forall (f:field) (x y:f), x <> 0 -> y <> 0 -> x + y = 0 -> x ^-1 + y ^-1 = 0.

  Inductive div_res (r:ring) (deg:r->nati) (a b:r) : Prop :=
    Div_res quo rem : a = quo * b + rem -> deg rem < deg b -> div_res deg a b.
  
  Structure euclid_ring : Type := Ering {
    ebase  :> domain;
    deg    : ebase -> nati;
    deg0   : forall x, deg x = -oo -> x = 0;
    deg0'  : forall x, x = 0 -> deg x = -oo;
    deg_lt : forall a b, b <> 0 -> deg a <= deg (a * b);
    degP   : forall a b, b <> 0 -> div_res deg a b
  }.

  Structure subring (r:ring) : Type := Subring {
    srbase :> set r;
    zeroP  : srbase 0;
    oneP   : srbase 1;
    addP   : forall x y:r, srbase x -> srbase y -> srbase (x + y);
    mulP   : forall x y:r, srbase x -> srbase y -> srbase (x * y);
    oppP   : forall x:r, srbase x -> srbase (- x)
  }.

  Definition srunit (u:ring) (r:subring u) x := exists y, r y /\ x * y = 1. 

(*   Parameter ring_to_subring : forall r:ring, subring r. *)
(*   Parameter subring_to_ring : forall r:ring, subring r -> ring. *)

  Axiom subring_ext  : forall (r:ring) (H K :subring r), srbase H = srbase K -> H = K.
  Axiom subring_addl : forall (r:ring) (s:subring r) x y, s x -> s (x + y) -> s y.
  Axiom subring_addr : forall (r:ring) (s:subring r) x y, s y -> s (x + y) -> s x.
  Axiom subr_m1      : forall (r:ring) (s:subring r), s (- (1:r)).

  Structure subfield (f:field) : Type := Subfield {
    sfbase :> subring f;
    invP   : forall x, sfbase x -> sfbase (inv x)
  }.

  Axiom subfield_ext : forall (f:field) (H K : subfield f), srbase H = srbase K -> H = K.

  Structure ideal (u:ring) (r:subring u) : Type := Ideal {
    idbase :> set u;
    id_ss  : sub_set idbase r;
    id0    : idbase 0;
    id_add : forall x y, idbase x -> idbase y -> idbase (x + y);
    idPL   : forall x y, idbase x -> r y -> idbase (x * y);
    idPR   : forall x y, r x -> idbase y -> idbase (x * y)
  }.

  Parameter ring_to_ideal : forall (u:ring) (r:subring u), ideal r.
  Coercion ring_to_ideal : subring >-> ideal.

  Axiom id_opp     : forall (u:ring) (r:subring u) (i:ideal r) x, i x -> i (- x).
  Axiom ideq       : forall (u:ring) (r:subring u) (i j : ideal r), (forall x, i x = j x) -> i = j.
  Axiom idbase_inj : forall (u:ring) (r:subring u) (i j : ideal r), idbase i = idbase j -> i = j.

  Definition maximal_ideal (u:ring) (r:subring u) (i:ideal r) := 
    i <> r /\  
    forall j : ideal r, sub_set i j -> j = i \/ j = r.

  Parameter ideal_of_elem : forall (u:ring) (r:subring u) (a : u), ideal r.

  Axiom ideal_unit : forall (u:ring) (r:subring u) a, r a -> srunit r a -> ideal_of_elem r a = r.
  Axiom unit_ideal : forall (u:ring) (r:subring u) x, r x -> ideal_of_elem r x = r -> srunit r x.

  Structure homo (u v:ring) (r:subring u) (s:subring v) (h : u -> v) : Prop := Homo {
    homoP    : forall x, r x -> s (h x);
    homoAddP : forall x y, r x -> r y -> h (x + y) = h x + h y;
    homoMulP : forall x y, r x -> r y -> h (x * y) = h x * h y;
    homoJunk : forall x, ~ (r x) -> h x = 0
  }.

  Axiom homo0 : forall (u v:ring) (r:subring u) (s:subring v) h, homo r s h -> h 0 = 0.
  Axiom homoOpp : forall (u v:ring) (r:subring u) (s:subring v) h, homo r s h -> forall x, r x -> h (- x) = - (h x).

  Definition kernel (u v:ring) (r:subring u) (s:subring v) h := fun x => r x && (h x == 0 :> v).
  
  Structure iso (u v:ring) (r:subring u) (s:subring v) (h : u -> v) : Prop := Iso {
    isobase :> homo r s h;
    imonoP : forall x y, r x -> r y -> h x = h y -> x = y;
    iontoP : surj r s h
  }.

  Definition isomorphic (u v:ring) (r:subring u) (s:subring v) := exists h, iso r s h.

End RING.


