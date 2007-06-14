
Require Import ssr.
Require Import lib.
Require Import withzero.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

Module Type RING.

  (* -------------------------------------------------------------------------- *)
  (*  Rings                                                                     *)
  (* -------------------------------------------------------------------------- *)

  Structure ring : Type := Ring {
    rbase   :> eqType;
    addr    : rbase -> rbase -> rbase;
    mulr    : rbase -> rbase -> rbase;
    oppr    : rbase -> rbase;
    zeror   : rbase;
    oner    : rbase;
    addC    : forall x1 x2, addr x1 x2 = addr x2 x1;
    addA    : forall x1 x2 x3, addr x1 (addr x2 x3) = addr (addr x1 x2) x3;
    addr0   : forall x, addr x zeror = x;
    oppL    : forall x, addr (oppr x) x = zeror;
    mulC    : forall x1 x2, mulr x1 x2 = mulr x2 x1;
    mulA    : forall x1 x2 x3, mulr x1 (mulr x2 x3) = mulr (mulr x1 x2) x3;
    mul1r   : forall x, mulr oner x = x;
    distPM  : forall x1 x2 x3, mulr (addr x1 x2) x3 = addr (mulr x1 x3) (mulr x2 x3);
    distMP  : forall x1 x2 x3, mulr x1 (addr x2 x3) = addr (mulr x1 x2) (mulr x1 x3)
  }.

  Implicit Arguments zeror [].
  Implicit Arguments oner [].

  Delimit Scope ring_scope with r.
  Bind Scope ring_scope with rbase.
  Open Scope ring_scope.

  Notation "x1 + x2" := (addr x1 x2)         : ring_scope.
  Notation "x1 * x2" := (mulr x1 x2)         : ring_scope.
  Notation "- x"     := (oppr x)             : ring_scope.
  Notation "0"       := (zeror _)            : ring_scope.
  Notation "1"       := (oner _)             : ring_scope.
  Notation "x - y"   := (x + oppr y)         : ring_scope.
  Notation addrr   := (fun x y => y + x).
  Notation mulrr   := (fun x y => y * x).

  Section Ring.

    Variable r:ring.

    Axiom add0r          : forall x:r, 0 + x = x.
    Axiom oppR           : forall x:r, x + -x = 0.
    Axiom addr_injl      : forall x:r, injective (addr x).
    Axiom addr_injr      : forall x:r, injective (addrr x).
    Axiom addKr          : forall x:r, cancel (addr x) (addr (- x)).
    Axiom addKrV         : forall x:r, cancel (addr (- x)) (addr x).
    Axiom addrK          : forall x:r, cancel (addrr x) (addrr (- x)).
    Axiom addrKV         : forall x:r, cancel (addrr (- x)) (addrr x).
    Axiom opp_opp        : forall x:r, -(-x) = x.
    Axiom opp_uniq       : forall x y y':r, x + y = 0 -> x + y' = 0 -> y = y'.
    Axiom opp_def        : forall x y:r, x + y = 0 -> y = - x.
    Axiom mul0r          : forall x:r, 0 * x = 0.
    Axiom mulr0          : forall x:r, x * 0 = 0.
    Axiom mul_oppL       : forall x y:r, - x * y = - (x * y).
    Axiom mul_oppR       : forall x y:r, x * - y = - (x * y).
    Axiom mul_opp_opp    : forall x y : r, - x * - y = x * y.
    Axiom opp_sym        : forall x y:r, - x = y -> x = - y.
    Axiom addrCA         : forall m n p:r, m + (n + p) = n + (m + p).
    Axiom opp0           : - 0 = 0 :> r.
    Axiom oppr0          : forall x:r, (-x == 0) = (x == 0).
    Axiom mulr1          : forall x:r, x * 1 = x.
    Axiom mul_opp1r      : forall x:r, -(1) * x = - x.
    Axiom mul_opp1_opp   : forall x:r, -(1) * - x = x.
    Axiom mul_opp1_opp1  : -(1) * -(1) = 1 :> r.
    Axiom opp_add        : forall x y : r, -(x + y) = - x - y.
    Axiom zero_ring      : 1 = 0 :> r -> forall x:r, x = 0.
    Axiom subr0          : forall x:r, x - 0 = x.
    Axiom sub0r          : forall x:r, 0 - x = - x.
    Axiom mulrCA         : forall m n p:r, m * (n * p) = n * (m * p).

    Definition rdivides (a b:r) := exists a', a * a' = b.
    Notation "x |` y" := (rdivides x y) (at level 55).

    Axiom div0           : forall c:r, c |` 0.
    Axiom div1           : forall c:r, 1 |` c.
    Axiom div_refl       : forall c:r, c |` c.
    Axiom div_add        : forall a b c:r, c |` a -> c |` b -> c |` a + b.
    Axiom div_mulL       : forall a b c:r, c |` a -> c |` a * b.
    Axiom div_trans      : forall a b c:r, a |` b -> b |` c -> a |` c.
    Axiom div_mulR       : forall a b c:r, c |` b -> c |` a * b.
    Axiom div_addP       : forall a b c:r, c |` a + b -> c |` a -> c |` b.

    CoInductive gcd (f g d:r) : Type :=
      Gcd : (d |` f) -> (d |` g) -> 
      (forall d', (d' |` f) -> (d' |` g) -> (d' |` d)) -> gcd f g d.

    Definition unit (x:r) := exists x', (x * x' = 1).

    Definition associates x y := exists u : r, unit u /\ x = u * y.  

    Definition irreducible p := forall x y, x * y = p -> (unit x \/ unit y).

    Definition prime (p:r) := ~ (unit p) /\ irreducible p.

    Definition rel_prime x y := forall d:r, gcd x y d -> unit d.

    Fixpoint pow (x:r) (n:nat) {struct n} : r := 
      if n is S n' then x * pow x n' else 1.

    Fixpoint cmul (n:nat) (a:r) {struct n} : r := 
      if n is S n' then a + cmul n' a else 1.

    Fixpoint dot (s1 s2:seq r) {struct s1} : r := 
      match s1,s2 with 
        | seq0, seq0 => 1
        | Adds h1 t1, Adds h2 t2 => h1 * h2 + dot t1 t2
        | _, _ => 0
      end.

  End Ring.

  Notation "x |` y" := (rdivides x y) (at level 55) : ring_scope.

  (* -------------------------------------------------------------------------- *)
  (*  Domains                                                                   *)
  (* -------------------------------------------------------------------------- *)

  Section Domain.

    Definition domainP (r:ring) := forall x1 x2:r, x1 * x2 = 0 -> x1 = 0 \/ x2 = 0.

    Structure domain : Type := Idom {
      dbase :> ring;
      integ : domainP dbase
    }.

    Axiom domain_cancel  : forall (r:ring), (forall x a b:r, x != 0 -> x * a = x * b -> a = b) <-> domainP r.
    Axiom domain_unit    : forall (r:ring), domainP r -> forall (f g u v:r), f <> 0 -> f = u * g -> g = v * f -> u * v = 1.

    Variable r:domain.

    Axiom mulr_injl      : forall x:r, x <> 0 -> injective (mulr x).
    Axiom mulr_injr      : forall z x y:r, z <> 0 -> (x * z = y * z) -> (x = y).
    Axiom div_sym        : forall a b:r, a |` b -> b |` a -> associates a b.

  End Domain.

  (* -------------------------------------------------------------------------- *)
  (*  Euclidean Domains                                                         *)
  (* -------------------------------------------------------------------------- *)

  Section Euclid.

    Inductive div_res (r:domain) (deg:r->nati) (a b:r) : Prop :=
      Div_res quo rem : a = quo * b + rem -> deg rem < deg b -> div_res deg a b.
    
    Structure euclid_ring : Type := Ering {
      ebase   :> domain;
      degr    : ebase -> nati;
      degr0   : forall x, degr x = -oo <-> x = 0;
      degr_lt : forall a b, b <> 0 -> degr a <= degr (a * b);
      degrP   : forall a b, b <> 0 -> div_res degr a b
    }.

  End Euclid.

  (* -------------------------------------------------------------------------- *)
  (*  Fields                                                                    *)
  (* -------------------------------------------------------------------------- *)

  Section Field.

    Structure field : Type := Field {
      fbase  :> domain;
      invf   : fbase -> fbase;  
      unitPL : forall x : fbase, x <> 0 -> invf x * x = 1;
      nzP    : 1 <> 0 :> fbase;
      inv0   : invf 0 = 0
    }.

    Notation "x '^-1'" := (invf x) (at level 9, format "x '^-1'").

    Variable f:field.

    Axiom invL         : forall (x:f), x <> 0 -> x^-1 * x = 1.
    Axiom mulKr        : forall (x:f), x <> 0 -> cancel (mulr x) (mulr x^-1).
    Axiom invR         : forall (x:f), x <> 0 -> x * x^-1 = 1.
    Axiom mulrK        : forall (x:f), x <> 0 -> cancel (mulrr x) (mulrr x^-1).
    Axiom mulKrV       : forall (x:f), x <> 0 -> cancel (mulr x^-1) (mulr x).
    Axiom mulrKV       : forall (x:f), x <> 0 -> cancel (mulrr x^-1) (mulrr x).
    Axiom inv_injR     : forall (x y:f), x <> 0 -> x * y = 1 -> y = x^-1.
    Axiom inv_injL     : forall (x y:f), x <> 0 -> y * x = 1 -> y = x^-1.
    Axiom opp1nz       : -(1) != 0 :> f.
    Axiom inv1         : 1^-1 = 1 :> f.
    Axiom opp_inv      : forall (x:f), x <> 0 -> (- x)^-1 = -(x ^-1).
    Axiom add_inv0     : forall (x y:f), x <> 0 -> y <> 0 -> x + y = 0 -> x ^-1 + y ^-1 = 0.

  End Field.

  Notation "x '^-1'" := (invf x) (at level 9, format "x '^-1'") : ring_scope.

  (* -------------------------------------------------------------------------- *)
  (*  Subrings                                                                  *)
  (* -------------------------------------------------------------------------- *)

  Section Subring.

    Variable u:ring.

    Structure subring : Type := Subring {
      srbase :> set u;
      zeroP  : srbase 0;
      oneP   : srbase 1;
      addP   : forall x y, srbase x -> srbase y -> srbase (x + y);
      mulP   : forall x y, srbase x -> srbase y -> srbase (x * y);
      oppP   : forall x, srbase x -> srbase (- x)
    }.

    Definition srunit (r:subring) x := exists y, r y /\ x * y = 1. 

    Axiom subring_ext  : forall (h k :subring), srbase h = srbase k -> h = k.
    Axiom subring_addl : forall (s:subring) x y, s x -> s (x + y) -> s y.
    Axiom subring_addr : forall (s:subring) x y, s y -> s (x + y) -> s x.
    Axiom subr_m1      : forall (s:subring), s (- (1)).

  End Subring.

  (* -------------------------------------------------------------------------- *)
  (*  Subfields                                                                 *)
  (* -------------------------------------------------------------------------- *)

  Section Subfield.

    Variable f:field.

    Structure subfield : Type := Subfield {
      sfbase :> subring f;
      invP   : forall x, sfbase x -> sfbase (invf x)
    }.
    
    Axiom subfield_ext : forall h k: subfield, srbase h = srbase k -> h = k.

  End Subfield.

  (* -------------------------------------------------------------------------- *)
  (*  Ideals                                                                    *)
  (* -------------------------------------------------------------------------- *)
  
  Section Ideal.
    
    Variable u:ring.
    Variable r:subring u.

    Structure ideal : Type := Ideal {
      idbase :> set u;
      id_ss  : sub_set idbase r;
      id0    : idbase 0;
      id_add : forall x y, idbase x -> idbase y -> idbase (x + y);
      idPL   : forall x y, idbase x -> r y -> idbase (x * y);
      idPR   : forall x y, r x -> idbase y -> idbase (x * y)
    }.

    Variable i j : ideal.
    Axiom id_opp     : forall x, i x -> i (- x).
    Axiom ideq       : (forall x, i x = j x) -> i = j.
    Axiom idbase_inj : idbase i = idbase j -> i = j.

    Parameter ring_to_ideal : forall r:subring u, ideal.

    Definition maximal_ideal := 
      i <> ring_to_ideal r /\  
      forall j : ideal, sub_set i j -> j = i \/ j = ring_to_ideal r.

    Parameter ideal_of_elem : forall a:u, ideal.

    Axiom ideal_unit : forall a, r a -> srunit r a -> ideal_of_elem a = ring_to_ideal r.

    Axiom unit_ideal : forall x, r x -> ideal_of_elem x = ring_to_ideal r -> srunit r x.

  End Ideal.

  (* -------------------------------------------------------------------------- *)
  (*  Homomorphisms                                                             *)
  (* -------------------------------------------------------------------------- *)

  Section Homomorphism.

    Variable u v:ring.
    Variable r:subring u.
    Variable s:subring v.

    Structure homo : Type := Homo {
      hbase    :> u->v;
      homoP    : forall x, r x -> s (hbase x);
      homoAddP : forall x y, r x -> r y -> hbase (x + y) = hbase x + hbase y;
      homoMulP : forall x y, r x -> r y -> hbase (x * y) = hbase x * hbase y;
      homoJunk : forall x, ~ (r x) -> hbase x = 0
    }.

    Axiom homo0 : forall h:homo, h 0 = 0.
    Axiom homoOpp : forall h:homo, forall x, r x -> h (- x) = - (h x).

    Definition kernel (h:homo) := fun x => r x && (h x == 0).
    
    Structure iso : Type := Iso {
      isbase :> homo;
      imonoP : forall x y, r x -> r y -> isbase x = isbase y -> x = y;
      iontoP : surj r s isbase
    }.

  End Homomorphism.

  (* -------------------------------------------------------------------------- *)
  (*  Rings with syntactic zero                                                 *)
  (* -------------------------------------------------------------------------- *)

  Section Ringz.
  
    Section Axioms.

      Variable d' : eqType.
      Notation d := (withzeroData d').
      Notation "0" := (@Zero _).

      Definition lift_opp (f : d' -> d') x :=
        match x with
          | Zero => 0
          | Nz x => Nz (f x)
        end.

      Definition lift_add (add : d' -> d' -> d) x y := 
        match x, y with 
          | Zero, _ => y
          | _, Zero => x
          | Nz x, Nz y => add x y
        end.

      Definition lift_addL (f : d' -> d' -> d) x y := 
        match x with
          | Zero => Nz y
          | Nz x => f x y
        end.

      Definition lift_addR (f : d' -> d' -> d) x y := 
        match y with
          | Zero => Nz x
          | Nz y => f x y
        end.

      Definition lift_mul (mul : d' -> d' -> d) x y := 
        match x, y with 
          | Nz x, Nz y => mul x y
          | _, _ => 0
        end.

      Definition lift_mulL (f : d' -> d' -> d) x y :=
        match x with
          | Zero => 0
          | Nz x => f x y
        end.

      Definition lift_mulR (f : d' -> d' -> d) x y := 
        match y with
          | Zero => 0
          | Nz y => f x y
        end.

      Variable addrz : d' -> d' -> d.
      Variable mulrz : d' -> d' -> d.
      Variable opprz : d' -> d'.
      Variable onerz : d'.

      Notation "x1 + x2" := (lift_add addrz x1 x2).
      Notation "x1 * x2" := (lift_mul mulrz x1 x2).
      Notation "- x" := (lift_opp opprz x).
      Notation "1" := (Nz onerz).

      Structure ringz_axioms : Type := Ringz_axioms {
        oppL'    : forall x : d,  - x + x = 0;
        addA'    : forall x1 x2 x3 : d, x1 + (x2 + x3) = (x1 + x2) + x3;   
        addC'    : forall x1 x2 : d, x1 + x2 = x2 + x1;
        mul1r'   : forall x, 1 * x = x;
        mulr1'   : forall x : d, x * 1 = x;
        mulA'    : forall x1 x2 x3 : d, x1 * (x2 * x3) = x1 * x2 * x3;
        distPM'  : forall x1 x2 x3 : d, (x1 + x2) * x3 = x1 * x3 + x2 * x3;
        distMP'  : forall x1 x2 x3 : d, x1 * (x2 + x3) = x1 * x2 + x1 * x3;
        mulC'    : forall x1 x2 : d, x1 * x2 = x2 * x1
      }.

    End Axioms.

    Structure ring_z : Type := Ring_z {
      rbase_z   : eqType;
      addr_z    : rbase_z -> rbase_z -> withzero rbase_z;
      oppr_z   : rbase_z -> rbase_z;
      oner_z    : rbase_z;
      mulr_z    : rbase_z -> rbase_z -> withzero rbase_z;
      axioms_z : ringz_axioms addr_z mulr_z oppr_z oner_z
    }.

    Definition ringz := withzero ring_z. 
    Definition rbasez r := withzeroData (rbase_z r).
    Coercion rbasez : ring_z >-> eqType.

    Definition mulrz (r : ring_z) (x y : r) : r := lift_mul (@mulr_z r) x y.
    Definition addrz (r : ring_z) (x y : r) : r := lift_add (@addr_z r) x y.
    Definition opprz (r : ring_z) (x : r) : r := lift_opp (@oppr_z r) x.
    Definition onerz (r : ring_z) : r := Nz (oner_z r).
    Implicit Arguments oner_z [r].

    Notation "x1 + x2" := (addrz x1 x2).
    Notation "x1 * x2" := (mulrz x1 x2).
    Notation "- x" := (opprz x).
    Notation "x - y" := (x + (- y)).
    Notation "1" := (onerz _).
    Notation "0" := (@Zero _).

    Variable r:ring_z.

    Axiom addCz   : forall x y:r, x + y = y + x.
    Axiom addAz   : forall x y z:r, x + (y + z) = (x + y) + z. 
    Axiom addr0z  : forall x:r, x + 0 = x.
    Axiom oppLz   : forall x:r, -x + x = 0.
    Axiom mulAz   : forall x y z:r, x * (y * z) = (x * y) * z. 
    Axiom distPMz : forall x1 x2 x3:r, (x1 + x2) * x3 = (x1 * x3) + (x2 * x3).
    Axiom distMPz : forall x1 x2 x3:r, x1 * (x2 + x3) = (x1 * x2) + (x1 * x3).
    Axiom mul1rz  : forall x:r, 1 * x = x. 
    Axiom mulCz   : forall x y:r, x * y = y * x.
    Axiom nzPz : 1 <> 0 :> r. 

    Canonical Structure ring_of_ringz := Ring addCz addAz addr0z oppLz mulCz mulAz mul1rz distPMz distMPz.

    Section Domain.

      Structure domain_z : Type := Domain_z {
        dbase_z :> ring_z;
        integz : forall x1 x2:dbase_z, mulrz x1 x2 <> 0
      }.

      Definition domainz := withzero domain_z.

    End Domain.

    Section Field.

      Structure field_z : Type := Field_z {
        fbase_z :> domain_z;
        finv_z : rbase_z fbase_z -> rbase_z fbase_z;
        unitPL0 : forall x, mulr_z x (finv_z x) = 1
      }.

      Definition fieldz := withzero field_z.

      Definition finvz (f:field_z) (x:f) := if x is Nz x' then Nz(finv_z x') else 0.

    End Field.

  End Ringz.

  (** 
    Variable r:ring.
    Variable r_z:ring_z.
    Variable rz:ringz.

    addr  : r -> r -> r
    addr_z : r_z -> r_z -> rz
    addrz : rz -> rz -> rz
   *)

  (* -------------------------------------------------------------------------- *)
  (*  Polynomials                                                               *)
  (* -------------------------------------------------------------------------- *)

  Section Poly.

    Variable r:domain_z.

    Inductive polyz : Type := Lc (c:rbase_z r) | Pcons (h:r) (t:polyz).

    Notation "h :: t" := (Pcons h t) (at level 70).

    Fixpoint eqpolyz (p1 p2:polyz) {struct p1} : bool := 
      match p1, p2 with
        | Lc c1, Lc c2 => c1 == c2
        | c1::t1, c2::t2 => (c1 == c2) && eqpolyz t1 t2 
        | _, _ => false
      end.

    Axiom eqpolyzPx : reflect_eq eqpolyz.

    Canonical Structure polyzData := EqType eqpolyzPx.

    Definition poly := (withzeroData polyzData).

    Definition onep := Lc (oner_z _).

    Notation "1" := onep.

    Definition const c := if c is Nz c' then Nz (Lc c') else Zero.
    
    Definition X := Nz(0::onep).

    Definition horner c p := if p is Nz p' then Nz (c::p') else const c.

    Fixpoint addpz (p1 p2:polyz) {struct p2} : poly :=
      match p1, p2 with
        | h::t, Lc c => Nz (addrz h (Nz c) :: t)
        | Lc c, h::t => Nz (addrz (Nz c) h :: t)
        | Lc c1, Lc c2 => const (addr_z c1 c2)
        | h1 :: t1, h2 :: t2 => horner (h1 + h2) (addpz t1 t2)
      end.

    Definition addp (p1 p2:poly) : poly := lift_add addpz p1 p2.
    
    Fixpoint cmulpz (c:rbase_z r) (p:polyz) {struct p} : polyz := 
      match p with
        | Lc c' => Lc (if mulr_z c c' is Nz c'' then c'' else c')
        | h :: t => (mulrz (Nz c) h)::(cmulpz c t) 
      end.

    Definition cmulp (c:r) (p:poly) : poly := 
      match c, p with
        | Zero, _ => Zero
        | _, Zero => Zero
        | Nz c', Nz p' => Nz (cmulpz c' p')
      end.

    Definition mulpz_aux (c:r) p : poly := if c is Nz c' then Nz (cmulpz c' p) else Zero.

    Fixpoint mulpz (p1 p2 : polyz) {struct p1} : poly := 
      match p1 with 
        | Lc c => Nz (cmulpz c p2)
        | h :: t => 
          addp (mulpz_aux h p2) (horner Zero (mulpz t p2))
      end.

    Definition mulp (p1 p2:poly) : poly := lift_mul mulpz p1 p2.

    Fixpoint opppz (p:polyz) {struct p} : polyz := 
      match p with
        | h::t => - h::opppz t 
        | Lc c => Lc (oppr_z c)
      end.

    Definition oppp (p:poly) : poly := if p is Nz p' then Nz(opppz p') else Zero.

    Fixpoint coefz (p:polyz) (i:nat) {struct i} : r := 
      match p, i with
        | h::t, S n => coefz t n
        | h::t, O => h
        | Lc c, O => Nz c
        | Lc c, S n => 0
      end.

    Definition coef (p:poly) i : r := if p is Nz p' then coefz p' i else 0.

    Notation "x1 + x2" := (addp x1 x2).
    Notation "x1 * x2" := (mulp x1 x2).
    Notation "- x"     := (oppp x).
    Notation "x - y"   := (x + (- y)).
    Notation "0"       := (Zero).
    Notation "1"       := (Nz onep).

    Axiom poly_indh : forall (P:poly->Prop),
      P Zero -> (forall c p, P p -> P (horner c p)) -> (forall p, P p).

    Axiom opppL     : forall p, - p + p = Zero.
    Axiom addpA     : forall p1 p2 p3, p1 + (p2 + p3) = p1 + p2 + p3.
    Axiom addpC     : forall p1 p2, p1 + p2 = p2 + p1.
    Axiom mul1p     : forall p, 1 * p = p.
    Axiom distpMP   : forall p1 p2 p3, p1 * (p2 + p3) = p1 * p2 + p1 * p3.
    Axiom distpPM   : forall p1 p2 p3, (p1 + p2) * p3 = p1 * p3 + p2 * p3.
    Axiom mulp1     : forall p, p * 1 = p.
    Axiom mulpA     : forall p1 p2 p3, p1 * (p2 * p3) = p1 * p2 * p3.
    Axiom mulpC     : forall p1 p2, p1 * p2 = p2 * p1.

    Canonical Structure poly_ring := Ring_z (Ringz_axioms opppL addpA addpC mul1p mulp1 mulpA distpPM distpMP mulpC).
    
    Fixpoint degpz (p:polyz) {struct p} : nat :=
      if p is h::t then S (degpz t) else O. 

    Definition degp p := if p is Nz p' then Nat (degpz p') else -oo.

    Definition constant p    := degp p = Nat O \/ degp p = -oo.
    Definition linear p      := degp p = Nat 1.
    Definition quadratic p   := degp p = Nat 2.
    Definition cubic p       := degp p = Nat 3.
    Definition quartic p     := degp p = Nat 4.
    Definition quintic p     := degp p = Nat 5.

    Axiom degp_const       : forall c, degp (const c) = if c is Nz _ then Nat O else -oo.
    Axiom degp_add_unevenL : forall p1 p2, degp p2 < degp p1 -> degp (p1 + p2) = degp p1.
    Axiom degp_add_unevenR : forall p1 p2, degp p1 < degp p2 -> degp (p1 + p2) = degp p2.
    Axiom degp_inf         : forall p, degp p = -oo -> p = 0.
    Axiom degp_add         : forall p q, degp (p + q) <= maxi (degp p) (degp q).
    Axiom degp_opp         : forall p, degp (- p) = degp p.

    Fixpoint lcz (p:polyz) {struct p} : rbase_z r :=
      match p with 
        | Lc c => c
        | h::t => lcz t
      end.

    Definition lc (p:poly) : r := if p is Nz p' then Nz (lcz p') else 0.

    Definition monic p := lc p = (@onerz _).

    Definition irreduciblep p := forall p1 p2, p = p1 * p2 -> degp p1 = Nat O \/ degp p2 = Nat O.



  End Poly.

  Notation "h :: t" := (Pcons h t) (at level 70) : ring_scope.








End RING.


