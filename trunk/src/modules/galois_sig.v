
Require Import ssr.
Require Import lib.
Require Import groups.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

Module Type GALOIS.

  (* -------------------------------------------------------------------------- *)
  (*  Rings                                                                     *)
  (* -------------------------------------------------------------------------- *)


  (** Our rings are founded on decidable types, include the usual arithmetic 
      functions, 0 and 1.  *)
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

    (** Divides. *)
    Definition rdivides (a b:r) := exists a', a * a' = b.
    Notation "x |` y" := (rdivides x y) (at level 55).

    (** Gcd. *)
    CoInductive gcd (f g d:r) : Type :=
      Gcd : (d |` f) -> (d |` g) -> 
      (forall d', (d' |` f) -> (d' |` g) -> (d' |` d)) -> gcd f g d.

    (** Units. *)
    Definition unit (x:r) := exists x', (x * x' = 1).

    (** Associates. *)
    Definition associates x y := exists u : r, unit u /\ x = u * y.  

    (** Irreducible elements. *)
    Definition irreducible p := forall x y, x * y = p -> (unit x \/ unit y).

    (** Prime elements. *)
    Definition prime (p:r) := ~ (unit p) /\ irreducible p.

    (** Relatively prime elements. *)
    Definition rel_prime x y := forall d:r, gcd x y d -> unit d.

    (** a^b. *)
    Fixpoint pow (x:r) (n:nat) {struct n} : r := 
      if n is S n' then x * pow x n' else 1.

    (** Multiply an element by a natural number. *)
    Fixpoint cmul (n:nat) (a:r) {struct n} : r := 
      if n is S n' then a + cmul n' a else 1.

    (** The dot product of two sequences. *)
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

  (** Domains, or integral domains, have the property that if the product of 
      two elements is 0, one of the elements must be 0. *)
  Section Domain.

    Definition domainP (r:ring) := forall x1 x2:r, x1 * x2 = 0 -> x1 = 0 \/ x2 = 0.

    Structure domain : Type := Domain {
      dbase :> ring;
      integ : domainP dbase
    }.

  End Domain.

  (* -------------------------------------------------------------------------- *)
  (*  Euclidean Domains                                                         *)
  (* -------------------------------------------------------------------------- *)

  (** Euclidean domains admit a division algorithm with respect to a "degree"
      function. *)
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

  (** Fields have multiplicative inverses.  *)
  Section Field.

    Structure field : Type := Field {
      fbase  :> domain;
      invf   : fbase -> fbase;  
      unitPL : forall x : fbase, x <> 0 -> invf x * x = 1;
      nzP    : 1 <> 0 :> fbase;
      inv0   : invf 0 = 0
    }.

    Notation "x '^-1'" := (invf x) (at level 9, format "x '^-1'").

  End Field.

  Notation "x '^-1'" := (invf x) (at level 9, format "x '^-1'") : ring_scope.

  (* -------------------------------------------------------------------------- *)
  (*  Subrings                                                                  *)
  (* -------------------------------------------------------------------------- *)

  (** Subrings are simply sets of the underlying type, with some closure
      properties. *)
  Section Subring.

    Variable u:ring.

    Structure subring : Type := Subring {
      srbase :> set u;
      zerorP  : srbase 0;
      onerP   : srbase 1;
      addrP   : forall x y, srbase x -> srbase y -> srbase (x + y);
      mulrP   : forall x y, srbase x -> srbase y -> srbase (x * y);
      opprP   : forall x, srbase x -> srbase (- x)
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
  
  (** Subfields are subrings of fields, closed under inverse *)
  Section Subfield.

    Variable f:field.

    Structure subfield : Type := Subfield {
      sfbase :> subring f;
      invrP   : forall x, sfbase x -> sfbase (invf x)
    }.
    
    Axiom subfield_ext : forall h k: subfield, srbase h = srbase k -> h = k.

  End Subfield.

  (* -------------------------------------------------------------------------- *)
  (*  Ideals                                                                    *)
  (* -------------------------------------------------------------------------- *)

  (** Ideals are special subrings that are closed under multiplication by 
      arbitrary ring elements.  They are the equivalent of normal subgroups in
      group theory, in that you can factor by them to get new rings.  *)
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

    (** The whole ring is an ideal. *)
    Parameter ring_to_ideal : forall r:subring u, ideal.

    (** Maximal ideals are not subideals of any ideal but the entire ring. 
        Factoring by maximal ideals gives a field.  *)
    Definition maximal_ideal := 
      i <> ring_to_ideal r /\  
      forall j : ideal, sub_set i j -> j = i \/ j = ring_to_ideal r.

    (** You can get an ideal from a single element [a] by taking the product with
        all the elements of the ring with [a]. *)
    Parameter ideal_of_elem : forall a:u, ideal.

  End Ideal.

  (* -------------------------------------------------------------------------- *)
  (*  Homomorphisms                                                             *)
  (* -------------------------------------------------------------------------- *)

  (** Homomorphisms are functions between rings that preserve the
      ring operations. Note that we define them as restrictions of functions 
      to subrings of larger rings.  This is because later, when considering 
      field extensions, we will want to consider automorphisms with respect 
      to towers of fields.  Since we want to count automorphisms, we need to
      controll what happens to the elements outside of the intended subring.  
      We'll start with sending them to 0.  Another option would be to consider
      equivalence classes.  *)
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

    (** The kernel of a homomorphism is those elements that are sent to 0. *)
    Definition kernel (h:homo) := fun x => r x && (h x == 0).
    
    (** An isomorphism is a bijective homomorphism. *)
    Structure iso : Type := Iso {
      isbase :> homo;
      imonoP : forall x y, r x -> r y -> isbase x = isbase y -> x = y;
      iontoP : surj r s isbase
    }.

  End Homomorphism.

  (** An automorphism is an isomorphism from a subring to itself. *)
  Definition auto u r := type_to_eqType (@iso u u r r).

  (* -------------------------------------------------------------------------- *)
  (*  Quotients                                                                 *)
  (* -------------------------------------------------------------------------- *)

  (** The rings that arise by the usual factoring operation by ideals are called
      quotients.  *)
  Section Quotient.
    
    Variable U:ring.
    Variable R:subring U.
    Variable I:ideal R.

    (** Cosets of an ideal. *)
    Definition coset_pred (s:set U) := 
      exists a, s a /\ forall x, s x <-> exists i, I i /\ x = a + i.

    Structure coset : Type := Coset {
      cosetS :> set U; 
      coset_mem : coset_pred cosetS
    }.

    Definition eqcoset (c1 c2:coset) := Pb (forall x, cosetS c1 x == cosetS c2 x).
    Axiom eqcosetPx : reflect_eq eqcoset.
    Canonical Structure cosetData := EqType eqcosetPx.

    Parameter elem_of_coset : coset -> U.
    Parameter coset_of_elem : U -> coset.

    Definition addq c1 c2 := coset_of_elem ((elem_of_coset c1) + (elem_of_coset c2)).
    Definition mulq c1 c2 := coset_of_elem ((elem_of_coset c1) * (elem_of_coset c2)).
    Definition oppq c     := coset_of_elem (- (elem_of_coset c)).
    Definition zeroq      := coset_of_elem 0.
    Definition oneq       := coset_of_elem 1.

    Notation "x1 +` x2" := (addq x1 x2) (at level 50).
    Notation "x1 *` x2" := (mulq x1 x2) (at level 40).
    Notation "-` x"     := (oppq x) (at level 35).

    Axiom addqC    : forall c1 c2:cosetData, c1 +` c2 = c2 +` c1.
    Axiom addqA    : forall c1 c2 c3, c1 +` (c2 +` c3) = c1 +` c2 +` c3.
    Axiom addq0    : forall c, c +` zeroq = c.
    Axiom oppqL    : forall c, -` c +` c = zeroq.
    Axiom mulqC    : forall x y, x *` y = y *` x.
    Axiom mulqA    : forall c1 c2 c3, c1 *` (c2 *` c3) = c1 *` c2 *` c3.
    Axiom mul1q    : forall x, oneq *` x = x.
    Axiom distqPM  : forall x1 x2 x3, (x1 +` x2) *` x3 = x1 *` x3 +` x2 *` x3.
    Axiom distqMP  : forall x1 x2 x3, x1 *` (x2 +` x3) = x1 *` x2 +` x1 *` x3.

    Canonical Structure quotient := Ring addqC addqA addq0 oppqL mulqC mulqA mul1q distqPM distqMP.

  End Quotient.

  (* -------------------------------------------------------------------------- *)
  (*  Rings with Syntactic Zero                                                 *)
  (* -------------------------------------------------------------------------- *)

  (** In Coq, the computational nature of proof makes it convenient to syntactically
      distinguish 0 from the rest of the ring.  In particular, it makes proofs of
      polynomial properties much easier.  We can easily cast a ring to a ring as 
      defined earlier. *)
  Section Ringz.
    
    Notation "0" := (@Zero _).

    Section Axioms.

      Variable d' : eqType.
      Notation d := (withzeroData d').

      Definition lift_opp (f:d'->d') x :=
        match x with
          | Zero => 0
          | Nz x => Nz (f x)
        end.

      Definition lift_add (add:d'->d'->d) x y := 
        match x, y with 
          | Zero, _ => y
          | _, Zero => x
          | Nz x, Nz y => add x y
        end.

      Definition lift_mul (mul:d'->d'->d) x y := 
        match x, y with 
          | Nz x, Nz y => mul x y
          | _, _ => 0
        end.

      Variable addr' : d'->d'->d.
      Variable mulr' : d'->d'->d.
      Variable oppr' : d'->d'.
      Variable oner' : d'.

      Notation "x1 + x2" := (lift_add addr' x1 x2).
      Notation "x1 * x2" := (lift_mul mulr' x1 x2).
      Notation "- x" := (lift_opp oppr' x).
      Notation "1" := (Nz oner').

      Structure ringz_axioms : Type := Ringz_axioms {
        addC'    : forall x1 x2, x1 + x2 = x2 + x1;
        addA'    : forall x1 x2 x3, x1 + (x2 + x3) = (x1 + x2) + x3;   
        oppL'    : forall x,  - x + x = 0;
        mulC'    : forall x1 x2, x1 * x2 = x2 * x1;
        mulA'    : forall x1 x2 x3, x1 * (x2 * x3) = x1 * x2 * x3;
        mul1r'   : forall x, 1 * x = x;
        distPM'  : forall x1 x2 x3, (x1 + x2) * x3 = x1 * x3 + x2 * x3;
        distMP'  : forall x1 x2 x3, x1 * (x2 + x3) = x1 * x2 + x1 * x3
      }.

    End Axioms.

    Structure ringz : Type := Ringz {
      rbase'    : eqType;
      addr'     : rbase' -> rbase' -> withzero rbase';
      oppr'     : rbase' -> rbase';
      oner'     : rbase';
      mulr'     : rbase' -> rbase' -> withzero rbase';
      axioms    : ringz_axioms addr' mulr' oppr' oner'
    }.

    Definition rbasez r := withzeroData (rbase' r).
    Coercion rbasez : ringz >-> eqType.

    Variable r:ringz.

    Definition addrz (x y:r) := lift_add (@addr' r) x y.
    Definition mulrz (x y:r) := lift_mul (@mulr' r) x y.
    Definition opprz (x:r)   := lift_opp (@oppr' r) x.
    Definition onerz         := Nz (oner' r).

    Notation "x1 + x2" := (addrz x1 x2).
    Notation "x1 * x2" := (mulrz x1 x2).
    Notation "- x"     := (opprz x).    
    Notation "1"       := (onerz).      
    Notation "0"       := (@Zero _).

    Axiom addCz   : forall x y:r, x + y = y + x.
    Axiom addAz   : forall x y z:r, x + (y + z) = (x + y) + z. 
    Axiom addr0z  : forall x:r, x + 0 = x.
    Axiom oppLz   : forall x:r, -x + x = 0.
    Axiom mulAz   : forall x y z:r, x * (y * z) = (x * y) * z. 
    Axiom distPMz : forall x1 x2 x3:r, (x1 + x2) * x3 = (x1 * x3) + (x2 * x3).
    Axiom distMPz : forall x1 x2 x3:r, x1 * (x2 + x3) = (x1 * x2) + (x1 * x3).
    Axiom mul1rz  : forall x:r, 1 * x = x. 
    Axiom mulCz   : forall x y:r, x * y = y * x.

    Canonical Structure ringz_to_ring := Ring addCz addAz addr0z oppLz mulCz mulAz mul1rz distPMz distMPz.

  End Ringz.

  Delimit Scope ringz_scope with Z.
  Open Scope ringz_scope.

  Notation "x1 + x2" := (addrz x1 x2) : ringz_scope.
  Notation "x1 * x2" := (mulrz x1 x2) : ringz_scope.
  Notation "- x"     := (opprz x)     : ringz_scope.
  Notation "1"       := (onerz _)       : ringz_scope.
  Notation "0"       := (@Zero _)     : ringz_scope.

  Section Domainz.

    Structure domainz : Type := Domainz {
      dbasez    :> ringz;
      domainPz'  : forall x1 x2:rbase' dbasez, mulr' x1 x1 <> 0
    }.

    Variable d:domainz.

    Axiom domainPz : domainP (ringz_to_ring d).

    Canonical Structure domainz_to_domain := Domain domainPz.

  End Domainz.

  Section Fieldz.

    Structure fieldz : Type := Fieldz {
      fbasez :> domainz;
      invrz' : rbase' fbasez -> rbase' fbasez;
      unitPL0 : forall x, mulr' x (invrz' x) = onerz _
    }.

    Definition invrz (f:fieldz) (x:f) := if x is Nz x' then Nz(invrz' x') else 0.

    Variable f:fieldz.

    Axiom unitPL' : forall x:f, x <> 0 -> invrz x * x = 1.
    Axiom nzP'    : 1 <> 0 :> f.
    Axiom inv0'   : invrz 0 = 0 :> f.

    Canonical Structure fieldz_to_field := Field unitPL' nzP' inv0'.

  End Fieldz.

  (* -------------------------------------------------------------------------- *)
  (*  Polynomials                                                               *)
  (* -------------------------------------------------------------------------- *)
  
  (** Polynomials are sequences with a nonzero leading coefficient. They form
      a ring under the usual operations. *)
  Section Poly.

    Open Scope ringz_scope.
    
    Variable r:domainz.

    Inductive polyz : Type := Lc (c:rbase' r) | Pcons (h:r) (t:polyz).

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

    Definition onep := Lc (oner' _).

    Notation "1" := onep.

    Definition const c := if c is Nz c' then Nz (Lc c') else Zero.
    
    Definition X := Nz(0::onep).

    Definition horner c p := if p is Nz p' then Nz (c::p') else const c.

    Fixpoint addpz (p1 p2:polyz) {struct p2} : poly :=
      match p1, p2 with
        | h::t, Lc c => Nz (addrz h (Nz c) :: t)
        | Lc c, h::t => Nz (addrz (Nz c) h :: t)
        | Lc c1, Lc c2 => const (addr' c1 c2)
        | h1 :: t1, h2 :: t2 => horner (h1 + h2) (addpz t1 t2)
      end.

    Definition addp (p1 p2:poly) : poly := lift_add addpz p1 p2.
    
    Fixpoint cmulpz (c:rbase' r) (p:polyz) {struct p} : polyz := 
      match p with
        | Lc c' => Lc (if mulr' c c' is Nz c'' then c'' else c')
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
        | Lc c => Lc (oppr' c)
      end.

    Definition oppp (p:poly) : poly := if p is Nz p' then Nz(opppz p') else Zero.

    Fixpoint coefz (p:polyz) (i:nat) {struct i} : r := 
      match p, i with
        | h::t, S n => coefz t n
        | h::t, O => h
        | Lc c, O => Nz c
        | Lc c, S n => 0
      end.

    Definition coef p i : r := if p is Nz p' then coefz p' i else 0.

    Fixpoint coefsz (p:polyz) {struct p} : seq r := 
      match p with
        | Lc c => Adds (Nz c) seq0
        | h::t => Adds h (coefsz t)
      end.

    Definition coefs (p:poly) := if p is Nz p' then coefsz p' else seq0.

    Notation "x1 + x2" := (addp x1 x2).
    Notation "x1 * x2" := (mulp x1 x2).
    Notation "- x"     := (oppp x).
    Notation "x - y"   := (x + (- y)).
    Notation "0"       := (Zero).
    Notation "1"       := (Nz onep).
    Notation "x <= y"  := (nati.leq x y).
    Notation "x < y"   := (nati.lt x y).

    Axiom opppL     : forall p, - p + p = Zero.
    Axiom addpA     : forall p1 p2 p3, p1 + (p2 + p3) = p1 + p2 + p3.
    Axiom addpC     : forall p1 p2, p1 + p2 = p2 + p1.
    Axiom mul1p     : forall p, 1 * p = p.
    Axiom distpMP   : forall p1 p2 p3, p1 * (p2 + p3) = p1 * p2 + p1 * p3.
    Axiom distpPM   : forall p1 p2 p3, (p1 + p2) * p3 = p1 * p3 + p2 * p3.
    Axiom mulp1     : forall p, p * 1 = p.
    Axiom mulpA     : forall p1 p2 p3, p1 * (p2 * p3) = p1 * p2 * p3.
    Axiom mulpC     : forall p1 p2, p1 * p2 = p2 * p1.

    Canonical Structure poly_ring := Ringz (Ringz_axioms addpC addpA opppL mulpC mulpA mul1p distpPM distpMP).
    
    Fixpoint degpz (p:polyz) {struct p} : nat :=
      if p is h::t then S (degpz t) else O. 

    Definition degp p := if p is Nz p' then Nat (degpz p') else -oo.

    Definition constant p    := (degp p == Nat O) || (degp p == -oo).
    Definition linear p      := degp p == Nat 1.
    Definition quadratic p   := degp p == Nat 2.
    Definition cubic p       := degp p == Nat 3.
    Definition quartic p     := degp p == Nat 4.
    Definition quintic p     := degp p == Nat 5.

    Fixpoint lcz (p:polyz) {struct p} : rbase' r :=
      match p with 
        | Lc c => c
        | h::t => lcz t
      end.

    (** The leading coefficient. *)
    Definition lc (p:poly) : r := if p is Nz p' then Nz (lcz p') else 0.

    (** Monic. *)
    Definition monic p := lc p = (@onerz _).

    (** Irreducible.  How does this compare with [irreducible] of rings? Can I dispense
        with it?  *)
    Definition irreduciblep p := forall p1 p2, p = p1 * p2 -> degp p1 = Nat O \/ degp p2 = Nat O.

    Open Scope ring_scope.

    Fixpoint evalpz (p:polyz) (x:r) {struct p} : r :=
      match p with
        | Lc c => Nz c
        | c::p' => c + x * evalpz p' x
      end.

    (** Evaluate a polynomial at a point, treating it as a function in the 
        natural way.  *)
    Definition evalp p x := if p is Nz p' then evalpz p' x else 0.

    Notation "p @ x" := (evalp p x) (at level 36, right associativity).

    (** Root of a polynomial. *)
    Definition root (p : poly) x := p @ x == 0.

  End Poly.

  Notation "h :: t" := (Pcons h t) (at level 70)                      : ring_scope.
  Notation "p @ x"  := (evalp p x) (at level 36, right associativity) : ring_scope.
  
  (* -------------------------------------------------------------------------- *)
  (*  Linear Algebra                                                            *)
  (* -------------------------------------------------------------------------- *)

  (** {4 Linear algebra} We consider field extensions as vector spaces.  *)

  Section LinearAlgebra.

    Variable U:field.
    Variable F:subfield U.

    Open Scope dnat_scope.
    Notation "0" := (zeror _).

    (** K is a "field extension" of F if F is a subset of K.  *)
    Definition extension (K F : subfield U) := sub_set F K.

    (** Linear combinations.  *)
    Structure lcomb (vs : seq U) (x : U) : Prop := Lcomb {
      fs : seq U;
      lcomb1 : all F fs;
      lcomb2 : dot fs vs = x
    }.
    
    (** Span. *) 
    Definition span vs := fun x => Pb (lcomb vs x).

    (** Linearly independent. *)
    Fixpoint linind (vs : seq U) {struct vs} : bool := 
      if vs is Adds v vs' then ~~ (span vs' v) && linind vs' else true.

    (** Linearly dependent. *)
    Structure lindep (vs : seq U) : Prop := Linind_spec {
      fs : seq U;
      nz : U;
      lindep1 : nz != 0;
      lindep2 : fs nz;
      lindep3 : all F fs;
      lindep4 : (size fs) <= (size vs);
      lindep5 : dot fs vs = 0
    }.

    (** Basis of a vector space. *)
    Definition basis K bs := linind bs && Pb (span bs = srbase K).

    (** Finite dimensional vector spaces have a finite basis. *)
    Definition finD K := exists b, basis K b.

  End LinearAlgebra.

  (* -------------------------------------------------------------------------- *)
  (*  Splitting Fields                                                          *)
  (* -------------------------------------------------------------------------- *)
  
  Section SplittingField.

    Open Scope dnat_scope.
    Open Scope ring_scope.

    Variable U:fieldz.
    Coercion fieldz_to_field : fieldz >-> field.

    Axiom inhabit : inhabited (seq U).

    (** The index of one field in another is the dimension of the corresponding vector space. *)
    Definition index K F := if Pb (finD K F) then Nat(size(epsilon inhabit (basis K F))) else -oo.

    (** Finite extensions have a finite basis. *)
    Definition finite_ext (K F:subfield U) := extension K F /\ finD K F.

    (** A polynomial "splits" if it factors into linear factors. *)
    Structure splits_def (K F:subfield U) (p : poly U) (sseq : seq (poly U)) : Prop := Splits_def {
      splits1      : all F (coefs p);
      splits2      : all (@linear U) sseq;
      splits3      : all (all K \o (@coefs _)) sseq;
      splits4      : foldr (@mulp U) (Nz (onep _)) sseq = p
    }.
    
    Definition splits K F p := exists s, splits_def K F p s.

    (** K is a splitting field of a polynomial with coefficients in F if 
        p splits in K but no proper subfield.  *)
    Structure splitting_field (K F:subfield U) (p : poly U) : Prop := Splitting_field {
      spf1    : all F (coefs p);
      spf2    : splits K F p;
      spf3    : forall K' : subfield U, extension K K' -> splits K' F p -> K = K'
    }.

    (** An element is algebraic over F if it is a root of a polynomial with
        coefficients in F. *)
    Definition algebraic (F : subfield U) (a : U) := 
      exists p, all F (coefs p) /\  p <> Zero /\ root p a.

    (** An extension is algebraic if each of its elements is algebraic. *)
    Definition algebraic_ext (K F:subfield U) := forall a, K a -> algebraic F a.

  End SplittingField.

  (* -------------------------------------------------------------------------- *)
  (*  Galois Groups                                                             *)
  (* -------------------------------------------------------------------------- *)

  Section GaloisGroup.

    Variable U:fieldz.
    Variable K F:subfield U.

    Variable ext:algebraic_ext K F.
    
    (** An automorphism of K is called Galois if it fixes F. *)
    Definition gal_auto (a:auto K) :=  Pb(forall x, F x -> a x = x).

    (** The fixed elements of an automorphism. This set turns out 
        to be a field. *)
    Definition fixed_field1 (a:auto K) : set U := fun x => a x == x.

    (** The fixed elements of a finite sequence of automorphisms, also a field. *)
    Definition fixed_field (s:seq (auto K)) : set U := fun x => K x && all (fun a:auto K => a x == x) s.

    (** If K is a finite extension of F, then there are a finite
        number of Galois automorphisms.  *)
    Definition galois_groupP (g:seq (auto K)) := forall a, gal_auto a -> g a /\ count (set1 a) g = 1%N.

    (** An extension is called Galois if the fixed field of K is equal to F. *)
    Definition galois_ext := forall g, galois_groupP g -> fixed_field g = F.

    Structure galois_group_ty : Type := Galois_group_ty {
      gg_seq :> seq (auto K);
      ggP : galois_groupP gg_seq
    }.
    
    (** Somehow we'll construct Galois groups. *)
    Parameter galois_group : galois_group_ty.

  End GaloisGroup.

  Implicit Arguments fixed_field [U].

  (* -------------------------------------------------------------------------- *)
  (*  Fundamental Theorem                                                       *)
  (* -------------------------------------------------------------------------- *)

  Section FundamentalTheorem.
    
    Variable U : fieldz.
    Variable E B C F : subfield U.
    Variable H K : seq (auto E).

    Parameter extEF : galois_ext E F.
    Parameter extEB : extension E B.
    Parameter extBF : extension B F.
    Parameter magic_subfield : set U -> subfield U.
    
    Parameter subgroup : seq (auto E) -> bool.
    Parameter normal_subgroup : seq (auto E) -> bool.
    Parameter intersect_group : seq (auto E) -> seq (auto E) -> seq (auto E).
    Parameter union_group : seq (auto E) -> seq (auto E) -> seq (auto E).
    Parameter group_index : seq (auto E) -> seq (auto E) -> nati.
    Parameter intersect_field : set U -> set U -> subfield U.
    Parameter union_field : set U -> set U -> subfield U.
    
    Definition gamma : seq (auto E) -> set U := fun g => fixed_field E g.
    Definition phi   : subfield U -> seq (auto E) := fun H => galois_group E H.

    Axiom galois1a : bijective gamma.
    Axiom galois1b : comp gamma phi = id.
    Axiom galois2a : fixed_field E (galois_group E B) = B.
    Axiom galois2b : gg_seq(galois_group E (magic_subfield(fixed_field E H))) = H.
    Axiom galois3a : fixed_field E (union_group H K) = intersect_field (fixed_field E H) (fixed_field E K).
    Axiom galois3b : fixed_field E (intersect_group H K) = union_field (fixed_field E H) (fixed_field E K).
    Axiom galois3c : gg_seq(galois_group E (union_field B C)) = intersect_group (galois_group E B) (galois_group E C).
    Axiom galois3d : gg_seq(galois_group E (intersect_field B C)) = union_group (galois_group E B) (galois_group E C).
    Axiom galois4  : index B F = group_index (galois_group E F) (galois_group E B).
    Axiom galois5  : galois_ext B F <-> normal_subgroup (galois_group E B).
    
  End FundamentalTheorem.

End GALOIS.
  




