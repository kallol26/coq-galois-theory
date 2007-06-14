
Require Import ssr.
Require Import lib.
Require Import withzero.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

Open Scope dnat_scope.

Module Type GALOIS.

  (* -------------------------------------------------------------------------- *)
  (*  Rings                                                                     *)
  (* -------------------------------------------------------------------------- *)

   Section Ring.
  
    Section Axioms.

      Variable d' : eqType.
      Notation d := (withzeroData d').
      Notation "0" := (@Zero _).

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

      Structure ring_axioms : Type := Ring_axioms {
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

    Structure ring : Type := Ring {
      rbase'    : eqType;
      addr'     : rbase' -> rbase' -> withzero rbase';
      oppr'     : rbase' -> rbase';
      oner'     : rbase';
      mulr'     : rbase' -> rbase' -> withzero rbase';
      axioms    : ring_axioms addr' mulr' oppr' oner'
    }.

    Definition rbase r := withzeroData (rbase' r).
    Coercion rbase : ring >-> eqType.

    Variable r:ring.

    Definition addr (x y:r) := lift_add (@addr' r) x y.
    Definition mulr (x y:r) := lift_mul (@mulr' r) x y.
    Definition oppr (x:r)   := lift_opp (@oppr' r) x.
    Definition oner         := Nz (oner' r).

    Notation "x1 + x2" := (addr x1 x2).
    Notation "x1 * x2" := (mulr x1 x2).
    Notation "- x"     := (oppr x).
    Notation "x - y"   := (x + (- y)).
    Notation "1"       := (oner).
    Notation "0"       := (@Zero _).

    Definition divides (a b:r) := exists a', a * a' = b.
    Notation "x |` y" := (divides x y) (at level 55).

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

  Notation "x1 + x2" := (addr x1 x2)         : ring_scope.
  Notation "x1 * x2" := (mulr x1 x2)         : ring_scope.
  Notation "- x"     := (oppr x)             : ring_scope.
  Notation "0"       := (@Zero _)            : ring_scope.
  Notation "1"       := (oner _)             : ring_scope.
  Notation "x - y"   := (x + oppr y)         : ring_scope.
  Notation addrr   := (fun x y => y + x).
  Notation mulrr   := (fun x y => y * x).
  Open Scope ring_scope.

  (* -------------------------------------------------------------------------- *)
  (*  Domains                                                                   *)
  (* -------------------------------------------------------------------------- *)
 
  Section Domain.

    Structure domain : Type := Domain {
      dbase    :> ring;
      domainP  : forall x1 x2:rbase' dbase, mulr' x1 x1 <> 0
    }.

  End Domain.

  (* -------------------------------------------------------------------------- *)
  (*  Fields                                                                    *)
  (* -------------------------------------------------------------------------- *)

  Section Field.

    Structure field : Type := Field {
      fbase :> domain;
      invr' : rbase' fbase -> rbase' fbase;
      unitPL0 : forall x, mulr' x (invr' x) = 1
    }.

    Definition invr (f:field) (x:f) := if x is Nz x' then Nz(invr' x') else 0.

  End Field.

  Notation "x '^-1'" := (invr x) (at level 9, format "x '^-1'") : ring_scope.

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

  End Subring.

  (* -------------------------------------------------------------------------- *)
  (*  Subfields                                                                 *)
  (* -------------------------------------------------------------------------- *)

  Section Subfield.

    Variable f:field.

    Structure subfield : Type := Subfield {
      sfbase :> subring f;
      invP   : forall x, sfbase x -> sfbase (invr x)
    }.
    
  End Subfield.

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

    Definition kernel (h:homo) := fun x => r x && (h x == 0).
    
    Structure iso : Type := Iso {
      isbase :> homo;
      imonoP : forall x y, r x -> r y -> isbase x = isbase y -> x = y;
      iontoP : surj r s isbase
    }.

  End Homomorphism.
  
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

    Parameter ring_to_ideal : forall r:subring u, ideal.

    Variable i:ideal.

    Definition maximal_ideal := 
      i <> ring_to_ideal r /\  
      forall j : ideal, sub_set i j -> j = i \/ j = ring_to_ideal r.

    Parameter principle_ideal : forall a:u, ideal.

    Definition pid := forall i:ideal, exists a, i = principle_ideal a.

  End Ideal.

  (* -------------------------------------------------------------------------- *)
  (*  Quotients                                                                 *)
  (* -------------------------------------------------------------------------- *)

  Section Quotient.
    
    Variable U:ring.
    Variable R:subring U.
    Variable I:ideal R.

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

    Canonical Structure quotient := Ring (Ring_axioms addqC addqA oppqL mulqC mulqA mul1q distqPM distqMP).
  End Quotient.

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
    Notation "x <= y"  := (nati.leq x y).
    Notation "x < y"   := (nati.lt x y).

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
    Axiom degp_add         : forall p q:poly, nati.leq (degp (p + q)) (maxi (degp p) (degp q)).
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

  (* -------------------------------------------------------------------------- *)
  (*  Field Extensions                                                          *)
  (* -------------------------------------------------------------------------- *)

  Section Fields.

    Variable U:field.
    Variable K F : subfield U.

    Definition extension (K F : subfield U) := sub_set F K.

    Structure lcomb (vs' : seq U) (x : U) : Prop := Lcomb {
      fs' : seq U;
      fsP' : all F fs';
      leP : dot fs' vs' = x
    }.

    Structure lcomb_ext (vs' : seq U) (x : U) : Prop := Lcomb_ext {
      fs0 : seq U;
      fsP0 : all F fs0;
      leP0 : dot fs0 vs' = x;
      leP1 : size fs0 = size vs' 
    }. 
 
    Axiom lcomb_extend : forall vs x, lcomb vs x <-> lcomb_ext vs x.

    Definition span vs := fun x => Pb (lcomb vs x).

    Fixpoint linind (vs : seq U) : bool := 
      if vs is Adds v vs' then ~~ (span vs' v) && linind vs' else true.

    Structure lindep (vs : seq U) : Prop := Linind_spec {
      fs : seq U;
      nz : U;
      nzP : nz != 0;
      nzM : fs nz;
      fsP : all F fs;
      fvP : (size fs) <= (size vs);
      depP : dot fs vs = 0
    }.

    Definition basis bs := linind bs && Pb (span bs = srbase K).

    Definition finD := exists b, basis b.

    Axiom inhabit : inhabited (seq U).
  
    Definition index := if Pb finD then Nat(size(epsilon inhabit basis)) else -oo.

    Definition finite_ext := extension K F /\ finD.

    Structure splits_def (K F : subfield U) (p : poly U) (sseq : seq (polyData U)) : Prop := Splits_def {
      sseqP      : all F p;
      sseq_lin   : all (@linear U) sseq;
      sseq_k     : all (all K \o (@coefs _)) sseq;
      sseq_mul   : foldr (@mul (poly_idom U)) 1 sseq = p
    }.

    Definition splits K F p := exists s, splits_def K F p s.

    Structure splitting_field (K F : subfield U) (p : poly U) : Prop := Splitting_field {
      sfQ    : all F p;
      sf_spl : splits K F p;
      sfP    : forall K' : subfield U, extension K K' -> splits K' F p -> K = K'
    }.

    Structure min_poly (F : subfield U) (p : poly U) (a : U) : Prop := Minp {
      minpQ      : all F p;
      minp_monic : monic p;
      minpP      : root a p;
      minpH      : forall (p' : poly U), all F p' -> root a p' -> degp p <= degp p'
    }.

    Structure algebraic (F : subfield U) (a : U) : Prop := Algebraic_spec {
      algp : poly U;
      algP : all F algp;
      anz  : algp <> 0;
      art  : root a algp
    }.

  (* Note!  one is not a galois automorphism if K is not an extension of F,
     so take the fixed field to be the intersection of F,K *)
    Definition galois_auto (a : auto_ty K) := Pb (forall x, F x -> K x -> auto a x = x).

    Definition galois_fauto := fun (K F : subfield U) (Ekf : finite_ext K F) => 
      let (_, T) := finite_finite Ekf in
        FinType (proj2 T).

    Definition galois_group (K F : subfield U) : finGroupType. 

      Canonical Structure galois_group := Subgroup galois_mul galois_inv galois1.

      Pb(forall a, H a -> (auto a) x = x).

      Definition fixed_ring (H : subgroup(auto_group U)) : subring U.
   (* {{{ *)
move=> H.
exists (fixed H).
- abstract(
  apply/PbP; move=> a Ha /=;
  rewrite /auto;
  exact: homo0 (autoP a)).
- abstract(
  apply/PbP; move=> a Ha /=;
  exact: iso1 (autoP a)).
- abstract(
  move=> x y Hx Hy;
  move/PbP: (Hx) => Hx'; 
  move/PbP: (Hy) => Hy'; 
  apply/PbP; move=> a Ha;
  rewrite (homoAddP (autoP a)); eauto;
  rewrite Hx'; eauto;
  by rewrite Hy'; eauto).
- abstract(
  move=> x y Hx Hy;
  move/PbP: (Hx) => Hx'; 
  move/PbP: (Hy) => Hy'; 
  apply/PbP; move=> a Ha;
  rewrite (homoMulP (autoP a)); eauto;
  rewrite Hx'; eauto;
  by rewrite Hy'; eauto).
abstract(
move=> x Hx;
move/PbP: (Hx) => Hx'; apply/PbP;
move=> a Ha;
rewrite (homoOpp (autoP a)); eauto;
by rewrite Hx';eauto).
 (* }}} *)
    Defined.

    Definition fixed_field (H : subgroup(auto_group U)) : subfield U.
   (* {{{ *)
move=> H;exists (fixed_ring H).
abstract(
move=> x Hx; move/PbP: (Hx) => Hx'; apply/PbP;
move=> a Ha;
move: Hx; rewrite /= => Hx;
(case H0 : (x == 0); first by move/eqP: H0 => ->;rewrite inv0 (homo0 (autoP a)));
move/eqP: H0 => H0;
rewrite (inv_iso (autoP a)) => //;
by rewrite (Hx' a Ha)).
 (* }}} *)
  Defined.

  Definition normal_ext := fixed_field galois_group = F.






  End Fields.
  




