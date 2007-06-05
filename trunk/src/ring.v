(** 
  ** The ring ([ring]) structure and variants such as integral domains ([idom]) and fields ([field]).
*)

Require Import ssr.
Require Import lib.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

(** Rings *)

Section RingAxioms.

Variable R : eqType.
Variable add : R -> R -> R.
Variable mul : R -> R -> R.
Variable opp : R -> R.
Variable zero : R.
Variable one : R.

Notation "x1 + x2" := (add x1 x2).
Notation "x1 * x2" := (mul x1 x2).
Notation "- x" := (opp x). 
Notation "0" := zero. 
Notation "x - y" := (x + opp y).

Structure ring_axioms : Prop := Ring_axioms {
  addC': forall x1 x2 : R, x1 + x2 = x2 + x1;
  addA': forall x1 x2 x3 : R, x1 + (x2 + x3) = (x1 + x2) + x3;
  add0r' : forall x : R, x + 0 = x;
  oppL' : forall x : R, - x + x = 0;
  mulA' : forall x1 x2 x3 : R, x1 * (x2 * x3) = x1 * x2 * x3;
  distPM' : forall x1 x2 x3 : R, (x1 + x2) * x3 = x1 * x3 + x2 * x3;
  distMP' : forall x1 x2 x3 : R, x1 * (x2 + x3) = x1 * x2 + x1 * x3;
  mul1r' : forall x : R, one * x = x;
  mulr1' : forall x : R, x * one = x;
  mulC' : forall x1 x2 : R, x1 * x2 = x2 * x1
}.

End RingAxioms.


Module Ring.

Structure ring : Type := Ring {
  rbase :> eqType;
  add : rbase -> rbase -> rbase;
  mul : rbase -> rbase -> rbase;
  opp : rbase -> rbase;
  zero : rbase;
  one : rbase;
  axioms : ring_axioms add mul opp zero one
}.

End Ring.


Delimit Scope ring_scope with R.
Bind Scope ring_scope with Ring.rbase.

Arguments Scope Ring.add [_ ring_scope ring_scope].
Arguments Scope Ring.mul [_ ring_scope ring_scope].
Arguments Scope Ring.opp [_ ring_scope].

Definition addr := nosimpl Ring.add.
Definition oppr := nosimpl Ring.opp.
Definition mulr := nosimpl Ring.mul.
Definition zeror := nosimpl Ring.zero.
Definition oner := nosimpl Ring.one.

Implicit Arguments Ring.zero [].
Implicit Arguments Ring.one [].

Open Scope ring_scope.
Notation ring := Ring.ring (only parsing).
Notation "x1 + x2" := (addr x1 x2) : ring_scope.
Notation "x1 * x2" := (mulr x1 x2) : ring_scope.
Notation "- x" := (oppr x) : ring_scope.
Notation "0" := (zeror _) : ring_scope.
Notation "1" := (oner _) : ring_scope.
Notation "x - y" := (x + oppr y) : ring_scope.
Notation addrr := (fun x y => y + x).
Notation mulrr := (fun x y => y * x).

(** Identities and Basic Lemmas *)

Section Rings.

Variable R : ring.

Notation axioms := Ring.axioms.

Lemma oppL : forall x : R, -x + x = 0.
Proof. exact: oppL' (axioms _). Qed. 

Lemma addr0 : forall x: R, x + 0 = x.
Proof. exact: add0r' (axioms _). Qed.

Lemma mulA : forall x y z : R, x * (y * z) = x * y * z. 
Proof. exact: mulA' (axioms _). Qed.

Lemma distPM : forall x1 x2 x3 : R, (x1 + x2) * x3 = (x1 * x3) + (x2 * x3).
Proof.  exact: distPM' (axioms _). Qed.

Lemma distMP : forall x1 x2 x3 : R, x1 * (x2 + x3) = (x1 * x2) + (x1 * x3).
Proof. exact: distMP' (axioms _). Qed.

Lemma addC : forall x y : R, x + y = y + x.
Proof. exact: addC' (axioms _). Qed.

Lemma addA : forall x y z : R, x + (y + z) = (x + y) + z. 
Proof. exact: addA' (axioms _). Qed.

Lemma add0r : forall x : R, 0 + x = x.
Proof. move=> x; rewrite addC; exact: addr0. Qed.

Lemma oppR : forall x : R, x + -x = 0.
Proof. move=> x. rewrite addC. exact: oppL. Qed.

Lemma addr_injl : forall x : R, injective (addr x).
Proof. by move=> x y z; move/(congr1 (addr (-x))); rewrite !addA !oppL !add0r. Qed.

Lemma addr_injr : forall x : R, injective (addrr x).
Proof. by move=> x y z /=; rewrite addC [z + _]addC; exact: addr_injl. Qed.

Lemma addKr : forall x : R, cancel (addr x) (addr (- x)).
Proof. by move=> x y; rewrite addA oppL add0r. Qed.

Lemma addKrV : forall x : R, cancel (addr (- x)) (addr x).
Proof. by move=> x y; rewrite addA oppR add0r. Qed.

Lemma addrK : forall x : R, cancel (addrr x) (addrr (- x)).
Proof. by move=> x y; rewrite -addA oppR addr0. Qed.

Lemma addrKV : forall x : R, cancel (addrr (- x)) (addrr x).
Proof. by move=> x y; rewrite -addA oppL addr0. Qed.

Lemma opp_opp : forall x : R, -(-x) = x.
Proof. by move=> x; apply: (@addr_injr (- x)); rewrite oppL oppR. Qed.

Lemma opp_uniq : forall x y y' : R, x + y = 0 -> x + y' = 0 -> y = y'.
Proof. by move=> x y y' H H'; apply (@addr_injl x); rewrite H H'. Qed.

Lemma opp_def : forall x y : R, x + y = 0 -> y = - x.
Proof. move=> x y H; apply (@opp_uniq x);auto; by rewrite oppR. Qed.

(** # <a href=http://code.google.com/p/coq-galois-theory/wiki/TheoremTimeline> ROTMAN: Theorem 1(i) </a> # *)
Lemma mul0r : forall x : R, 0 * x = 0.
Proof. by move=> x; apply (@addr_injr (0 * x)); rewrite -distPM !add0r. Qed.

Lemma mulr0 : forall x : R, x * 0 = 0.
Proof. by move=> x; apply (@addr_injr (x * 0)); rewrite -distMP !add0r. Qed.

Lemma mul_oppL : forall x y : R, - x * y = - (x * y).
Proof. by move=> x y; apply (@opp_uniq (x * y));rewrite -?distPM oppR ?mul0r. Qed. 
  
Lemma mul_oppR : forall x y : R, x * - y = - (x * y).
Proof. by move=> x y; apply (@opp_uniq (x * y)); rewrite -?distMP oppR ?mulr0. Qed.

Lemma mul_opp_opp : forall x y : R, - x * - y = x * y.
Proof. by move=> x y; rewrite mul_oppR mul_oppL opp_opp. Qed.

Lemma opp_sym : forall x y : R, - x = y -> x = - y.
Proof. by move=> x y H; rewrite -H; symmetry; exact: opp_opp. Qed.

Lemma addrCA : forall m n p : R, m + (n + p) = n + (m + p).
Proof. by move=> m n p; rewrite addA [m + _]addC addA. Qed.

Lemma opp0 : - 0 = 0 :> R.
Proof. by apply (@addr_injr 0); rewrite oppL !addr0. Qed.

Lemma oppr0 : forall x : R, (-x == 0) = (x == 0).
Proof. 
 (* {{{ *)

move=> x. 
apply/eqP.
case H : (_ == _) => [|H']; first by rewrite (eqP H) opp0.
move: (congr1 (@oppr _) H).
rewrite opp_opp opp0 => H0.
by rewrite H0 eq_refl in H'.

 (* }}} *)
Qed.

Lemma mul1r : forall x : R, 1 * x = x. 
Proof. exact: mul1r' (axioms _). Qed.

Lemma mulr1 : forall x : R, x * 1 = x.
Proof. exact: mulr1' (axioms _). Qed.

(** # <a href=http://code.google.com/p/coq-galois-theory/wiki/TheoremTimeline> ROTMAN: Theorem 1(ii) </a> # *)
Lemma mul_opp1r : forall x : R, -(1) * x = - x.
Proof. by move=> x; apply (@addr_injl x); rewrite oppR mul_oppL mul1r oppR. Qed.

(** # <a href=http://code.google.com/p/coq-galois-theory/wiki/TheoremTimeline> ROTMAN: Theorem 1(iii) </a> # *)
Lemma mul_opp1_opp : forall x : R, -(1) * - x = x.
Proof. by move=> x; rewrite mul_opp1r opp_opp. Qed.

Lemma mul_opp1_opp1 : -(1) * -(1) = 1 :> R.
Proof.  exact: mul_opp1_opp. Qed.

Lemma opp_add : forall x y : R, -(x + y) = - x - y.
Proof. by move=> x y; rewrite -mul_opp1r distMP !mul_opp1r. Qed.

Lemma zero_ring : (1:R) = 0 -> forall x : R, x = 0.
Proof. by move=> H x; rewrite -[x]mul1r H mul0r. Qed.

Lemma subr0 : forall x : R, x - 0 = x.
Proof. by rewrite opp0; exact: addr0. Qed.

Lemma sub0r : forall x : R, 0 - x = - x.
Proof. by move=> x; rewrite add0r. Qed.

Lemma mulC : forall x y : R, x * y = y * x.
Proof. exact: mulC' (axioms _). Qed.

Lemma mulrCA : forall m n p : R, m * (n * p) = n * (m * p).
Proof. by move=> m n p; rewrite mulA [m * _]mulC mulA. Qed.

Definition rdivides a b := exists a' : R, a * a' = b.

Notation "x |` y" := (rdivides x y) (at level 55).

Lemma div0 : forall c : R, c |` 0.
Proof. exists (0:R); exact: mulr0. Qed.

Lemma div1 : forall c : R, 1 |` c.
Proof. by move=> c; exists c; rewrite mul1r. Qed.

Lemma div_refl : forall c : R, c |` c.
Proof. by move=> x; exists (1 : R); rewrite mulr1. Qed.

Lemma div_add : forall a b c : R, c |` a -> c |` b -> c |` a + b.
Proof. 
 (* {{{ *)

move=> a b c [a' <-] [b' <-].
rewrite -distMP.
by exists (a' + b').

 (* }}} *)
Qed.

Lemma div_mulL : forall a b c : R, c |` a -> c |` a * b.
Proof. by move=> a b c [a' <-]; exists (a' * b); rewrite mulA. Qed.

Lemma div_trans : forall a b c : R, a |` b -> b |` c -> a |` c.
Proof. by move=> a b c [a' <-] [b' <-]; rewrite -mulA; exists (a' * b'). Qed.

Lemma div_mulR : forall a b c : R, c |` b -> c |` a * b.
Proof. by move=> a b c [b' <-]; exists (a * b'); rewrite mulC -mulA [b' * _]mulC. Qed.

Lemma div_addP : forall a b c : R, c |` a + b -> c |` a -> c |` b.
Proof.
 (* {{{ *)

move=> a b c [d Hd] [a' Ha'].
rewrite -Ha' in Hd.
move: (canLR Hd (addKr (c * a'))).
rewrite -mul_oppR -distMP.
by exists (- a' + d).

 (* }}} *)
Qed.

(** Definitions *)

CoInductive gcd (f g d : R) : Type :=
  Gcd : (d |` f) -> (d |` g) -> 
       (forall d', (d' |` f) -> (d' |` g) -> (d' |` d)) -> gcd f g d.

Definition unit (x : R) := exists x', (x * x' = 1).

Lemma unit_nz : (1:R) <> 0 -> forall u, unit u -> u <> (0:R).
Proof. by move=> H u [u' Hu'] H'; rewrite H' mul0r in Hu'; move/esym: Hu'. Qed.

Definition associates x y := exists u : R, unit u /\ x = u * y.  

Definition irreducible (p : R) := forall x y, x * y = p -> (unit x \/ unit y).

Definition prime (p : R) := ~ (unit p) /\ irreducible p.

Definition rel_prime x y := forall d : R, gcd x y d -> unit d.

Fixpoint pow (x : R) (n : nat) {struct n} : R := 
  if n is S n' then x * pow x n' else 1.

Fixpoint cmul (n : nat) (a : R) {struct n} : R := 
  if n is S n' then a + cmul n' a else 1.

Fixpoint dot (s1 s2 : seq R) {struct s1} : R := 
  match s1,s2 with 
    | seq0, seq0 => 1%R
    | Adds h1 t1, Adds h2 t2 => h1 * h2 + dot t1 t2
    | _, _ => 0
  end.

Definition domainP := forall x1 x2 : R, x1 * x2 = 0 -> x1 = 0 \/ x2 = 0.

(** # <a href=http://code.google.com/p/coq-galois-theory/wiki/TheoremTimeline> ROTMAN: Theorem 2</a> # *)
Lemma domain_cancel : (forall r a b : R, r != 0 -> r * a = r * b -> a = b) <-> domainP.
Proof.
 (* {{{ *)
split.
  move=> H x1 x2 H1.
  case H2 : (x1 == 0).
  left; by apply/eqP.
  right.
  move/negbT: H2.
  move/(H x1 x2 0).
  apply.
  by rewrite mulr0.
move=> H r a b H1 H2.
have: r * (a - b) = 0 by rewrite distMP mul_oppR H2 oppR.
move/(H _ _) => [].
  by move/eqP: H1.
move=> H3.
apply(@addr_injr (-b)).
by rewrite H3 oppR.
 (* }}} *)
Qed.

(** # <a href=http://code.google.com/p/coq-galois-theory/wiki/TheoremTimeline> ROTMAN: Exercise 4</a> # *)
Lemma domain_unit : domainP -> forall f g u v : R, f <> 0 -> f = u * g -> g = v * f -> u * v = 1.
Proof.
 (* {{{ *)
move=> H f g u v Hf Hfg Hgf.
move: Hfg.
rewrite {}Hgf mulA -{1}(@mul1r f) => Hfg.
move: {Hfg}(comb (addrr (- (1 * f))) Hfg).
rewrite oppR -mul_oppL -distPM.
move=> Hg.
move: {Hg}(sym_eq Hg).
move/H.
move=> [] //.
move/(comb (addrr 1)).
by rewrite -addA oppL addr0 add0r.
 (* }}} *)
Qed.

End Rings.

Notation "x |` y" := (rdivides x y) (at level 55) : ring_scope.
Notation "x ^ n" := (pow x n) : ring_scope.

Prenex Implicits unit.

(* -------------------------------------------------------------------------- *)
(*  Integral domains                                                          *)
(* -------------------------------------------------------------------------- *)

(** Integral domains *)
Structure domain : Type := Idom {
  ibase :> ring;
  integ : domainP ibase
}.

Section Domain.

Variable R : domain.

Lemma mulr_injl : forall x : R, x <> 0 -> injective (mulr x).
Proof.
 (* {{{ *)
move=> x Hx y z Hxy.
rewrite -(add0r (x * z)) in Hxy.
move/(fun H => canLR H (addrK _)) : Hxy.
rewrite -mul_oppR -distMP.
move/integ => [|] //.
move/(fun H => canRL H (addrKV _)).
by rewrite add0r.
 (* }}} *)
Qed.

Lemma mulr_injr : forall z x y : R, z <> 0 -> (x * z = y * z) -> (x = y).
Proof. by move=> z x y H0 H; apply: (mulr_injl H0); rewrite mulC H mulC. Qed.
Open Scope ring_scope.

Lemma div_sym : forall a b : R, a |` b -> b |` a -> associates a b.
Proof.
 (* {{{ *)
move=> a b [a' Ha'] [b' Hb'].
case Ha : (a == 0); move/eqP: Ha => Ha.
  have Hb : (b = 0) by symmetry; rewrite Ha mul0r in Ha'.
  exists (1:R); split; first by exists (1:R); rewrite mulr1.
  by rewrite Ha Hb mulr0.
exists b'.
split.
  exists a'.
  rewrite -Ha' in Hb'.
  rewrite mulC.
  apply: (mulr_injl Ha).
  by rewrite mulA mulr1.
by rewrite -Hb' mulC.
 (* }}} *)
Qed.  

End Domain. 

(** Fields *)

Module Field.

Structure field : Type := Field {
  fbase :> domain;
  inv : fbase -> fbase;  
  unitPL : forall x : fbase, x <> 0 -> inv x * x = 1;
  nzP : 1 <> 0 :> fbase;
  inv0 : inv 0 = 0
}.

End Field.

Notation field := Field.field (only parsing).
Arguments Scope Field.inv [_ ring_scope].

Definition invf := nosimpl Field.inv.

Notation "x '^-1'" := (invf x) (at level 9, format "x '^-1'") : ring_scope.

(** Euclidean rings *)

Open Scope nati_scope.
Open Scope ring_scope.

Inductive div_res (R : ring) (deg : R -> nati) (a b : R) : Prop :=
  Div_res q r : a = q * b + r -> deg r < deg b -> div_res deg a b.

Structure euclid_ring : Type := Ering {
  ebase :> domain;
  deg : ebase -> nati;
  deg0 : forall x, deg x = -oo -> x = 0;
  deg0' : forall x, x = 0 -> deg x = -oo;
  deg_lt : forall a b, b <> 0 -> deg a <= deg (a * b);
  degP : forall a b, b <> 0 -> div_res deg a b
}.

Section Fields.

Variable F : field.

Lemma inv0 : 0^-1 = 0 :> F.
Proof. exact: Field.inv0. Qed.

Lemma invL : forall x : F, x <> 0 -> x^-1 * x = 1.
Proof. exact: Field.unitPL. Qed.

Lemma mulKr : forall x : F, x <> 0 -> cancel (mulr x) (mulr x^-1).
Proof. by move=> x Hx y; rewrite mulA (invL Hx) mul1r. Qed.

Lemma invR : forall x : F, x <> 0 -> x * x^-1 = 1.
Proof. move=> x; rewrite mulC; exact: invL. Qed.

Lemma mulrK : forall x : F, x <> 0 -> cancel (mulrr x) (mulrr x^-1).
Proof. by move=> x Hx y; rewrite -mulA (invR Hx) mulr1. Qed.

Lemma mulKrV : forall x : F, x <> 0 -> cancel (mulr x^-1) (mulr x).
Proof. by move=> x Hx y; rewrite mulA (invR Hx) mul1r. Qed.

Lemma mulrKV : forall x : F, x <> 0 -> cancel (mulrr x^-1) (mulrr x).
Proof. by move=> x Hx y; rewrite -mulA (invL Hx) mulr1. Qed.

Lemma inv_injR : forall x y : F, x <> 0 -> x * y = 1 -> y = x^-1.
Proof.
 (* {{{ *)
move=> x y Hx.
move/(congr1 (fun k => x^-1 * k)).
by rewrite mulA invL // mul1r mulr1.
 (* }}} *)
Qed.

Lemma inv_injL : forall x y : F, x <> 0 -> y * x = 1 -> y = x^-1.
Proof.  move=> x y; rewrite mulC; exact: inv_injR. Qed.

Lemma nzP : 1 <> 0 :> F.
Proof. exact: Field.nzP. Qed.

Lemma opp1nz : -(1) != 0 :> F.
Proof. 
 (* {{{ *)
apply/eqP.
move/(congr1 (fun x => x * -(1))).
rewrite mul_opp1_opp1 mul0r.
exact: nzP.
 (* }}} *)
Qed.

Lemma inv1 : 1^-1 = 1 :> F.
Proof. symmetry; apply: inv_injL; first exact: nzP; by rewrite mulr1. Qed.

Lemma opp_inv : forall x : F, x <> 0 -> (- x)^-1 = -(x ^-1).
Proof.
 (* {{{ *)
move=> x Hx.
symmetry.
apply: inv_injR.
  move=> H.
  by rewrite -(opp_opp x) H opp0 in Hx.
by rewrite mul_opp_opp invR.
 (* }}} *)
Qed.

Lemma add_inv0 : forall x y : F, x <> 0 -> y <> 0 -> x + y = 0 -> x ^-1 + y ^-1 = 0.
Proof.
 (* {{{ *)
move=> x y Hx Hy Hxy.
move/(congr1 (fun k => - x + k)): Hxy.
rewrite addA oppL addr0 add0r => ->.
rewrite opp_inv => //.
by rewrite oppR.
 (* }}} *)
Qed.

End Fields.


(** Subrings *)
Section Sub_ring.

Variable R : ring.

Structure subring : Type := Subring {
  srbase :> set R;
  zeroP : srbase 0;
  oneP : srbase 1;
  addP : forall x y : R, srbase x -> srbase y -> srbase (x + y);
  mulP : forall x y : R, srbase x -> srbase y -> srbase (x * y);
  oppP : forall x : R, srbase x -> srbase (- x)
}.

Lemma Subring_ext : forall H K : subring, srbase H = srbase K -> H = K.
Proof.
 (* {{{ *)
move=> [H1 H2 H3 H4 H5 H6] [K1 K2 K3 K4 K5 K6].
rewrite /= => H.
rewrite H in H2 H3 H4 H5 H6 *.
congr Subring;  by apply: proof_irrelevance.
 (* }}} *)
Qed.

Definition ring_to_subring : subring.
exists (fun (x:R) => true) => //. 
Defined.

Variable S : subring.

Notation Sty := (sub_eqType S).

Definition sadd : Sty -> Sty -> Sty.
 (* {{{ *)
move=> x y.
exists (val x + val y).
abstract(apply: addP; exact: valP).
 (* }}} *)
Defined.

Definition smul : Sty -> Sty -> Sty.
 (* {{{ *)
move=> x y.
exists (val x * val y).
abstract(apply: mulP; exact: valP).
 (* }}} *)
Defined.

Definition sopp : Sty -> Sty.
 (* {{{ *)
move=> x.
exists (- val x).
abstract(apply: oppP; exact: valP).
 (* }}} *)
Defined.

Definition szero := EqSig _ 0 (@zeroP S).

Definition sone := EqSig _ 1 (@oneP S).

Lemma subring_axioms : ring_axioms sadd smul sopp szero sone.
Proof.
 (* {{{ *)
split; move=> H *; apply: val_inj => /=;
[exact: addC |
 exact: addA |
 exact: addr0 |
 exact: oppL |
 exact: mulA |
 exact: distPM |
 exact: distMP |
 exact: mul1r |
 exact: mulr1 |
 exact: mulC].
 (* }}} *)
Qed.

Definition subring_to_ring := Ring.Ring subring_axioms.

Lemma subring_addl : forall x y, S x -> S (x + y) -> S y.
Proof.
 (* {{{ *)
move=> x y Hx Hxy.
move: (oppP Hx) => Hx'.
move: (addP Hx' Hxy).
by rewrite addA oppL add0r.
 (* }}} *)
Qed.

Lemma subring_addr : forall x y, S y -> S (x + y) -> S x.
Proof. by move=> x y Hy; rewrite addC; apply: subring_addl. Qed.

Lemma subr_m1 : S (- (1:R)).
Proof. apply: oppP. exact: oneP. Qed.

End Sub_ring.

Coercion ring_to_subring : ring >-> subring.

(** Subdomain *)
Section SubDomain.

Variable R : domain.
Variable S : subring R.

Definition subring_to_domain : domain.
 (* {{{ *)

exists (subring_to_ring S).
abstract(
  move=> x1 x2 [H];
  (case: {H}(integ H) => H; first by (left; apply: val_inj));
  by right;apply: val_inj).

 (* }}} *)
Defined.

End SubDomain.

(** Subfields *)

Section Sub_field.

Variable F : field.

Structure subfield : Type := Subfield {
  sfbase :> subring F;
  invP : forall x : F, sfbase x -> sfbase (invf x)
}.

Lemma Subfield_ext : forall H K : subfield, srbase H = srbase K -> H = K.
Proof.
 (* {{{ *)
move=> [[H1 H2 H3 H4 H5] H6 H7] [[K1 K2 K3 K4 K5] K6 K7] /= H.
rewrite {H1} H in H2 H3 H4 H5 H6 H7 *.
have -> : H2 = K2 by apply: proof_irrelevance.
have -> : H3 = K3 by apply: proof_irrelevance.
have -> : H4 = K4 by apply: proof_irrelevance.
have -> : H5 = K5 by apply: proof_irrelevance.
have -> : H6 = K6 by apply: proof_irrelevance.
congr Subfield.
by apply: proof_irrelevance.
 (* }}} *)
Qed.

Definition field_to_subfield : subfield.
exists (ring_to_subring F) => //.
Defined.

Variable S : subfield.

Notation Fty := (sub_eqType S).

Definition sinv : Fty -> Fty.
 (* {{{ *)
move=> x.
exists ((val x)^-1).
abstract(apply: invP; exact: valP).
 (* }}} *)
Defined.

Definition subfield_to_field : field.
 (* {{{ *)
exists (subring_to_domain S) sinv.
  abstract(
  move=> [x Hx] H;
  apply: val_inj => /=;
  apply: invL => H0;
  rewrite H0 in Hx H;
  (suffices: (EqSig S 0 Hx = (@szero _ _)) by done);
  by apply: val_inj).
abstract(move=> [H]; by move/nzP: H).
abstract(
rewrite /sinv;
apply: val_inj => /=;
exact: inv0).
 (* }}} *)
Defined.

End Sub_field.

Coercion field_to_subfield : field >-> subfield.

(** Ideals *)

Section Ideal.

Variable U : ring.
Variable R : subring U.

Structure ideal : Type := Ideal {
  idbase :> set U;
  id_ss : sub_set idbase R;
  id0 : idbase 0;
  id_add : forall x y : U, idbase x -> idbase y -> idbase (x + y);
  idPL : forall x y : U, idbase x -> R y -> idbase (x * y);
  idPR : forall x y : U, R x -> idbase y -> idbase (x * y)
}.

Lemma id_opp : forall (I:ideal) x, I x -> I (- x).
Proof.  by move=> I x Hx; rewrite -mul_opp1r idPR // subr_m1. Qed.

Definition ring_to_ideal : ideal.
 (* {{{ *)
exists R => //.
- exact: zeroP.
- exact: addP.
- exact: mulP.
- exact: mulP.
 (* }}} *)
Defined.

End Ideal.

Coercion ring_to_ideal : subring >-> ideal.

Section Ideal0.

Variable U : ring.
Variable R : subring U.

Lemma ideq : forall (I J : ideal R), (forall x, I x = J x) -> I = J.
Proof.
 (* {{{ *)

move=> [I a1 a2 a3 a4 a5] [J b1 b2 b3 b4 b5] /= H.
rewrite (weak_ext H) in a1 a2 a3 a4 a5 *.
congr Ideal; by apply: proof_irrelevance.

 (* }}} *)
Qed.

Lemma idbase_inj : forall I J : ideal R, (idbase I = idbase J) -> I = J.
Proof.
 (* {{{ *)

move=> I J H.
apply: ideq.
by rewrite H.

 (* }}} *)
Qed.

Definition zero_ideal : ideal R.
 (* {{{ *)
exists (fun x => x == 0 :> U).
- abstract(
  move=> x;
  move/eqP => ->;
  exact: zeroP).
- abstract(exact: eq_refl).
- abstract(by move=> x y;do 2 move/eqP => ->; rewrite addr0).
- abstract(by move=> x y; move/eqP => ->; rewrite mul0r).
abstract(
move=> x y Hx;
move/eqP => ->; 
by rewrite mulr0).
 (* }}} *)
Defined.

Definition maximal_ideal (I : ideal R) := 
  I <> R /\  
  forall J : ideal R, sub_set I J -> J = I \/ J = R.

Inductive not_maximal_ideal (I : ideal R) : Prop :=  
  | Not_maximal0 : I = R -> not_maximal_ideal I
  | Not_maximal1 (J : ideal R) : 
    sub_set I J -> J <> I -> J <> R -> not_maximal_ideal I.

Lemma not_maximalP : forall I, ~ (maximal_ideal I) -> not_maximal_ideal I.
Proof.
 (* {{{ *)
move=> I.
move/not_and_or => [|].
  left; by apply: NNPP.
move/(not_all_ex_not _ (fun x => _)) => [K HK].
move: (imply_to_and _ _ HK) => [H1 H2].
move/not_or_and: H2 => [H2 H3].
by apply: (@Not_maximal1 I K).
 (* }}} *)
Qed.

End Ideal0.

Notation "0" := (zero_ideal _) : ideal_scope.
Delimit Scope ideal_scope with Id.

Section Ideal1.

Open Scope ring_scope.
Open Scope ideal_scope.

Variable U : ring.
Variable R : subring U.

Hint Resolve id0 id_add idPL idPR mulP oneP zeroP addP.

Definition ideal_of_elem (a : U) : ideal R.
 (* {{{ *)
move/(insub R)=> [[a Ha]|]; last exact: 0.
exists (fun x => Pb (exists x', R x' /\ x = x' * a )).
- abstract(
  move=> x /=;
  move/PbP => [y [Hy ->]];
  auto).
- abstract(by apply/PbP; exists (0:U)%R; rewrite mul0r; auto).
- abstract(move=> x y;move/PbP => [x' [Hx' ->]]; move/PbP => [y' [Hy' ->]];
  rewrite -distPM; apply/PbP; exists (x' + y'); auto).
- abstract(move=> x y; move/PbP => [x' [Hx' ->]] Hy; apply/PbP; exists (x' * y);
  rewrite -mulA [a * _]mulC mulA; auto).
abstract(move=> x y Hx; move/PbP => [x' [Hx' ->]]; apply/PbP; exists (x * x');
rewrite mulA; auto).
  (* }}} *)
Defined.

Definition srunit u := exists u', R u' /\ u * u' = 1. 

Lemma ideal_unit : forall a, R a -> srunit a -> ideal_of_elem a = R.
Proof.
 (* {{{ *)
move=> a Ha [u' [Hu Hu']].
apply: ideq => x /=.
rewrite /ideal_of_elem /=.
case: insubP => [[_ _] /= _ ->|]; last by rewrite Ha.
apply/idP/idP.
  by move/PbP => [y [Hy ->]]; auto.
move=> H.
apply/PbP.
exists (u' * x).
split; auto.
rewrite -mulA mulrCA.
rewrite mulC in Hu'.
by rewrite Hu' mulr1.
 (* }}} *)
Qed.

Lemma unit_ideal : forall u, R u -> ideal_of_elem u = R -> srunit u.
Proof.
 (* {{{ *)
move=> u Hu.
move/(congr1 (fun x => idbase x (1:U))).
rewrite /ideal_of_elem /ring_to_ideal /=.
case: insubP => [[_ _] /= _ ->|].
  move/PbP.
  rewrite oneP => [[x' [Hx' Hx0]]].
  exists x'.
  by rewrite mulC; split.
by move/negP.
 (* }}} *)
Qed.

End Ideal1.

Prenex Implicits ideal_of_elem.

(** Homomorphisms *)

Section Homo.

Variable R S : ring.
Variable R' : subring R.
Variable S' : subring S.

Structure homo (h : R -> S) : Prop := Homo {
  homoP : forall x, R' x -> S' (h x);
  homoAddP : forall x y, R' x -> R' y -> h (x + y) = h x + h y;
  homoMulP : forall x y, R' x -> R' y -> h (x * y) = h x * h y;
  homoJunk : forall x, ~ (R' x) -> h x = 0
}.

Structure iso (h : R -> S) : Prop := Iso {
  isobase :> homo h;
  imonoP : forall x y, R' x -> R' y -> h x = h y -> x = y;
  iontoP : surj R' S' h
}.

Definition isomorphic := exists h, iso h.

End Homo.
  
Definition endo R R' := @homo R R R' R'.
Definition auto R R' := @iso R R R' R'.

Prenex Implicits auto.

Section Homo0.

Variable R S : ring.
Variable R' : subring R.
Variable S' : subring S.
Variable s : R -> S.

Lemma homo0 : homo R' S' s -> s 0 = 0.
Proof.
 (* {{{ *)

move=> Hs.
apply: (@addr_injl _ (s 0)).
rewrite addr0 -(homoAddP Hs); try exact: zeroP.
by rewrite addr0.

 (* }}} *)
Qed.

Lemma homoOpp : homo R' S' s -> forall x, R' x -> s (- x) = - (s x).
Proof.
 (* {{{ *)
move=> Hs x Hx.
apply: (@addr_injl _ (s x)).
rewrite oppR -(homoAddP Hs) //.
  by rewrite oppR homo0.
exact: oppP.
 (* }}} *)
Qed.

Definition kernel := fun x => R' x && (s x == 0).

Definition ker_ideal : homo R' S' s -> ideal R'.
 (* {{{ *)

move=> Hs.
exists kernel.
- abstract(by move=> x; move/andP; firstorder).
- by rewrite /kernel homo0 // eq_refl andbT zeroP.
- abstract(
  move: (Hs) => [H1 H2 H3 H4];
  move=> x y;
  move/andP => [H5 H6];
  move/eqP: H6 => H6;
  move/andP => [H7 H8];
  move/eqP: H8 => H8;
  by rewrite /kernel H2 //= H6 H8 addr0 addP /=).
- abstract(
  move: (Hs) => [H1 H2 H3 H4];
  move=> x y;
  move/andP => [H5 H6];
  move/eqP: H6 => H6;
  move=> H7;
  by rewrite /kernel H3 //= H6 mulP //= mul0r).
- move: (Hs) => [H1 H2 H3 H4].
  move=> x y Hx. 
  move/andP => [H5 H6].
  move/eqP: H6 => H6.
  rewrite /kernel.
  by rewrite mulP //= H3 //= H6 mulr0.

 (* }}} *)
Defined.

End Homo0.

Prenex Implicits kernel.

(** Isomorphisms *)

Section Iso.

Variable R S : ring.
Variable R' : subring R.
Variable S' : subring S.
Variable i : R -> S.
Hypothesis Hi : iso R' S' i.

(* -------------------------------  inverse  -------------------------------- *)

Structure iso_inv_spec (i' : S -> R) : Prop := IIS {
  ii_closed : forall x, S' x -> R' (i' x);
  ii_inv1 : forall x, R' x -> i' (i x) = x;
  ii_inv2 : forall y, S' y -> i (i' y) = y;
  ii_junk : forall y, ~ (S' y) -> i' y = 0
}.

Definition iso_inv y := if S' y then epsilon (inhabits 0) (fun x : R => R' x /\ i x = y) else 0.

Lemma iso_invP : iso_inv_spec iso_inv.
Proof.
 (* {{{ *)
split.
- move=> x Hx; rewrite /iso_inv.
  case H : (S' x).
    move: (@epsilon_spec _ (inhabits 0) (fun y => R' y /\ i y = x)).
    apply: antsE. 
      move: (iontoP Hi Hx) => [y [Hy Hy']].
      by exists y; split.
    by move => [H1 H2].
  exact: zeroP.
- move=> x Hx; rewrite /iso_inv.
  have ->: (S' (i x)) by apply: (homoP Hi) ;eauto.
  move: (@epsilon_spec _ (inhabits 0) (fun y => R' y /\ i y = i x)).
  apply: antsE; first by exists x;split.
  move => [H1 H2].
  by move: (imonoP Hi H1 Hx H2) => ->.
- move=> y Hy; rewrite /iso_inv Hy.
  move: (@epsilon_spec _ (inhabits 0) (fun x => R' x /\ i x = y)).
  apply: antsE. 
    move: (iontoP Hi Hy) => [y1 [Hy1 Hy1']].
    by exists y1; split.
  by move => [H1 H2].
by rewrite /iso_inv; move=> y Hy; move/eqP: Hy; rewrite neq_true; move/eqP => ->.
 (* }}} *)
Qed.

Hint Resolve oneP addP mulP oppP homoP homoAddP homoMulP ii_closed.

Lemma iso_inv_homo : homo S' R' iso_inv.
Proof.
 (* {{{ *)
move: iso_invP => [H1 H2 H3 H4].
split; auto.
- move=> x y Hx Hy.
  apply: (imonoP Hi); auto.
  rewrite H3;auto.
  rewrite (homoAddP Hi);auto.
  by rewrite !H3; auto.
- move=> x y Hx Hy.
  apply: (imonoP Hi); auto.
  rewrite H3;auto.
  rewrite (homoMulP Hi);auto.
  by rewrite !H3; auto.
 (* }}} *)
Qed.

Lemma iso_inv_iso : iso S' R' iso_inv.
Proof.
 (* {{{ *)
move: iso_invP => [H1 H2 H3 H4].
split; first by exact: iso_inv_homo.
  move=> x y Hx Hy.
  move/(congr1 i).
  by rewrite !H3;auto.
move=> y Hy.
exists (i y).
split.
  by apply: (homoP Hi).
by symmetry; auto.
 (* }}} *)
Qed.

Lemma iso1 : i 1 = 1.
Proof.
 (* {{{ *)
rewrite -(mul1r (i 1)).
rewrite -{1}(@ii_inv2 _ iso_invP 1);auto.
rewrite -(homoMulP Hi); auto.
  by rewrite mulr1 (ii_inv2 iso_invP); auto.
by apply: (ii_closed iso_invP); auto.
 (* }}} *)
Qed.

End Iso.

Section Iso0.

Variable F K : field.
Variable F' : subfield F.
Variable K' : subfield K.
Variable i : F -> K.
Hypothesis Hi : iso F' K' i.

Lemma inv_iso : forall x, F' x -> x <> 0 -> i (x^-1) = (i x)^-1.
Proof.
 (* {{{ *)
move=> x Hx H0.
have H0' : i x <> 0.
  move/(congr1 (iso_inv F' K' i)).
  rewrite (ii_inv1 (iso_invP Hi)); auto.
  by rewrite (homo0 (iso_inv_homo Hi)).
apply: (@mulr_injl _ (i x)) => //.
rewrite invR; auto.
rewrite -(homoMulP Hi); auto.
  rewrite invR;auto.
  exact: (iso1 Hi).
by apply: invP.
 (* }}} *)
Qed.

End Iso0.

Section Iso1.

Variable R S : ring.
Variable R' : subring R.
Variable S' : subring S.
Variable phi : R -> S.
Hypothesis phiP : homo R' S' phi.
Hypothesis ontoP : surj R' S' phi.
Hypothesis phiP' : kernel R' phi = set1 0.

Hint Resolve oppP addP.

Lemma homo_iso : iso R' S' phi.
Proof.
 (* {{{ *)

split => //.
move=> x y Hx Hy.
move/(congr1 (addrr (- phi y))).
rewrite oppR -(homoOpp phiP Hy) -(homoAddP phiP); auto.
move=> H.
move/(congr1 (fun f => f (x - y))): phiP'.
rewrite /kernel.
move/andP.
case H' : (_ == _).
  move=> _.
  move/eqP: H'.
  move/(congr1 (addrr y)).
  rewrite -addA oppL addr0 add0r.
  by move=> ->.
rewrite H.
move/not_and_or => [|].
  case; auto.
by rewrite eq_refl; move/negP.

 (* }}} *)
Qed.

End Iso1.






