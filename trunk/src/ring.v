(** 
  ** The ring ([ring]) structure and variants such as integral domains ([idom]) and fields ([field]).
*)

Require Import ssr.
Require Import nati_lib.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

(** Axioms *)

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

(** Structure *)
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

(** Identities and Lemmas *)

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

(** Division *)
Definition divides a b := exists a' : R, a * a' = b.

Notation "x |` y" := (divides x y) (at level 55).

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

(** Greatest Common Divisor (GCD) *)
CoInductive gcd (f g d : R) : Type :=
  Gcd : (d |` f) -> (d |` g) -> 
       (forall d', (d' |` f) -> (d' |` g) -> (d' |` d)) -> gcd f g d.

(** Units *)
Definition unit (x : R) := exists x', (x * x' = 1).

Lemma unit_nz : (1:R) <> 0 -> forall u, unit u -> u <> (0:R).
Proof. by move=> H u [u' Hu'] H'; rewrite H' mul0r in Hu'; move/esym: Hu'. Qed.

(** Associates *)
Definition associates x y := exists u : R, unit u /\ x = u * y.  

(** Irreducible elements *)
Definition irreducible (p : R) := forall x y, x * y = p -> (unit x \/ unit y).

(** Prime elements *)
Definition prime (p : R) := ~ (unit p) /\ irreducible p.

(** Relative primality *)
Definition rel_prime x y := forall d : R, gcd x y d -> unit d.

(** raise to a natural number power *)
Fixpoint pow (x : R) (n : nat) {struct n} : R := 
  if n is S n' then x * pow x n' else 1.

(** Multiply by a natural number *)
Fixpoint cmul (n : nat) (a : R) {struct n} : R := 
  if n is S n' then a + cmul n' a else 1.

(** Dot product *)
Fixpoint dot (s1 s2 : seq R) {struct s1} : R := 
  match s1,s2 with 
    | seq0, seq0 => 1%R
    | Adds h1 t1, Adds h2 t2 => h1 * h2 + dot t1 t2
    | _, _ => 0
  end.

Definition domain := forall x1 x2 : R, x1 * x2 = 0 -> x1 = 0 \/ x2 = 0.

(** # <a href=http://code.google.com/p/coq-galois-theory/wiki/TheoremTimeline> ROTMAN: Theorem 2</a> # *)
Lemma domain_cancel : (forall r a b : R, r != 0 -> r * a = r * b -> a = b) <-> domain.
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

End Rings.

(** *** Integral domains *)
Structure idom : Type := Idom {
  ibase :> ring;
  integ : domain ibase
}.



(** *** Fields *)

Module Field.

Structure field : Type := Field {
  fbase :> idom;
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

(** *** Euclidean rings *)

Inductive div_res (R : ring) (deg : R -> nati) (a b : R) : Prop :=
  Div_res q r : a = q * b + r -> deg r < deg b -> div_res deg a b.

Structure ering : Type := Ering {
  ebase :> idom;
  deg : ebase -> nati;
  deg0 : forall x, deg x = -oo -> x = 0;
  deg0' : forall x, x = 0 -> deg x = -oo;
  deg_lt : forall a b, b <> 0 -> deg a <= deg (a * b);
  degP : forall a b, b <> 0 -> div_res deg a b
}.

