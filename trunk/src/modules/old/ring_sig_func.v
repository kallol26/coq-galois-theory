
Require Import ssr.
Require Import lib.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

Module Type RING.

  Parameter base : eqType.

  Parameter addr : base -> base -> base.
  Parameter mulr : base -> base -> base.
  Parameter oppr : base -> base.
  Parameter zeror : base.
  Parameter oner : base.

  Notation "x1 + x2" := (addr x1 x2).
  Notation "x1 * x2" := (mulr x1 x2).
  Notation "x - y" := (x + oppr y).
  Notation "- x" := (oppr x).
  Notation "0" := zeror.
  Notation "1" := oner.
  Notation addrr := (fun x y => y + x).
  Notation mulrr := (fun x y => y * x).

  Axiom addC : forall x y, x + y = y + x.
  Axiom addA : forall x y z, x + (y + z) = (x + y) + z.
  Axiom addr0 : forall x, x + 0 = x.
  Axiom oppL : forall x, -x + x = 0.
  Axiom mulC : forall x y, x * y = y * x.
  Axiom mulA : forall x y z, x * (y * z) = x * y * z.
  Axiom mul1r : forall x, 1 * x = x.
  Axiom distPM : forall x1 x2 x3, (x1 + x2) * x3 = (x1 * x3) + (x2 * x3).
  Axiom distMP : forall x1 x2 x3, x1 * (x2 + x3) = (x1 * x2) + (x1 * x3).

End RING.

Module Type RING_LEMMAS.
  
  Declare Module R : RING. 

  Notation addr := R.addr.
  Notation mulr := R.mulr.
  Notation "x1 + x2" := (addr x1 x2).
  Notation "x1 * x2" := (mulr x1 x2).
  Notation "x - y" := (x + R.oppr y).
  Notation "- x" := (R.oppr x).
  Notation "0" := R.zeror.
  Notation "1" := R.oner.
  Notation addrr := (fun x y => y + x).
  Notation mulrr := (fun x y => y * x).

  Axiom mulr1 : forall x, x * 1 = x.
  Axiom add0r : forall x, 0 + x = x.
  Axiom mul0r : forall x, 0 * x = 0.
  Axiom mulr0 : forall x, x * 0 = 0.
  Axiom oppR : forall x, x + -x = 0.
  Axiom addr_injl : forall x, injective (addr x).
  Axiom addr_injr : forall x, injective (addrr x).
  Axiom addKr : forall x, cancel (addr x) (addr (- x)).
  Axiom addKrV : forall x, cancel (addr (- x)) (addr x).
  Axiom addrK : forall x : R.base, cancel (addrr x) (addrr (- x)).
  Axiom addrKV : forall x, cancel (addrr (- x)) (addrr x).
  Axiom opp_opp : forall x, -(-x) = x.
  Axiom opp_uniq : forall x y y', x + y = 0 -> x + y' = 0 -> y = y'.
  Axiom opp_def : forall x y, x + y = 0 -> y = - x.
  Axiom mul_oppL : forall x y, - x * y = - (x * y).
  Axiom mul_oppR : forall x y, x * - y = - (x * y).
  Axiom mul_opp_opp : forall x y, - x * - y = x * y.
  Axiom opp_sym : forall x y, - x = y -> x = - y.
  Axiom addrCA : forall m n p, m + (n + p) = n + (m + p).
  Axiom opp0 : - 0 = 0.
  Axiom oppr0 : forall x, (-x == 0) = (x == 0).
  Axiom mul_opp1r : forall x, -(1) * x = - x.
  Axiom mul_opp1_opp : forall x, -(1) * - x = x.
  Axiom mul_opp1_opp1 : -(1) * -(1) = 1.
  Axiom zero_ring : 1 = 0 -> forall x, x = 0.
  Axiom mulrCA : forall m n p, m * (n * p) = n * (m * p).
  Axiom subr0 : forall x, x - 0 = x.
  Axiom opp_add : forall x y, -(x + y) = - x - y.
  Axiom sub0r : forall x, 0 - x = - x.

End RING_LEMMAS.

Module RingLemmas(R : RING) : RING_LEMMAS with Module R := R.

Module R := R.

Notation addr := R.addr.
Notation mulr := R.mulr.
Notation oppr := R.oppr.
Notation addrr := R.addrr.
Notation mulrr := R.mulrr.
Notation addC := R.addC.
Notation addA := R.addA.
Notation addr0 := R.addr0.
Notation oppL := R.oppL.
Notation mulC := R.mulC.
Notation mulA := R.mulA.
Notation mul1r := R.mul1r.
Notation distPM := R.distPM.
Notation distMP := R.distMP.
Notation "x1 + x2" := (R.addr x1 x2).
Notation "x1 * x2" := (R.mulr x1 x2).
Notation "- x" := (R.oppr x).
Notation "0" := R.zeror.
Notation "1" := R.oner.
Notation "x - y" := (x + R.oppr y).

Lemma mulr1 : forall x, x * 1 = x.
Proof. by move=> x; rewrite mulC; exact: mul1r. Qed.

Lemma add0r : forall x, 0 + x = x.
Proof. by move=> x; rewrite addC; exact: addr0. Qed.

Lemma oppR : forall x, x + -x = 0.
Proof. move=> x. rewrite addC; exact: oppL. Qed.

Lemma addr_injl : forall x, injective (addr x).
Proof. by move=> x y z; move/(congr1 (addr (-x))); rewrite !addA !oppL !add0r. Qed.

Lemma addr_injr : forall x, injective (addrr x).
Proof. by move=> x y z /=; rewrite addC [z + _]addC; exact: addr_injl. Qed.

Lemma addKr : forall x, cancel (addr x) (addr (- x)).
Proof. by move=> x y; rewrite addA oppL add0r. Qed.

Lemma addKrV : forall x, cancel (addr (- x)) (addr x).
Proof. by move=> x y; rewrite addA oppR add0r. Qed.

Lemma addrK : forall x, cancel (addrr x) (addrr (- x)).
Proof. by move=> x y; rewrite -addA oppR addr0. Qed.

Lemma addrKV : forall x, cancel (addrr (- x)) (addrr x).
Proof. by move=> x y; rewrite -addA oppL addr0. Qed.

Lemma opp_opp : forall x, -(-x) = x.
Proof. by move=> x; apply: (@addr_injr (- x)); rewrite oppL oppR. Qed.

Lemma opp_uniq : forall x y y', x + y = 0 -> x + y' = 0 -> y = y'.
Proof. by move=> x y y' H H'; apply (@addr_injl x); rewrite H H'. Qed.

Lemma opp_def : forall x y, x + y = 0 -> y = - x.
Proof. move=> x y H; apply (@opp_uniq x);auto; by rewrite oppR. Qed.

(** # <a href=http://code.google.com/p/coq-galois-theory/wiki/TheoremTimeline> ROTMAN: Theorem 1(i) </a> # *)
Lemma mul0r : forall x, 0 * x = 0.
Proof. by move=> x; apply (@addr_injr (0 * x)); rewrite -distPM !add0r. Qed.

Lemma mulr0 : forall x, x * 0 = 0.
Proof. by move=> x; apply (@addr_injr (x * 0)); rewrite -distMP !add0r. Qed.

Lemma mul_oppL : forall x y, - x * y = - (x * y).
Proof. by move=> x y; apply (@opp_uniq (x * y));rewrite -?distPM oppR ?mul0r. Qed. 
  
Lemma mul_oppR : forall x y, x * - y = - (x * y).
Proof. by move=> x y; apply (@opp_uniq (x * y)); rewrite -?distMP oppR ?mulr0. Qed.

Lemma mul_opp_opp : forall x y, - x * - y = x * y.
Proof. by move=> x y; rewrite mul_oppR mul_oppL opp_opp. Qed.

Lemma opp_sym : forall x y, - x = y -> x = - y.
Proof. by move=> x y H; rewrite -H; symmetry; exact: opp_opp. Qed.

Lemma addrCA : forall m n p, m + (n + p) = n + (m + p).
Proof. by move=> m n p; rewrite addA [m + _]addC addA. Qed.

Lemma opp0 : - 0 = 0.
Proof. by apply (@addr_injr 0); rewrite oppL !addr0. Qed.

Lemma oppr0 : forall x, (-x == 0) = (x == 0).
Proof. 
 (* {{{ *)
move=> x. 
apply/eqP.
case H : (_ == _) => [|H']; first by rewrite (eqP H) opp0.
move: (congr1 oppr H).
rewrite opp_opp opp0 => H0.
by rewrite H0 eq_refl in H'.
 (* }}} *)
Qed.

(** # <a href=http://code.google.com/p/coq-galois-theory/wiki/TheoremTimeline> ROTMAN: Theorem 1(ii) </a> # *)
Lemma mul_opp1r : forall x, -(1) * x = - x.
Proof. by move=> x; apply (@addr_injl x); rewrite oppR mul_oppL mul1r oppR. Qed.

(** # <a href=http://code.google.com/p/coq-galois-theory/wiki/TheoremTimeline> ROTMAN: Theorem 1(iii) </a> # *)
Lemma mul_opp1_opp : forall x, -(1) * - x = x.
Proof. by move=> x; rewrite mul_opp1r opp_opp. Qed.

Lemma mul_opp1_opp1 : -(1) * -(1) = 1.
Proof.  exact: mul_opp1_opp. Qed.

Lemma opp_add : forall x y, -(x + y) = - x - y.
Proof. by move=> x y; rewrite -mul_opp1r distMP !mul_opp1r. Qed.

Lemma zero_ring : 1 = 0 -> forall x, x = 0.
Proof. by move=> H x; rewrite -[x]mul1r H mul0r. Qed.

Lemma subr0 : forall x, x - 0 = x.
Proof. by rewrite opp0; exact: addr0. Qed.

Lemma sub0r : forall x, 0 - x = - x.
Proof. by move=> x; rewrite add0r. Qed.

Lemma mulrCA : forall m n p, m * (n * p) = n * (m * p).
Proof. by move=> m n p; rewrite mulA [m * _]mulC mulA. Qed.

End RingLemmas. 
