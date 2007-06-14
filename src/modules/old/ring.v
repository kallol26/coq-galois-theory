
Require Import ssr.
Require Import ring_sig.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

Module Ring : RING.

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

Variable r : ring.
Notation "x1 + x2" := (@add r x1 x2).
Notation "x1 * x2" := (@mul r x1 x2).
Notation "- x" := (@opp r x). 
Notation "0" := (@zero r).
Notation "1" := (@one r).
Notation "x - y" := (x + opp y).
Notation addr := (fun x y => x + y).
Notation addrr := (fun x y => y + x).

Lemma add0r : forall x, 0 + x = x.
Proof. by move=> x; rewrite addC; exact: addr0. Qed.

Lemma oppR : forall x:r, x + -x = 0.
Proof. by move=> x; rewrite addC; exact: oppL. Qed.

Lemma addr_injl : forall x:r, injective (addr x).
Proof. by move=> x y z; move/(congr1 (addr (-x))); rewrite !addA !oppL !add0r. Qed.

Lemma addr_injr : forall x:r, injective (addrr x).
Proof. by move=> x y z /=; rewrite addC [z + _]addC; exact: addr_injl. Qed.

Lemma addKr : forall x:r, cancel (addr x) (addr (- x)).
Proof. by move=> x y; rewrite addA oppL add0r. Qed.

Lemma addKrV : forall x:r, cancel (addr (- x)) (addr x).
Proof. by move=> x y; rewrite addA oppR add0r. Qed.

Lemma addrK : forall x:r, cancel (addrr x) (addrr (- x)).
Proof. by move=> x y; rewrite -addA oppR addr0. Qed.

Lemma addrKV : forall x:r, cancel (addrr (- x)) (addrr x).
Proof. by move=> x y; rewrite -addA oppL addr0. Qed.

Lemma opp_opp : forall x:r, -(-x) = x.
Proof. by move=> x; apply: (@addr_injr (- x)); rewrite oppL oppR. Qed.

Lemma opp_uniq : forall x y y':r, x + y = 0 -> x + y' = 0 -> y = y'.
Proof. by move=> x y y' H H'; apply (@addr_injl x); rewrite H H'. Qed.

Lemma opp_def : forall x y:r, x + y = 0 -> y = - x.
Proof. move=> x y H; apply (@opp_uniq x);auto; by rewrite oppR. Qed.

Lemma mul0r : forall x:r, 0 * x = 0.
Proof. by move=> x; apply (@addr_injr (0 * x)); rewrite -distPM !add0r. Qed.

Lemma mulr0 : forall x:r, x * 0 = 0.
Proof. by move=> x; apply (@addr_injr (x * 0)); rewrite -distMP !add0r. Qed.

Lemma mul_oppL : forall x y:r, - x * y = - (x * y).
Proof. by move=> x y; apply (@opp_uniq (x * y));rewrite -?distPM oppR ?mul0r. Qed. 
  
Lemma mul_oppR : forall x y:r, x * - y = - (x * y).
Proof. by move=> x y; apply (@opp_uniq (x * y)); rewrite -?distMP oppR ?mulr0. Qed.

Lemma mul_opp_opp : forall x y:r, - x * - y = x * y.
Proof. by move=> x y; rewrite mul_oppR mul_oppL opp_opp. Qed.

Lemma opp_sym : forall x y:r, - x = y -> x = - y.
Proof. by move=> x y H; rewrite -H; symmetry; exact: opp_opp. Qed.

Lemma addrCA : forall m n p:r, m + (n + p) = n + (m + p).
Proof. by move=> m n p; rewrite addA [m + _]addC addA. Qed.

Lemma opp0 : - 0 = 0 :> r.
Proof. by apply (@addr_injr 0); rewrite oppL !addr0. Qed.

Lemma oppr0 : forall x:r, (-x == 0) = (x == 0).
Proof. 
 (* {{{ *)
move=> x. 
apply/eqP.
case H : (_ == _) => [|H']; first by rewrite (eqP H) opp0.
move: (congr1 (@opp _) H).
rewrite opp_opp opp0 => H0.
by rewrite H0 eq_refl in H'.
 (* }}} *)
Qed.

Lemma mulr1 : forall x:r, x * 1 = x.
Proof. by move=> x; rewrite mulC; exact: mul1r. Qed.

Lemma mul_opp1r : forall x:r, -(1) * x = - x.
Proof. by move=> x; apply (@addr_injl x); rewrite oppR mul_oppL mul1r oppR. Qed.

Lemma mul_opp1_opp : forall x:r, -(1) * - x = x.
Proof. by move=> x; rewrite mul_opp1r opp_opp. Qed.

Lemma mul_opp1_opp1 : -(1) * -(1) = 1 :> r.
Proof.  exact: mul_opp1_opp. Qed.

Lemma opp_add : forall x y:r, -(x + y) = - x - y.
Proof. by move=> x y; rewrite -mul_opp1r distMP !mul_opp1r. Qed.

Lemma zero_ring : 1 = 0 :> r -> forall x:r, x = 0.
Proof. by move=> H x; rewrite -[x]mul1r H mul0r. Qed.

Lemma subr0 : forall x:r, x - 0 = x.
Proof. by rewrite opp0; exact: addr0. Qed.

Lemma sub0r : forall x:r, 0 - x = - x.
Proof. by move=> x; rewrite add0r. Qed.

Lemma mulrCA : forall m n p:r, m * (n * p) = n * (m * p).
Proof. by move=> m n p; rewrite mulA [m * _]mulC mulA. Qed.

End Ring.