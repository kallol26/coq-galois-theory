
Require Import ssr.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.


(* -------------------------------------------------------------------------- *)
(*  Natural numbers                                                           *)
(* -------------------------------------------------------------------------- *)

Section Nat.

Lemma ltnSS : forall n m, (S n < S m) = (n < m).
Proof. by elim => [|n IH] [|m]. Qed.

Lemma leqSS : forall n m, (S n <= S m)%N = (n <= m)%N.
Proof. by elim => [|n IH] [|m]. Qed.


(* ---------------------------------  Max  ---------------------------------- *)

Fixpoint max (m n : nat) {struct m} : nat :=
  match m, n with
  | O, _ => n
  | _, O => m
  | S m, S n => S (max m n)
  end.

Lemma maxE : forall n1 n2, max n1 n2 = if n1 <= n2 then n2 else n1.
Proof. elim=> [|n IH] [|m] //= ;by rewrite IH (fun_if S). Qed.

Lemma max_refl : forall n, max n n = n.
Proof. move=> n; by rewrite maxE leqnn. Qed.

Lemma max0n : forall n, max O n = n.
Proof. done. Qed.

Lemma maxn0 : forall n, max n O = n.
Proof. move=> [|n]; by rewrite maxE leqn0. Qed.

Lemma max_leL : forall n m : nat, n <= max n m.
Proof. 
 (* {{{ *)
move=> n m.
rewrite maxE.
by case H : (n <= m) => // .
 (* }}} *)
Qed.

Lemma max_sym : forall n m, max n m = max m n.
Proof. 
 (* {{{ *)
move=> n m.
rewrite !maxE.
case H : (n <= m) => // .
  case H' : (m <= n) => // .
  apply/eqP.
  by rewrite eqn_leq H H'.
move: H.
move/negbT.
rewrite -ltnNge.
move/ltnW => H.
by rewrite H.
 (* }}} *)
Qed.

Lemma max_leR : forall n m, m <= max n m.
Proof. move=> n m; rewrite max_sym; exact: max_leL. Qed.

(* --------------------------  Complete induction  -------------------------- *)

Lemma comp_ind_aux : 
  forall (P : nat -> Prop), P O -> 
   (forall n, (forall i, i < n -> P i) -> P n) -> 
     (forall n i, i < S n -> P i).
Proof.
 (* {{{ *)
move=> P P0 H1.
elim=> [|n IH] i H.
  rewrite ltnS leqn0 in H.
  by rewrite (eqP H).
rewrite ltnS leq_eqVlt in H.
move: H.
move/orP => [].
  move/eqP => -> .
  by apply: (H1 (S n) IH).
exact: IH.
 (* }}} *)
Qed.

Lemma comp_ind : 
  forall (P : nat -> Prop), P O -> 
   (forall n, (forall i, i < n -> P i) -> P n) -> forall n, P n.
Proof. move=> P H0 Hn n. exact: (comp_ind_aux H0 Hn (ltnSn n)). Qed.

Lemma muln_injL : forall p m n, p != 0 -> p * n == p * m -> n == m.
Proof.
 (* {{{ *)
by move=> p m n; move/negbET=> Hp; rewrite eqn_leq !leq_mul2l Hp /= -eqn_leq.
 (* }}} *)
Qed.

Lemma muln_injR : forall p m n, p != 0 -> n * p == m * p -> n == m.
Proof. 
 (* {{{ *)
move=> p n m Hp; move/eqP => Hq; apply: muln_injL; eauto. 
by rewrite mulnC Hq mulnC.
 (* }}} *)
Qed.

(* -------------------------------  Divides  -------------------------------- *)

Definition divides n m := exists n', n * n' = m.

(* ---------------------------------  min  ---------------------------------- *)

Fixpoint smallest_aux (P : nat -> bool) (m n : nat) {struct n} : nat := 
  match n with 
    | O => m
    | S n' => let m' := m - n in if P m' then m' else @smallest_aux P m n'
  end.

Definition smallest P n := smallest_aux P n n.

(* ---------------------------------  sum  ---------------------------------- *)

Definition natsum (l : seq nat_eqType) := foldr addn O l.

Lemma natsum_mult : forall (s : seq nat_eqType) n, all (set1 n) s -> natsum s = ((size s) * n)%N.
Proof.
 (* {{{ *)
elim=> [|x s IH] n //=.
move/andP => [H1 H2].
move/eqP: H1 => <-.
by rewrite (IH _ H2).
 (* }}} *)
Qed.

Lemma leq_sub : forall n m k, n <= m -> n - k <= m.
Proof.
 (* {{{ *)
move=> n m k Hnm.
apply: (@leq_trans n) => //.
exact: leq_subr.
 (* }}} *)
Qed.

Lemma ltn_sub : forall n m k, n < m -> n - k < m.
Proof.
 (* {{{ *)
move=> n m k Hnm.
apply: (@leq_trans (S n)) => //.
rewrite leqSS.
exact: leq_subr.
 (* }}} *)
Qed.

Lemma let_trans : forall n m p, n <= m -> m < p -> n < p.
Proof. by move=> n m p Hnm Hmp; rewrite -leqSS in Hnm; apply: (leq_trans Hnm). Qed.

Lemma lte_trans : forall n m p, n < m -> m <= p -> n < p.
Proof. by move=> n m p Hnm Hmp; apply: (leq_trans Hnm). Qed.

Lemma ltn_add_sub : forall n m, n <= m + (n - m).
Proof.
 (* {{{ *)
move=> n m.
case: (leqP n m) => H.
  move: (H).
  rewrite {1}/ssrnat.leq.
  move/eqP => ->.
  by rewrite addn0.
rewrite leq_add_sub => //.
exact: (ltnW H).
 (* }}} *)
Qed.

Lemma ltn_subR : forall k n m, n + m <= k -> n <= k - m.
Proof.
 (* {{{ *)

elim=> [|k IH] n m //=.
  rewrite leqn0 eqn_add0.
  move/andP => [H _].
  by move/eqP : H => ->.
rewrite leq_eqVlt.
move/orP => [|].
  move/eqP => <-.
  by rewrite addnC subn_addr.
rewrite leqSS.
move/IH => H.
apply: (leq_trans H).
rewrite -eqn_sub0 subn_sub eqn_sub0.
apply: (@leq_trans (S k)) => //.
exact: ltn_add_sub.

 (* }}} *)
Qed.

End Nat.

Notation "x |` y" := (divides x y) (at level 55) : dnat_scope.
