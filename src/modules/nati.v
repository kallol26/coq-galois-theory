
Require Import ssr.
Require Import constructive_lib.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

(* -------------------------------------------------------------------------- *)
(*  Natural numbers with oo                                                   *)
(* -------------------------------------------------------------------------- *)

(** *** Natural numbers with an added oo *)

Inductive nati : Type := Inf | Nat (x : nat).

Bind Scope nati_scope with nati.

Definition eqnati (x y : nati) := 
  match x,y with
    | Inf, Inf => true 
    | Nat x, Nat y => eqn x y
    | _,_ => false 
  end.

Lemma eqnatiPx : reflect_eq eqnati.
Proof.
 (* {{{ *)
move=> [|x] [|y] /= ; try by [constructor].
case H : (eqn x y).
  left.
  by rewrite (eqP H).    
right.
injection.
move=> H'; rewrite {H0 x}H' in H.
move: H.
suffices ->: (eqn y y = true); first by done.
move: y.
by elim=> [|n].
 (* }}} *)
Qed.

Canonical Structure eqnatiData := EqType eqnatiPx.

Definition plusi x y := 
  match x, y with 
    | Nat x', Nat y' => Nat (x' + y')
    | _, _ => Inf
  end.

Definition muli x y := 
  match x, y with 
    | Nat x', Nat y' => Nat (x' * y')
    | _, _ => Inf
  end.

Definition leq x y :=
  match x, y with
    | Inf, _ => true
    | _, Inf => false
    | Nat x', Nat y' => x' <= y'
  end.

Definition lt x y :=
  match x, y with
    | Inf, Inf => false
    | Inf, _ => true
    | _, Inf => false
    | Nat x', Nat y' => x' < y'
  end.

Definition mini x y := 
  match x,y with
    | Nat x', Nat y' => Nat (x' - y')
    | Inf,_ => Inf 
    | _,Inf => Nat 0
  end.

Definition S' n :=
  match n with
    | Inf => Inf
    | Nat n' => Nat (S n')
  end.

Delimit Scope nati_scope with I.
Open Scope nati_scope.
Notation "-oo" := Inf : nati_scope.
Notation "x <= y" := (leq x y) : nati_scope.
Notation "x < y" := (lt x y) : nati_scope.
Notation "x + y" := (plusi x y) : nati_scope.
Notation "x * y" := (muli x y) : nati_scope.
Notation "x - y" := (mini x y) : nati_scope.

Lemma ltmi : forall n, n < -oo = false. Proof. by case. Qed.

Lemma milt : forall n, -oo <= n = true. Proof. by case. Qed.

Lemma ltiS : forall n m, (S' n < S' m) = (n < m). 
Proof. by move=> [|n] [|m]. Qed.

Lemma leiS : forall n m, S' n <= S' m = (n <= m).
Proof. by move=> [|n] [|m]. Qed.

Lemma add_minf : forall n, (n + -oo)%I = -oo. Proof. by case. Qed.

Lemma add0i : forall n, (Nat O + n)%I = n.
Proof. by case. Qed.

Lemma addiSSn : forall n m, S'(n + m)%I = (S' n + m)%I.
Proof. by move=> [|n] [|m]. Qed.

Lemma ltIS : forall n, -oo < Nat n.
Proof. by case. Qed.

Lemma ltiSn : forall n, Nat n < S' (Nat n).
Proof. exact: leqnn. Qed.

Lemma leti_trans : forall m n o : nati, n <= m -> m < o -> n < o.
Proof.
 (* {{{ *)
move=> [|m] [|n] [|o] //= .
rewrite leq_eqVlt.
move/orP => [].
  by move/eqP => -> .
exact: ltn_trans.
 (* }}} *)
Qed.

Lemma lei_trans : forall m n o : nati, n <= m -> m <= o -> n <= o.
Proof. move=> [|m] [|n] [|o] //= . exact: leq_trans. Qed.

Lemma lei_refl : forall m, m <= m.
Proof. case=>[|m] // . exact: leqnn. Qed.

Inductive leq_xor_gti (m n : nati) : bool -> bool -> Set :=
  | LeqNotGti : m <= n -> leq_xor_gti m n true false
  | GtnNotLeq : n < m -> leq_xor_gti m n false true.

Lemma ltiNge : forall m n, (m < n) = negb (n <= m).
Proof. move=> [|m] [|n] // . exact: ltnNge. Qed.

Lemma leqiP : forall m n, leq_xor_gti m n (m <= n) (n < m).
Proof.
 (* {{{ *)
move=> m n; rewrite ltiNge; case Hmn: (m <= n); constructor; auto.
by rewrite ltiNge Hmn.
 (* }}} *)
Qed.

Definition maxi m n :=
  match m, n with
  | -oo, _ => n
  | _, -oo => m
  | Nat m', Nat n' => Nat (max m' n')
  end.

Lemma maxiI : forall n, maxi n -oo = n.
Proof. by case. Qed. 

Lemma maxi_leL : forall m n, n <= maxi n m.
Proof. case=> [|m] [|n] //= . exact: max_leL. Qed.

Lemma maxi_leR : forall m n, n <= maxi m n.
Proof. case=> [|m] [|n] //= . exact: max_leR. Qed.

Lemma leqNgt : forall m n, (n <= m) = negb (m < n).
Proof. move=> [|m] [|n] //=. exact: leqNgt. Qed.

Lemma ltnNge : forall m n, (m < n) = negb (n <= m).
Proof. move=> [|m] [|n] //=.  exact: ltnNge. Qed.

Lemma lti_addR : forall n m, n + m < m -> n = -oo.
Proof.
 (* {{{ *)

move=> [|n] [|m] //=.
move: (leq_addr n m).
rewrite addnC => H1 H2.
move: (leq_trans H2 H1).
by rewrite ltnn.

 (* }}} *)
Qed.

Lemma Nat_inj : forall x y, Nat x = Nat y -> x = y.
Proof. elim => [|x IH] [|y] //. by move=> [->]. Qed.

Lemma min_inf : forall m n, (n - m)%I = -oo -> n = -oo.
Proof. by move=> [|m] [|n]. Qed.

Lemma nati_ind' : forall (P : nati -> Prop),
   P -oo -> P (Nat 0) -> (forall (n : nati), P n -> P (S' n)) 
        -> (forall n, P n).
Proof.
 (* {{{ *)
move=> P PI P0 PS [|n] //.
elim: n => [|n] // Pn.
by move: (PS _ Pn) => /=.
 (* }}} *)
Qed.

Lemma lei0 : forall n, n <= Nat O -> n = Nat O \/ n = -oo.
Proof. 
 (* {{{ *)
move=> [|n]. 
  by right.
rewrite /= leqn0.
move/eqP.
by move=> -> ; left.
 (* }}} *)
Qed.

Lemma S'_inj : forall n m, S' n = S' m -> n = m.
Proof. move=> [|n] [|m] => //= [[H]]. by rewrite H. Qed.

Lemma lti0 : forall n, n < Nat O = (n == -oo).
Proof. by move=> [|n]. Qed.

Lemma ltinSn : forall n, n <> -oo -> n < S' n.
Proof. 
 (* {{{ *)

move=> [|n].
  move/eqP.
  by rewrite eq_refl.
move=> _ /=.
exact: ltnSn.

 (* }}} *)
Qed.

Lemma lenSn : forall n, n <= S' n.
Proof. by move=> [|n] //=. Qed.

Lemma s'inf : forall n, S' n = -oo -> n = -oo.
Proof. by move=> [|n]. Qed.

Lemma leq_eqVlti : forall m n, (m <= n) = (m == n) || (m < n).
Proof. move=> [|m] [|n] // . exact: leq_eqVlt. Qed.

Lemma addi0 : forall n, (n + Nat O)%I = n.
Proof.  move=> [|n] //=. by rewrite addn0. Qed.

Lemma nati_le_le : forall n m, n <= m -> m <= n -> n = m.
Proof.
 (* {{{ *)
move=> [|n] [|m] => // [[Hn]] [Hm].
congr Nat.
move: Hn.
rewrite leq_eqVlt.
move/orP => [|]; first by move/eqP.
rewrite ssrnat.ltnNge.
by move/negP.
 (* }}} *)
Qed.

Lemma nati_wo : forall (s : set eqnatiData) w,
  s w -> exists a, s a /\ forall x, s x -> a <= x.
Proof.
 (* {{{ *)
move=> s [|w] Hw;first by exists -oo; split.
case H : (s -oo); first by exists -oo; split.
move: (@nat_wo (fun n => s (Nat n)) _ Hw) => [a [Ha1 Ha2]].
exists (Nat a); split => // x Hx /=.
case: x Hx => //.
by rewrite H.
 (* }}} *)
Qed.
