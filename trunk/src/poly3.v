
Require Import ssr.
Require Import lib.
Require Import ring.
Require Import nzring.
Require Import poly.
Require Import poly2.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

Open Scope nati_scope.
Open Scope poly_scope.
Open Scope ring_scope.

(* ========================================================================== *)
(*  Division, Roots and Euclidean structure                                   *)
(* ========================================================================== *)

Section Div.

Variable F : nzfield.

Definition poly := (poly_idom F).

Notation X := (X F:poly_ring F).

(* -------------------------------  Division  ------------------------------- *)

Fixpoint div_alg_aux (n:nat) (f g : poly) {struct n} : poly * poly :=
  if n is S n' then
    if deg f < (deg g + Nat n')%I then div_alg_aux n' f g
    else 
      let s := const (lc f * (lc g)^-1) * powX _ n' in
      let (q,r) := div_alg_aux n' (f - s * g) g in
        (q + s,r)
  else (0,f).

Definition div_alg f g := 
  match (S' (deg f) - deg g)%I with 
    | -oo => (0,0)
    | Nat n => div_alg_aux n f g
  end.

Definition quo (f g : poly) := fst (div_alg f g).
Definition rem (f g : poly) := snd (div_alg f g).

(* ------------------  Lemma instances for weak rewriting  ------------------ *)

Lemma pone : (Nz (one_nz F):F) = 1. Proof. done. Qed.

Lemma addr0' : forall x: poly, x + 0 = x.
Proof. exact: addr0. Qed. 

Lemma lc_mul : forall p q : poly, lc (p * q) = lc p * lc q.
Proof. exact: lc_mul. Qed.

Lemma nz_lc : forall p : polynz F, lc (Nz p) = Nz (lc_nz p).
Proof. done. Qed.

Lemma deg_opp : forall p : poly, deg (- p) = deg p.
Proof. exact: deg_opp. Qed.

Lemma lc_opp : forall p : poly, lc (- p) = - lc p.
Proof. exact: lc_opp. Qed.

Lemma leqi_add_sub : forall n m : nati, n <> -oo -> n <= m -> (n + (m - n))%I = m.
Proof. by move=> [|n] [|m] //= _ H; rewrite leq_add_sub. Qed.

Lemma deg_mul : forall p q : poly, deg (p * q) = (deg p + deg q)%I.
Proof. exact: deg_mul. Qed.

Lemma mul0r' : forall x : poly, 0 * x = 0.
Proof. exact: mul0r. Qed.

Lemma mulC' : forall x y : poly, x * y = y * x. 
Proof. exact: mulC. Qed.

Lemma add_unevenL : forall p1 p2 : poly, deg p2 < deg p1 -> deg (p1 + p2) = deg p1.
Proof. exact: add_unevenL. Qed.

Lemma mulr0' : forall p : poly, p * 0 = 0. Proof. exact: mulr0. Qed.

Lemma poly_ind : forall (P : poly -> Prop),
   P 0 -> (forall (c : F) (p : poly), P p -> P (const c + (poly2.X F) * p))
        -> (forall (p : poly), P p).
Proof. exact: poly_ind. Qed.

Definition invL := @invL (field_of_nzfield F). 
Definition invR := @invR (field_of_nzfield F). 
Definition integ := @integ (field_of_nzfield F).

(* -----------------------------  Correctness  ------------------------------ *)

Inductive div_spec (f g : poly) : poly * poly -> Type :=
  | DivSpec (q r : poly) : f = q * g + r -> deg r < deg g -> div_spec f g (q,r). 

Lemma div_correct : 
  forall f g : poly, g <> 0 -> div_spec f g (div_alg f g).
Proof.
 (* {{{ *)
move=> f g.
case Dg : {1}g => [|g'] => [[//]|_].
rewrite /div_alg.
case Dn : (_ - _)%I => [|n].
  rewrite Dg in Dn *.
  by case: f Dn => [|f'].
have {Dn} : deg f < (deg g + Nat n)%I.
  case: (deg f) Dn => [|df] // <-.
  by rewrite Dg /= -leq_sub_add leqnn.
elim: n f => [|n IH] f.
  rewrite Dg /= addn0.
  by split.
move=> Hfg /=.
case Hn : (_ < _).
  auto.
case Df : {1}f Hn => [|f'] Hn; first by rewrite Dg in Hn.
have Hd : deg f = (deg g + Nat n)%I.
  move: Hn Hfg.
  rewrite Dg Df /= => Hn.
  rewrite addnS ltnS leq_eqVlt Hn orbF.
  by move/eqP => ->.
case: IH => [|q r Hqr Hr].
  rewrite -Hd addC.
  apply: lc_cancel.
  - by rewrite Df.
  - rewrite deg_opp !deg_mul deg_powX deg_const Dg Df /=.
    rewrite /mulr /=.
    case H : (nzring.mul_nz _ _) => [|k].
      contradiction (mul_nz_nz H).
    rewrite add0i.
    by rewrite Df Dg /= addnC in Hd.
  - rewrite lc_opp !lc_mul lc_const lc_powX mulr1 Dg nz_lc.
    by rewrite -mulA invL ?mulr1.
split => //.
by rewrite distPM -addA [_ + r]addC addA -[_ + r]Hqr -addA oppL addr0.
 (* }}} *)
Qed.

Lemma quoP : forall f g, f = quo f g * g + rem f g.
Proof.
 (* {{{ *)
move=> f [|g].
  by case: f.
rewrite /quo /rem.
by case: div_correct.
 (* }}} *)
Qed.

Lemma remP : forall f g, g <> 0 -> deg (rem f g) < deg g.
Proof.
 (* {{{ *)
move=> f g Hg.
rewrite /rem.
by case: div_correct.
 (* }}} *)
Qed.

(* -------------------------------  Divides  -------------------------------- *)

Lemma div_const : forall (c : F) f, c <> 0 -> const c |` f.
Proof.
 (* {{{ *)
move=> [|c] f; first by move/eqP; rewrite eq_refl.
move=> _; exists (const (Nz c : F)^-1 * f).
rewrite mulA const_mul invR //. 
rewrite /mulr /=.
case: f => [|f'] //.
by rewrite cmulnz1.
 (* }}} *)
Qed.

(* --------------------------------  Euclid  -------------------------------- *)

(* euclid_aux _ f g = (d,a,b) means d is the gcd of f,g, 
   and a * f + b * g = d *)
Fixpoint euclid_aux (n:nat) (f g : poly) {struct n} : poly * poly * poly:=
  if n is S n' then
    match div_alg f g with
      | (_,Zero) => (g,0,1)
      | (q,r) => let: (d,a,b) := euclid_aux n' g r in (d,b,a - b * q)
    end
  else (g,0,1).

Definition euclid f g := 
  match deg g with
    | -oo => (0,0,0)
    | Nat n => euclid_aux (S n) f g
  end.

Hint Resolve div_refl.

Inductive gcd (f g d : poly) : Type :=
  Gcd : (d |` f) -> (d |` g) -> 
       (forall d', (d' |` f) -> (d' |` g) -> (d' |` d)) -> gcd f g d.

Inductive euclid_spec (f g : poly) : poly * poly * poly -> Type :=
  | EuclidSpec (d a b : poly) : 
    gcd f g d -> a * f + b * g = d -> euclid_spec f g (d,a,b). 

Lemma euclid_correct : 
  forall f g : poly, g <> 0 -> euclid_spec f g (euclid f g).
Proof.
 (* {{{ *)
move=> f [|g] => [[] //|_]; rewrite /euclid /deg.
elim: {g}(S (deg_nz g)) f {-2 4}g (ltnSn (deg_nz g)) => [|n IH] f g //= Hn.
case: div_correct => // q [|r] Hqr Hqr'.
  split; try split; rewrite ?div_refl => //.
    by exists q; rewrite mulC' Hqr addr0'.
  by rewrite mul1r mul0r' add0r.
case: IH => [|d a b [Hdg Hdr Hrgd] Ed]; first exact: leq_trans Hqr' Hn.
have Ed': b * f + (a - b * q) * Nz g = d.
  by rewrite Hqr distMP distPM mulA addA addC !addA mul_oppL oppL add0r addC.
by move: div_add div_mulR; do 2!split => // *; [rewrite Hqr | rewrite -Ed']; auto.
 (* }}} *)
Defined.

(* ---------------------------------  root  --------------------------------- *)

Definition root (p : poly) x := p @ x == 0.

Lemma root_const : forall (c x : F), root (const c) x -> (c == 0).
Proof.  by case. Qed.

Lemma root_prod : forall (p q : poly) x, root (p * q) x -> root p x || root q x.
Proof.
 (* {{{ *)
move=> p q x.
rewrite /root; move/eqP.
rewrite /= evalp_mul.
by move/integ => [|] ->; rewrite eq_refl // orbT.
 (* }}} *)
Qed.

Lemma rootX : forall x, root X x -> x = 0.
Proof.  by move=> x; rewrite /root /= pone mulr1 add0r; move/eqP. Qed.


(* --------------------------  The Main Theorems  --------------------------- *)

Definition evalp_add := @evalp_add F.
Definition evalp_mul := @evalp_mul F.
Definition evalp_const := @evalp_const F.

Theorem remainder_thm : forall f b, 
  rem f ((X:poly_ring F) - const b) = const (f @ b).
Proof.
 (* {{{ *)
move=> f b.
move: (@remP f (X - const b) (@linear_nz _ _)).
move: (@quoP f (X - const b)).
set p := (X - const b).
have -> : (deg p = Nat (S O)).
  rewrite /p add_unevenL // deg_opp deg_const /=.
  by case b.
move=> H1 H2.
move: {H2}(deg_lt1 H2) => [r Hr].
rewrite Hr.
rewrite Hr in H1.
move: {H1}(congr1 (fun x => evalp x b) H1).
rewrite /p. 
by rewrite !evalp_add !evalp_const !evalp_mul evalp_root mulr0 /= => ->.
 (* }}} *)
Qed.

Theorem root_div1 : forall f x, root f x -> rdivides (X - const x) f.
Proof.
 (* {{{ *)
move=> f x.
rewrite /root /divides. 
move/eqP => Hx.
exists (quo f (X - const x)).
move: (@quoP f (X - const x)).
rewrite remainder_thm Hx const0 addr0'.
move=> H.
symmetry.
by rewrite mulC'.
 (* }}} *)
Qed.

Theorem root_div2 : forall f x, rdivides (X - const x) f -> root f x.
Proof.
 (* {{{ *)
move=> f x.
rewrite /root /divides. (* XXX can't have the next line here??? *)
move=> [b <-].
by rewrite evalp_mul evalp_root.
 (* }}} *)
Qed.

(* ------------------------------  more roots  ------------------------------ *)

Lemma root_linear : forall x y : F, root (X + const x) y -> y = -x.
Proof.
 (* {{{ *)
move=> x y.
move/root_div1 => [q Hq].
have Hq1 : deg q = Nat O.
  move/(congr1 (@deg _)): (Hq).
  rewrite deg_mul const_opp !deg_linear /=.
  case H : (deg q) => [|k] //=.
  by case: k H.
move/deg0: Hq1 => [H1 [c Hc2]].
move: Hq.
rewrite Hc2 distPM const_opp const_mul.
rewrite addC [_ + const x]addC.
rewrite -{2}(mulr1 X).
move=> H.
have Hc : c = 1.
  move: (congr1 (fun p => coef p 1%nat) H).
  by rewrite -!hornerP !coef_horner /= coef_const.
rewrite Hc const1 !mulr1 in H.
move/(congr1 (fun x => x + (- X))) : H.
rewrite -!addA !oppR !addr0 => H.
move: (congr1 (fun p => coef p O) H).
rewrite !coef_const => <-.
by rewrite opp_opp.
 (* }}} *)
Qed.

Theorem root_bound : forall n (p : poly), deg p = Nat n -> forall l, all (root p) l -> uniq l -> (size l <= n)%N.
Proof.
 (* {{{ *)
elim=> [|n IH] p //=.
  move/deg0 => [H1 [c Hc]].
  rewrite Hc.
  case => [|x l] //=.
  move/andP => [H2 H3].
  move/root_const: H2.
  move/eqP => H.
  by rewrite H /= in Hc.
move=> Hp [|x l] //=.
move/andP => [H1 H2].
move/andP => [H3 H4].
move/root_div1: H1 => [q Hq].
move: (congr1 (@deg _) Hq).
rewrite deg_mul const_opp deg_linear => H.
have Hq1 : deg q = Nat n.
  rewrite {}Hp in H.
  case: {Hq} q H => [|q] //=.
  by move=> [->].
move: {IH Hq1} (IH _ Hq1) => IH.
rewrite leqSS.
suffices Hq2 : all (root q) l by auto.
move: {IH H} H2.
rewrite -{}Hq => H.
apply/allP => y Hy.
move/allP: (Hy) => T.
move/T: H.
move/root_prod.
move/orP => [|] //.
rewrite const_opp.
move/root_linear.
rewrite opp_opp => H.
case : H3.
by rewrite -H Hy.
 (* }}} *)
Qed.

(* ----------------------------  Euclidean Ring  ---------------------------- *)

Definition poly_id := idom_of_nzring (poly_idom F).

Definition poly_ering : euclid_ring.
 (* {{{ *)
exists poly_id (@deg F).
- exact: degInf.
- by move=> x ->.
- move=> a [|b] // _.
  exact: deg_mulL.
move=> a [|b] // _.
set q := quo a (Nz b).
set r := rem a (Nz b).
apply: (@Div_res poly_id _ _ _ q r).
  exact: quoP.
exact: remP.
 (* }}} *)
Defined.

End Div.

Section Euclid.

Variable F : nzfield.

Notation poly := (poly_ering F).

(* -----------------------------  Irreducible  ------------------------------ *)

Definition is_const (p : poly) := exists c : F, c <> 0 /\ p = const c.

Definition irr (p : poly) := forall p1 p2, p = p1 * p2 -> deg p1 = Nat O \/ deg p2 = Nat O.

Definition deg_mul' := @deg_mul F.
Definition invR' := @invR F.

Lemma addi_eq0 : forall x y, (x + y)%I = Nat O -> x = Nat O /\ y = Nat O.
Proof. by move=> [|[|x]] [|[|y]]. Qed.

Definition const_mul := @const_mul F.
Lemma unit_const : forall p : poly, unit p <-> is_const p.
Proof.
 (* {{{ *)
move=> p.
split.
  move=> [q Hq].
  move: (congr1 deg Hq).
  rewrite deg_mul' /=.
  move/addi_eq0 => [H1 _].
  move/deg0: H1 => [H [c Hc]].
  exists c; split => //.
  move=> H'.
  by rewrite H' const0 in Hc.
move=> [c [Hc ->]].
rewrite /unit.
exists (const c^-1).
by rewrite const_mul invR'.
 (* }}} *)
Qed.

Lemma irr_prime : forall p : poly_ering F, (~ is_const p /\ irr p) <-> prime p.
Proof.
 (* {{{ *)
move=> p.
rewrite /irr /prime.
split.
  move=> [H1 H].
  split.
    by move/unit_const.
  move=> x y Hxy.
  move: (H x y).
  apply: antsE; first by symmetry.
  move=>[|].
    move/deg0 => [H2 [c Hc]].
    rewrite Hc in H2 *.
    left.
    exists (const c^-1).
    rewrite const_mul invR' //.
    move=> Hc'.
    by rewrite Hc' in H2.
  move/deg0 => [H2 [c Hc]].
  rewrite Hc in H2 *.
  right.
  exists (const c^-1).
  rewrite const_mul invR' //.
  move=> Hc'.
  by rewrite Hc' in H2.
move=> [H1 H2].
split.
  by move/unit_const.
move=> q r H.
rewrite H in H2.
move: (H2 q r).
apply: antsE => //.
move=> [|].
  move/unit_const => [c [Hc Hc']].
  rewrite Hc'; left.
  rewrite deg_const.
  by case: c Hc Hc'.
move/unit_const => [c [Hc Hc']].
rewrite Hc'; right.
rewrite deg_const.
by case: c Hc Hc'.
 (* }}} *)
Qed.

Lemma irr0 : ~ irr 0.
Proof. 
 (* {{{ *)
rewrite /irr.
move=> H.
move: (H 0 0).
apply: antsE; first by rewrite mulr0. 
by move=> [|]. 
 (* }}} *)
Qed.

End Euclid.


