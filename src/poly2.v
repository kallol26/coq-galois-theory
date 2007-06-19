Require Import ssr.
Require Import lib.
Require Import ring.
Require Import nzring.
Require Import poly.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

Open Scope poly_scope.

(* ========================================================================== *)
(*  degree, lc, powX, idom structure                                          *)
(* ========================================================================== *)

Section Poly2.

Notation "0" := (@Zero _).

Variable R : nzidom.

(* ------------------------  Defs at the ring level  ------------------------ *)

Notation poly := (poly_ring R).

Definition const c : poly_ring R := if c is Nz c' then Nz (Lc c') else 0.

Definition X : poly_ring R := Nz(0::(Lc (one_nz _))).

(* ---------------------  Lemma instances at Ring type  --------------------- *)

Lemma cmulnz1 : forall p : polynz R, cmul_nz (one_nz _) p = p.
Proof. exact: cmulnz1. Qed.

Lemma const_add : forall c1 c2 : R, (const c1 + const c2) = const (c1 + c2).
Proof. exact: const_add. Qed.

Lemma mulX : forall p : poly, X * p = if p is Nz p' then Nz (0::p') else 0.
Proof. exact: mulX. Qed.

Lemma hornerP : forall (c : R) (p : poly), horner c p = const c + X * p.
Proof. exact: hornerP. Qed.

Lemma const_cmul : forall (c : R) (p : poly), (const c) * p = poly.cmul c p.
Proof. exact: const_cmul. Qed.

Lemma coef_add : forall (p q : poly) i, coef (p + q) i = (coef p i + coef q i).
Proof. exact: coef_add. Qed.

Lemma coef_opp : forall n (p:poly), coef (- p) n = - (coef p n).
Proof. exact: coef_opp. Qed.

Lemma coef_const : forall (x : R) i, coef (const x) i = if i is O then x else 0.
Proof. exact: coef_const. Qed.

(* -----------------------------  Misc lemmas  ------------------------------ *)

Lemma cmul_horner : forall (p : poly) (c c' : R),
  cmul c (const c' + X * p) = const (c * c')%R + X * (cmul c p).
Proof. move=> p c c'.  by rewrite -!hornerP !cmul_horner. Qed.

Lemma horner0 : forall (p : poly) (c : R), const c + X * p = 0 -> c = 0 /\ p = 0.
Proof. by move=> [|p] [|c]. Qed.

Lemma const_opp : forall c:R, - const c = const (-c).
Proof. by case. Qed.

Lemma const00 : forall c : R, (const c == 0) = (c == 0).
Proof. by case. Qed.

Lemma const0 : const (0:R) = 0.
Proof. done. Qed.

Lemma const1 : const (1:R) = 1.
Proof. done. Qed.

Lemma linear_nz : forall c, X - const c <> 0.
Proof.
 (* {{{ *)
move=> c Hc.
move: (congr1 (fun x => coef x (S O)) Hc).
by rewrite coef_add coef_opp coef_const /= .
 (* }}} *)
Qed.

(* need to recast this for polynomials as a ring *)
Lemma poly_ind : forall (P : poly -> Prop),
   P 0 -> (forall (c : R) (p : poly), P p -> P (const c + X * p))
        -> (forall (p : poly), P p).
Proof. 
 (* {{{ *)
move=> P H0 H1 [|p] //.
elim: p => [c | h t IH].
  move: (H1 (Nz c) 0) => /= H.
  by apply H.
move: {H1 IH H0}(H1 h (Nz t) IH).
rewrite /mulr /const /=.
case: h => [|h] //=.
  by rewrite cmulnz1 add0r.
by rewrite cmulnz1.
 (* }}} *)
Qed.

(* ----------------------  abstract common reasoning  ----------------------- *)

Ltac hornerize := rewrite addrCA !addA const_add -addA -distMP.
Ltac hornerize' H := rewrite addrCA !addA const_add -addA -distMP in H.

(* --------------------------------  degree  -------------------------------- *)

Fixpoint deg_nz (p : polynz R) {struct p} : nat :=
  if p is h::t then S (deg_nz t) else O. 

Definition deg (p : poly) := if p is Nz p' then Nat (deg_nz p') else -oo.

Definition constant p := deg p = Nat O \/ deg p = -oo.
Definition linear p := deg p = Nat 1.
Definition quadratic p := deg p = Nat 2.
Definition cubic p := deg p = Nat 3.
Definition quartic p := deg p = Nat 4.
Definition quintic p := deg p = Nat 5.

Definition irreducible (p : poly) := forall p1 p2, p = p1 * p2 -> deg p1 = Nat O \/ deg p2 = Nat O.

Lemma deg_horner : forall (c : R) (p : poly), deg (const c + X * p) = 
  if p is Nz _ then S' (deg p) else if c is Nz _ then Nat O else Inf.
Proof. move=> [|c] [|p] //= ; by rewrite cmulnz1.  Qed.

Lemma deg_const : forall (c : R), deg (const c) = if c is Nz _ then Nat O else Inf.
Proof.  move=> c. by case c. Qed.

Lemma nz_ni : forall p : polynz R, deg (Nz p) <> -oo. Proof. by case. Qed.

Lemma add_uneven_nz : forall p1 p2 : poly, deg p2 < deg p1 -> p1 + p2 <> 0.
Proof.
 (* {{{ *)
elim/poly_ind => [p2|c p1 IH]; first by rewrite ltmi.
elim/poly_ind => [|d p2 _].
  by case: {IH}p1 => [|p1]; case c.
rewrite !deg_horner.
case: p1 IH => [|p1] IH.
  case: p2 => [|p2].
    case: d => [|d] //.
      by case: c.
    by case: c.
  by case: c.
case: p2 => [|p2] //.
  case: d => [|d] //.
    by case: c.
  by case: c.
rewrite ltiS.
move/IH => {IH} IH.
rewrite addrCA !addA const_add -addA -distMP /=.
rewrite /= in IH.
case H : (add_nz p1 p2) => [|k] //.
move/(congr1 deg).
rewrite deg_horner /=.
by case H' : (_ + _).
 (* }}} *)
Qed.

Lemma add_unevenL : forall p1 p2 : poly, deg p2 < deg p1 -> deg (p1 + p2) = deg p1.
Proof.
 (* {{{ *)
elim/poly_ind => [p2|c p1 IH]; first by rewrite ltmi.
elim/poly_ind => [|d p2 _]; first by rewrite addr0.
case: p1 IH => [_|p1 IH].
(*   rewrite pzero mulr0 addr0 deg_const. *)
  rewrite mulr0 addr0 deg_const.
  case: c => [|c]; first by rewrite ltmi.
  rewrite deg_horner.
  case: p2 => [|p2].
  case: d => [|d] // .
  by case H : (deg _).
case: p2 => [_|p2].
  by rewrite mulr0 addr0 addC addA const_add !deg_horner.
rewrite !deg_horner ltiS => H.
move: {IH}(IH (Nz p2) H) => H'.
rewrite !addA [const c + _]addC -!addA [const c + _]addA const_add.
rewrite addA addC addA -distMP addC [(Nz p2:poly) + _]addC.
case H2 : ((Nz p1:poly) + _) => [|x].
  contradiction (add_uneven_nz H H2).
by rewrite deg_horner -H2 H'.
 (* }}} *)
Qed.

Lemma add_unevenR : forall p1 p2 : poly, deg p1 < deg p2 -> deg (p1 + p2) = deg p2.
Proof. move=> p1 p2 IH. rewrite addC. by apply: add_unevenL. Qed.

Lemma degInf : forall p : poly, deg p = -oo -> p = 0.
Proof. by case. Qed.

Lemma deg0nz : forall p : poly, deg p = Nat O -> exists c, p = Nz(Lc c).
Proof. case=> [|[c|c p]] //= _ . by exists c. Qed.

Lemma degXn : forall p, deg (X * p) = S' (deg p).
Proof. move=> p. rewrite mulX. by case: p. Qed.

Lemma deg_cmul : forall (p : poly) c, 
  deg(cmul c p) = if c is Nz _ then deg p else -oo.
Proof.
 (* {{{ *)
elim/poly_ind => [|c p IH] [|c'] // .
rewrite cmul_horner !deg_horner.
case: p IH => [|p] IH //= .
  case: c => [|c] //= .
  case H : (_ * _) => // .
  contradiction (mul_nz_nz H).
move: {IH}(IH (Nz c')) => /= .
move=> [H].
by rewrite H.
 (* }}} *)
Qed.

Lemma degS : forall p n, deg p = Nat (S n) -> 
  exists c, exists p', p = const c + X * Nz p' /\ deg (Nz p') = Nat n.
Proof.
 (* {{{ *)
elim/poly_ind => [|c [|p] _] n // .
  rewrite mulr0 addr0 deg_const.
  by case c.
move=> H.
exists c.
exists p.
split => // .
rewrite deg_horner /= in H.
move: H => [H].
by rewrite /= H.
 (* }}} *)
Qed.

Open Scope poly_scope.

Lemma deg_add_nz_aux : forall n (p q : poly), 
  deg p = n -> deg p = deg q -> deg (p + q) <= deg p.
Proof.
 (* {{{ *)

move=> [|n] p q Hp Hq.
  move: (degInf Hp) => -> /= .
  by rewrite add0r -Hq Hp lei_refl.
move: p q Hp Hq.
elim: n => [|n IH] p q Hp Hq.
move: {Hq}(sym_equal Hq) => Hq.
  rewrite Hp in Hq.
  move: {Hp}(deg0nz Hp) => [c Hp].
  move: {Hq}(deg0nz Hq) => [d Hq].
  rewrite Hp Hq /=. 
  rewrite /addr /ring_of_nzring /= deg_const.
  by case H : (nzring.add_nz _ _).
move: (degS Hp) => [c [p' [-> Hc2]]].
rewrite Hp in Hq.
move: {Hq}(sym_equal Hq) => Hq.
move: (degS Hq) => [d [q' [-> Hd2]]].
rewrite (addrCA _ (const d)) !addA const_add -addA -distMP.
rewrite !deg_horner.
case H : (_ + _) => [|x].
  by case: (@addr (ring_of_nzring (b_idom R)) d c).
rewrite -H leiS.
apply: IH => // .
by rewrite Hc2 Hd2.

 (* }}} *)
Qed.

Lemma deg_add_nz : forall p q : poly, 
  deg p = deg q -> deg (p + q) <= deg p.
Proof. by move=> p q H; apply (@deg_add_nz_aux (deg p)). Qed.

Lemma deg_add : forall p q : poly, deg (p + q) <= maxi (deg p) (deg q).
Proof.
 (* {{{ *)
move=> [|p] [|q] // ; try exact : leqnn.
case: (leqiP (deg (Nz p)) (deg (Nz q))).
  rewrite leq_eqVlti.
  move/orP => [|].
    move/eqP => H.
    apply: (lei_trans (deg_add_nz H)).
    exact: maxi_leL.
  move=> H.
  move: (add_unevenR H) => H'.
  rewrite H'.
  exact: maxi_leR.
move=> H.
move: (add_unevenL H) => H'.
rewrite H'.
exact: maxi_leL.
 (* }}} *)
Qed.

Lemma add0_deg : forall p q : poly, p + q = 0 -> deg p = deg q.
Proof.
 (* {{{ *)

elim/poly_ind=> [|c p IH].
  by move=> q; rewrite add0r => ->.
elim/poly_ind=> [|d q _].
  by rewrite addr0 => ->.
hornerize.
case H : (p + _) => [|x].
  rewrite mulr0 addr0.
  move: {IH H}(IH q H) => H H'.
  case: p H => [|p].
    rewrite mulr0 addr0.
    move/esym=> H.
    rewrite /= in H.
    move: (degInf H) => ->.
    rewrite mulr0 addr0.
    rewrite !deg_const.
    by case: c H' => [|c] H';case: d H'.
  case: q => [|q] //.
  by rewrite !deg_horner => ->.
move=> H'.
by move: (horner0 H') => [H1 H2].

 (* }}} *)
Qed.

Lemma deg_opp : forall p : poly, deg (- p) = deg p.
Proof.
 (* {{{ *)

elim/poly_ind => [|c p IH] //.
rewrite -mul_opp1r distMP mulA mul_opp1r [- _ * _]mulC -mulA mul_opp1r const_opp.
rewrite !deg_horner.
case: p IH => [|p] IH //=.
  by case c.
rewrite /= in IH.
by move: IH => [<-].

 (* }}} *)
Qed.

Lemma deg_lt1 : forall p : poly, deg p < Nat (S O) -> exists c, p = const c.
Proof.
 (* {{{ *)

move=> p.
case H : (deg p) => [|x].
  move=> _.
  exists (0 : R).
  by move: (degInf H).
move=> [H'].
rewrite ltnS leqn0 in H'.
move: H'.  
move/eqP => H'.
rewrite {}H' in H.
move: (deg0nz H) => [c ->].
by exists (Nz c).

 (* }}} *)
Qed.

Lemma deg_linear : forall x, deg (X + const x) = Nat 1%nat. 
Proof. by case. Qed.

Lemma deg0 : forall p : poly, deg p = Nat O -> (p <> 0) /\ exists c : R, (p = const c).
Proof.
 (* {{{ *)

move=> p.
move/deg0nz => [c ->].
split => //.
by exists (Nz c).

 (* }}} *)
Qed.

Lemma degX : deg X = Nat 1%nat.
Proof. done. Qed.


(* -------------------------  leading coefficient  -------------------------- *)

Fixpoint lc_nz (p : polynz R) {struct p} : base' R :=
  match p with 
    | Lc c => c
    | h::t => lc_nz t
  end.

Definition lc (p : poly) : R := if p is Nz p' then Nz (lc_nz p') else 0.

Definition monic p := lc p = 1.

Lemma lc_nz_nz : forall p, lc p <> 0 -> p <> 0.
Proof. by move=> [|[c|c p]]. Qed.

Lemma lc_horner : forall c p, lc (const c + X * p) = if p is Nz _ then lc p else c.
Proof. by move=> [|c] [|p] //=; rewrite cmulnz1. Qed.

Lemma lc_mulX : forall p, lc (X * p) = lc p.
Proof. move=> [|p] //. by rewrite mulX /= . Qed.

Lemma const_mul : forall c1 c2 : R, const c1 * const c2 = const (c1 * c2).
Proof. exact: const_mul. Qed.

Lemma lc_cmul : forall (p:poly) (c:R), lc (const c * p) = c * lc p.
Proof.
 (* {{{ *)

elim/poly_ind => [|c p IH] d.
  by rewrite mulr0 /= mulr0.
rewrite lc_horner.
case: p IH => [|p] IH.
  rewrite mulr0 addr0 const_mul.
  by case: (d * c).
rewrite distMP const_mul -IH mulA.
rewrite (mulC _ X) -mulA IH lc_horner.
case H : (_ * _) => [|x].
  rewrite const_cmul in H.
  by move: (cmul_nz_z H) => -> .
by rewrite -H IH.

 (* }}} *)
Qed.

Lemma lc_const : forall c : R, lc (const c) = c.
Proof.  by case. Qed.

Lemma add_uneven_lcL : forall p1 p2 : poly, deg p2 < deg p1 -> lc (p1 + p2) = lc p1.
Proof.
 (* {{{ *)

elim/poly_ind => [p2|c p1 IH]; first by rewrite ltmi.
elim/poly_ind => [|d p2 _]; first by rewrite addr0.
case: p1 IH => [_|p1 IH].
  rewrite mulr0 addr0 deg_const.
  case: c => [|c]; first by rewrite ltmi.
  rewrite deg_horner.
  case: p2 => [|p2].
  case: d => [|d] // .
  by case H : (deg _).
case: p2 => [_|p2].
  by rewrite mulr0 addr0 addC addA const_add !lc_horner.
rewrite !deg_horner ltiS => H.
move: {IH}(IH (Nz p2) H) => H'.
rewrite !addA [const c + _]addC -!addA [const c + _]addA const_add.
rewrite addA addC addA -distMP addC [(Nz _:poly) + _]addC.
case H2 : ((Nz p1 : poly) + _) => [|x].
  contradiction (add_uneven_nz H H2).
by rewrite [_ + const c]addC !lc_horner -H2 H'.

 (* }}} *)
Qed.

Lemma add_uneven_lcR : forall p1 p2 : poly, deg p1 < deg p2 -> lc (p1 + p2) = lc p2.
Proof. move=> p1 p2 IH. rewrite addC. by apply: add_uneven_lcL. Qed.

Lemma mulC' : forall x y : poly, x * y = y * x. Proof. exact: mulC. Qed.

Lemma lc_opp : forall p : poly, lc (- p) = - lc p.
Proof.
 (* {{{ *)
elim/poly_ind => [|c p IH] //.
rewrite -mul_opp1r distMP mulA mul_opp1r [_ * X]mulC' -mulA mul_opp1r  const_opp.
rewrite !lc_horner.
by case: p IH.
 (* }}} *)
Qed.

Lemma add0_lc : forall p q : poly, p + q = 0 -> lc p = - lc q.
Proof.
 (* {{{ *)
elim/poly_ind=> [|c p IH] q Hq.
  rewrite add0r in Hq.
  by rewrite Hq /=.
move: q Hq.
elim/poly_ind=> [|d q _].
  rewrite addr0 => H.
  by move: (horner0 H) => [-> ->] /=.
hornerize => H.
rewrite lc_horner.
move: {H}(horner0 H) => [H1 H2].
move: {IH H2}(IH q H2) => H'.
case: p H' => [|p].
  move/esym;move/eqP.
  rewrite {2}/lc (@oppr0 (idom_of_nzring R)).
  move/eqP => H.
  rewrite lc_horner.
  case: q H => [|q] H //.
  apply: (@addr_injl _ d).
  by rewrite H1 oppR.
move=> H.
rewrite H lc_horner.
by case: q H.
 (* }}} *)
Qed.

Lemma add_even_lc0 : forall p q : poly, 
  deg p = deg q -> p + q = 0 -> lc (p + q) = lc p + lc q.
Proof.
 (* {{{ *)
elim/poly_ind=>[|c p IH] //. 
elim/poly_ind=>[|d q _] Hp Hq.
  by rewrite {3}/lc !addr0.
rewrite Hq.
move: Hq.
hornerize => Hq.
move: (horner0 Hq) => [H1 H2].
rewrite !lc_horner.
case: p IH Hp Hq H2 => [|p] IH Hp Hq H2.
  rewrite add0r in H2.
  rewrite H2 /=.
  symmetry.
  by rewrite addC.
case: q Hp Hq H2 => [|q] Hp Hq H2.
  by rewrite addr0 in H2.
rewrite -IH => //.
  by rewrite /= in H2; rewrite /= H2.
rewrite !deg_horner in Hp.
exact: (S'_inj Hp).
 (* }}} *)
Qed.

Lemma lc_cancel : forall p q : poly,
  q <> 0 -> deg p = deg q -> lc p = - lc q -> deg (p + q) < deg q.
Proof.
 (* {{{ *)
elim/poly_ind=> [|c p IH] //; first by case.
elim/poly_ind=> [|d q _] //.
hornerize.
case: p IH => [|p] IH.
  rewrite mulr0 addr0 add0r.
  case: q => [|q].
    rewrite mulr0 !addr0.
    case: c => [|c] Hd.
      move/esym => /= H.
      contradiction (Hd (degInf H)).
    case: d Hd => [|d] Hd // _.
    rewrite !lc_const => ->.
    by rewrite oppR.
  rewrite deg_const deg_horner.
  by case: c.
case: q => [|q].
  rewrite mulr0 !addr0.
  rewrite deg_const deg_horner.
  by case d.
rewrite 2!deg_horner => _.
move/S'_inj => H.
case H' : ((Nz _:poly) + _) => [|x].
  rewrite mulr0 addr0.
  rewrite deg_const.
  by case: (d+c).
rewrite deg_horner ltiS !lc_horner -H' => Hl.
by apply: IH.
 (* }}} *)
Qed.

Lemma lcX : lc X = 1.
Proof. done. Qed.

(* --------------------------  the main theorems  --------------------------- *)

Lemma deg_mul_lt : forall p q : poly, p <> 0 -> q <> 0 -> 
  deg p <= deg (p * q) /\ deg q <= deg (p * q).
Proof.
 (* {{{ *)
elim/poly_ind => [|c p IH] q // .
move=> Hp.
case: q => [|q] //.
move=> _.
case: p IH Hp => [|p] IH Hp.
  rewrite mulr0 addr0 in Hp.
  case: c Hp => [|c] //.
  clear.
  rewrite mulr0 addr0 const_cmul deg_cmul /=.
  split.
    exact: leq0n.
  exact: leqnn.
clear Hp.
move: {IH}(IH (Nz q)).
elim=> // H1 H2.
have H' : (Nz p:poly) * Nz q <> 0.
  move=> H'.
  by rewrite H' /= in H1 H2.
split.
  rewrite deg_horner.
  rewrite distPM add_unevenR.
    by rewrite -mulA degXn leiS.
  rewrite const_cmul -mulA degXn deg_cmul.
  case: c => [|c].
    case Hd: (deg _) => [|x] //.
    move: (degInf Hd) => T.
    contradiction (H' T).
  apply: (leti_trans H2).
  case H : (deg _) => [|y].
    move: (degInf H) => T.
    contradiction (H' T).
  rewrite -H.
  apply: ltinSn.
  by move/degInf.
rewrite distPM add_unevenR.
  rewrite -mulA degXn.
  apply: (lei_trans H2).
  case H : (deg _) => [|y].
    move: (degInf H) => T.
    contradiction (H' T).
  rewrite -H.
  exact: lenSn.
rewrite -mulA degXn.
case: c => [|c].
  rewrite /= .
  case Hd: (deg _) => [|x] //.
  move: (degInf Hd) => T.
  contradiction (H' T).
rewrite const_cmul deg_cmul.
apply: (leti_trans H2).
case H : (deg _) => [|y].
  move: (degInf H) => T.
  contradiction (H' T).
rewrite -H.
apply: ltinSn.
by move/degInf.
 (* }}} *)
Qed.

Notation polynz := (base' (poly_ring R)).

Lemma deg_mulL : forall p (q : polynz), deg p <= deg (p * Nz q).
Proof.
 (* {{{ *)
move=> p q.
move: (@deg_mul_lt p (Nz q)).
case: p => [|p] //.
by elim.
 (* }}} *)
Qed.

Lemma deg_mulR : forall q (p : polynz), deg q <= deg ((Nz p:poly) * q).
Proof.
 (* {{{ *)
move=> q p.
move: (@deg_mul_lt (Nz p) q).
case: q => [|q] //.
by elim.
 (* }}} *)
Qed.

Lemma pnz_nz : forall p q : polynz, (Nz p:poly) * Nz q <> 0.
Proof.
 (* {{{ *)
move=> p q H.
move: {H}(congr1 deg H) => H.
move: (@deg_mul_lt (Nz p) (Nz q)).
elim => //.
rewrite /= in H *.
by rewrite H /=.
 (* }}} *)
Qed.

Lemma deg_mul : forall p q : poly, deg (p * q) = (deg p + deg q)%I.
Proof.
 (* {{{ *)

elim/poly_ind => [|c [|p] IH] q // .
  rewrite !mulr0 addr0.
  rewrite const_cmul deg_const deg_cmul.
  case: c => [|c] // .
  by rewrite add0i.
case: q => [|q]; first by rewrite mulr0 add_minf.
rewrite !deg_horner distPM add_unevenR -mulA degXn IH addiSSn => // .
rewrite -addiSSn -{}IH.
apply: (@leti_trans (deg ((Nz p:poly) * Nz q))).
  rewrite const_cmul deg_cmul.
  case: c => [|c] //.
  exact: deg_mulR.
case H : (deg _) => [|x].
  move: {H}(degInf H) => H.
  contradiction (pnz_nz H).
exact: ltiSn.

 (* }}} *)
Qed.

Lemma lc_mul : forall p q : poly, lc (p * q) = lc p * lc q.
Proof.
 (* {{{ *)

elim/poly_ind => [|c p IH] [|q] //.
  by rewrite mulr0 lc_horner /= mulr0.
rewrite lc_horner.
case: p IH => [|p] IH.
  by rewrite mulr0 addr0 lc_cmul.
rewrite -IH distPM.
rewrite add_uneven_lcR.
  by rewrite -mulA lc_mulX.
rewrite const_cmul deg_cmul -mulA degXn.
case: c => [|c].
  case H: (deg _) => //.
  move: {H}(degInf H) => H.
  contradiction (pnz_nz H).
case H: (deg (_ * _)) => [|x] //.
  move: {H}(degInf H) => H.
  contradiction (pnz_nz H).
case H': (deg _) => [|y] //.
rewrite -H -H'.
apply: (@leti_trans (deg ((Nz p:poly) * Nz q))).
  exact: deg_mulR.
rewrite /= in H.
rewrite /= H.
exact: ltiSn.

 (* }}} *)
Qed.

(* ---------------------------------  powX  --------------------------------- *)

Fixpoint powX (n : nat) {struct n} : poly :=
  if n is S n' then X * powX n' else 1.

Lemma powX0 : forall n, powX n <> 0.
Proof. elim=> [|n IH] //=. by case H : (powX n) => [|k]. Qed.

Lemma deg_powX : forall n, deg (powX n) = Nat n.
Proof.
 (* {{{ *)
elim=> [|n IH] //=.
case H : (powX n) => [|x].
  contradiction (powX0 H).
rewrite deg_mul -H IH. 
by rewrite /X /=.
 (* }}} *)
Qed.


Lemma lc_powX : forall n, lc (powX n) = 1.
Proof.
 (* {{{ *)
elim=> [|n IH] //=.
case H : (powX n) => [|x].
  contradiction (powX0 H).
by rewrite -H lc_mul IH lcX (@mulr1 (idom_of_nzring R)).
 (* }}} *)
Qed.

(* ---------------------------------  eval  --------------------------------- *)

Fixpoint evalp_nz (p : polynz) (x : R) {struct p} : R :=
  match p with
    | Lc c => Nz c
    | c::p' => c + x * evalp_nz p' x
  end.

Definition evalp p x := if p is Nz p' then evalp_nz p' x else 0.

Notation "p @ x" := (evalp p x) (at level 36, right associativity).

Lemma evalp_const : forall c d : R, const c @ d = c.
Proof. by move=> [|c] [|d]. Qed.

Lemma evalp0 : forall c : R, (0:poly) @ c = 0.
Proof. done. Qed.

Lemma evalp_horner : forall (p:poly) (c d : R), (const c + X * p) @ d = c + d * (p @ d).
Proof. move=> [|p] [|c] [|d] // ; by rewrite /= cmulnz1. Qed.

Lemma evalp_add : forall (p q : poly) (c : R), (p + q) @ c = (p @ c) + (q @ c).
Proof. 
 (* {{{ *)
elim/poly_ind => [|d p IH] //. 
elim/poly_ind => [|e q _] c//.
  by rewrite addr0 evalp0 addr0.
rewrite addrCA !addA const_add -addA -distMP !evalp_horner IH distMP !addA.
by rewrite [_ + e]addC addA.
 (* }}} *)
Qed.

Lemma evalp_Xmul : forall (p: poly) x, (X * p) @ x = x * (p @ x).
Proof.
 (* {{{ *)

move=> [|p] x.
  by rewrite mulr0 evalp0 mulr0.
by rewrite /= cmulnz1.

 (* }}} *)
Qed.

Lemma evalp_cmul : forall p (c : R) x, (const c * p) @ x = c * (p @ x).
Proof.
 (* {{{ *)
elim/poly_ind => [|d p IH] c x //. 
  by rewrite mulr0 evalp0 /= mulr0.
rewrite distMP const_mul evalp_add .
rewrite evalp_horner distMP evalp_const mulA [const c * _]mulC' -mulA evalp_Xmul.
by rewrite IH [x * (c * _)](@mulrCA (idom_of_nzring R)).
 (* }}} *)
Qed.

Lemma evalp_mul : forall (p q : poly) (c : R), (p * q) @ c = (p @ c) * (q @ c).
Proof.
 (* {{{ *)
elim/poly_ind => [|d p IH] //. 
elim/poly_ind => [|e q _] c//.
  by rewrite !evalp0 !mulr0.
rewrite !evalp_horner distPM distMP !evalp_add const_mul evalp_const.
rewrite evalp_cmul evalp_Xmul distMP evalp_add -!mulA !evalp_Xmul.
rewrite !mulA [p * _]mulC' evalp_cmul [p * _]mulC' -!mulA evalp_Xmul IH.
rewrite !distMP !distPM -!mulA -!addA.
congr addr.
rewrite addC -!addA.
congr addr.
  congr mulr.
  exact: mulC.
rewrite addC.
congr addr.
congr mulr.
by rewrite (@mulrCA (idom_of_nzring R)).
 (* }}} *)
Qed.

Lemma evalp_opp : forall (p : poly) (c : R), - p @ c = - (p @ c).
Proof.
 (* {{{ *)
move=> p c.
rewrite -mul_opp1r evalp_mul.
have -> : (- (1:poly)) @ _ = (- (1:R)) => //.
by rewrite mul_opp1r.
 (* }}} *)
Qed.

Lemma evalpX : forall c, X @ c = c.
Proof. 
 (* {{{ *)
move=> c.
have -> : X = X * 1.
  by rewrite mulr1.
rewrite evalp_Xmul /=.
rewrite -(mulr1 c).
rewrite /mulr /=.
congr nzring.mul.
exact: nzmulr1.
 (* }}} *)
Qed.

Lemma evalp_root : forall c, (X - const c) @ c = 0.
Proof. move=> c. by rewrite evalp_add evalp_opp evalp_const evalpX oppR. Qed.

(* ----------------------------  Idom structure  ---------------------------- *)

Canonical Structure poly_idom := Nz_idom pnz_nz.

End Poly2.

Notation "p @ x" := (evalp p x) (at level 36, right associativity) : poly_scope.

Prenex Implicits const deg lc.