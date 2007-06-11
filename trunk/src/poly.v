Require Import ssr.
Require Import lib.
Require Import ring.
Require Import nzring.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

(* ========================================================================== *)
(* Polynomial definition, and the ring structure                              *)
(* ========================================================================== *)

Section Poly.

Notation "0" := (@Zero _).

Variable R : nzidom.

Inductive polynz : Type := Lc (c : base' R) | Pcons (h : R) (t : polynz).

Notation "h :: t" := (Pcons h t) (at level 70).

Fixpoint eqpolynz (p1 p2 : polynz) {struct p1} : bool := 
  match p1, p2 with
    | Lc c1, Lc c2 => c1 == c2
    | c1::t1, c2::t2 => (c1 == c2) && eqpolynz t1 t2 
    | _, _ => false
  end.

Lemma eqpolynzPx : reflect_eq eqpolynz.
Proof.
 (* {{{ *)
move; elim=> [c1|c1 s1 Hrec]  [c2|c2 s2]; first [by constructor | simpl ]. 
  case: (c1 =P c2) => [<-|Hc]; first by left.
  by right; move=> [H']; case: Hc.
case: (c1 =P c2) => [<-|Hc] /= .
  by apply: (iffP (Hrec _)) => [<-|[E]].
by right; move=> [H1 H2].
 (* }}} *)
Qed.

Canonical Structure polynzData := EqType eqpolynzPx.

Definition poly := (withzeroData polynzData).

(* ---------------------------------  one  ---------------------------------- *)

Definition onep := Lc (one_nz _).
Notation "1" := onep.

(* ------------------------------  constants  ------------------------------- *)

Definition const c := if c is Nz c' then Nz (Lc c') else Zero.

(* ----------------------------------  X  ----------------------------------- *)

Definition X := Nz(0::onep).

(* -----------------------------  horner form  ------------------------------ *)

Definition horner c p := if p is Nz p' then Nz (c::p') else const c.

(* ---------------------------------  add  ---------------------------------- *)

Fixpoint add_nz (p1 p2 : polynz) {struct p2} : poly :=
  match p1, p2 with
    | h::t, Lc c => Nz (add h (Nz c) :: t)
    | Lc c, h::t => Nz (add (Nz c) h :: t)
    | Lc c1, Lc c2 => const (nzring.add_nz c1 c2)
    | h1 :: t1, h2 :: t2 => horner (h1 + h2) (add_nz t1 t2)
  end.

Definition add (p1 p2 : poly) : poly := lift_add add_nz p1 p2.
        
(* ---------------------------------  cmul  --------------------------------- *)

Fixpoint cmul_nz (c : base' R) (p : polynz) {struct p} : polynz := 
  match p with
    | Lc c' => Lc (if mul_nz c c' is Nz c'' then c'' else c')
    | h :: t => (nzring.mul (Nz c) h)::(cmul_nz c t) 
  end.

Definition cmul (c : R) (p : poly) : poly := 
  match c, p with
    | Zero, _ => Zero
    | _, Zero => Zero
    | Nz c', Nz p' => Nz (cmul_nz c' p')
  end.

Definition cmulL (c : R) p : poly := if c is Nz c' then Nz (cmul_nz c' p) else Zero.

(* ---------------------------------  mul  ---------------------------------- *)

Fixpoint mul_nz (p1 p2 : polynz) {struct p1} : poly := 
  match p1 with 
    | Lc c => Nz (cmul_nz c p2)
    | h :: t => 
      add (cmulL h p2) (horner Zero (mul_nz t p2))
  end.

Definition mul (p1 p2 : poly) : poly := lift_mul mul_nz p1 p2.

(* ---------------------------------  opp  ---------------------------------- *)

Fixpoint opp_nz (p : polynz) {struct p} : polynz := 
  match p with
    | h::t => - h::opp_nz t 
    | Lc c => Lc (nzring.opp_nz c)
  end.

Definition opp (p : poly) : poly := if p is Nz p' then Nz(opp_nz p') else Zero.

(* ---------------------------------  coef  --------------------------------- *)

Fixpoint coef_nz (p : polynz) (i : nat) {struct i} : R := 
  match p, i with
    | h::t, S n => coef_nz t n
    | h::t, O => h
    | Lc c, O => Nz c
    | Lc c, S n => 0
  end.

Definition coef (p : poly) i : R := if p is Nz p' then coef_nz p' i else 0.

Notation "x1 + x2" := (add x1 x2).
Notation "x1 * x2" := (mul x1 x2).
Notation "- x" := (opp x).
Notation "x - y" := (x + (- y)).
Notation "1" := (Nz onep).

Lemma poly_indh : forall (P : poly -> Prop),
   P Zero -> (forall (c : R) (p : poly), P p -> P (horner c p))
        -> (forall (p : poly), P p).
Proof.
 (* {{{ *)
move=> P H0 H1 [|p] //=. 
elim: p => [c | h t IH].
  move: (H1 (Nz c) Zero) => /= H.
  by apply H.
by move: {H1 IH H0}(H1 h (Nz t) IH).
 (* }}} *)
Qed.

(* --------------------------------  degree  -------------------------------- *)

(* this def is only temporary, to prove the ring axioms *)
Fixpoint deg_nz (p : polynz) {struct p} : nat :=
  if p is h::t then S (deg_nz t) else O. 

Definition deg (p : poly) := if p is Nz p' then Nat (deg_nz p') else -oo.

(* ---------------------------------  cmul  --------------------------------- *)

Lemma cmul_horner : forall c c' p, 
  cmul c (horner c' p) = horner (nzring.mul c c') (cmul c p).
Proof. 
 (* {{{ *)
move=> [|c] [|c'] [|p] //= .
case H : (nzring.mul_nz _ _) => //= .
contradiction (mul_nz_nz H).
 (* }}} *)
Qed.

Lemma cmul0 : forall c, cmul c Zero = Zero.
Proof. by move=> [|c]. Qed.

Lemma cmulnz_cmul : forall c p, Nz (cmul_nz c p) = cmul (Nz c) (Nz p).
Proof. done. Qed.

(* ---------------------------------  coef  --------------------------------- *)

Lemma coef_deg : forall p : polynz, ~(coef_nz p (deg_nz p) == 0).
Proof. by elim. Qed.

Lemma coef_nz_ext : forall p q, coef_nz p =1 coef_nz q -> p = q.
Proof.
 (* {{{ *)
elim => [c1 | x1 t1 IHs1] [c2 | x2 t2] H.
- move: (H O) => /= H'.
  by rewrite (Nz_inj H'). (* hack for slow elim *)
- move: (H (deg_nz (x2 :: t2))).
  move/eqP.
  rewrite eq_sym => H'.
  contradiction (coef_deg H').
- move: (H (deg_nz (x1 :: t1))).
  move/eqP.
  rewrite eq_sym => H'.
  contradiction (coef_deg H').
congr Pcons.
  by move: (H O).
apply: IHs1 => i.
by move: (H (S i)).
 (* }}} *)
Qed.

Lemma coef_ext : forall p q, coef p =1 coef q -> p = q.
Proof. 
 (* {{{ *)
move=> [|p] [|q] //= .
- move/(fun H => H (deg_nz q)) => /= .
  move/eqP.
  rewrite eq_sym => H.
  contradiction (coef_deg H).
- move/(fun H => H (deg_nz p)) => /= .
  move/eqP.
  rewrite eq_sym => H.
  contradiction (coef_deg H).
rewrite /coef => H.
congr Nz.
by apply: coef_nz_ext.
 (* }}} *)
Qed.
  
Lemma coef_const : forall x i, coef (const x) i = if i is O then x else 0.
Proof. by move=> [|x] [| i]. Qed. 

Lemma coef_add : forall p q i, coef (p + q) i = (coef p i + coef q i)%R.
Proof. 
 (* {{{ *)
move=> [|p] [|q] i //=; first by rewrite addr0.
move: p q i.
elim=> [c1|h1 t1 IH] [c2|h2 t2] i //= .
- rewrite coef_const.
  by case i.
- by case i => [|n] //= ; by case: (nzring.add_nz c1 c2).
- by case i => [|n] //= ; first by rewrite addr0.
case: i => [|i] //= .
  case: (add_nz t1 t2) => [|x] //= .
  by rewrite coef_const.
move : {IH}(IH t2 i) => <- .
case: (add_nz t1 t2) => [|x] //=.
by rewrite coef_const.
 (* }}} *)
Qed.

Lemma coef_horner : 
  forall c p n, coef (horner c p) n = if n is S n' then coef p n' else c.
Proof. move=> c [|[c'|h t]] [|n] //= ; exact: coef_const. Qed.

Lemma coef_cmul : forall p c i, coef (cmul c p) i = (c * coef p i)%R.
Proof.
 (* {{{ *)
elim/poly_indh => [|c' p IH] c i //=.
  by rewrite cmul0 mulr0. 
rewrite !coef_horner cmul_horner coef_horner.
by case i.
 (* }}} *)
Qed.

Lemma cmul1 : forall p, cmul 1%R p = p.
Proof. by move=> p; apply coef_ext => i; rewrite coef_cmul mul1r. Qed.

Lemma coef_opp_nz : forall n p, coef_nz (opp_nz p) n = (- (coef_nz p n))%R.
Proof. by elim=> [|n IH] [|[c|h t]] //=. Qed.

Lemma coef_opp : forall n p, coef (- p) n = (- (coef p n))%R.
Proof. elim=> [|n IH] [|[c|h t]] //=; by move: (IH (Nz t)). Qed.

Lemma cmulnz1 : forall p : polynz, cmul_nz (one_nz _) p = p.
Proof.
 (* {{{ *)
move=> p.
apply: Nz_inj => //.
rewrite cmulnz_cmul.
exact: cmul1.
 (* }}} *)
Qed.

Lemma addp0 : forall p : poly, p + Zero = p.
Proof. by move=> [|p]. Qed.

Lemma mulp0 : forall p : poly, p * Zero = Zero.
Proof. by move=> [|p]. Qed.

Lemma const_cmul : forall c p, (const c) * p = cmul c p.
Proof. by move=> [|c]. Qed.

Lemma mulX : forall p, X * p = if p is Nz p' then Nz (0::p') else Zero.
Proof.
 (* {{{ *)
move=> [|p] //.
rewrite /mul /= .
congr Nz; congr Pcons.
apply: Nz_inj => //.
rewrite cmulnz_cmul.
exact: cmul1.
 (* }}} *)
Qed.

Lemma const_add : forall c1 c2 : R, const c1 + const c2 = const (c1 + c2)%R.
Proof.
 (* {{{ *)
move=> c1 c2.
apply: coef_ext.
move=> i.
rewrite coef_add !coef_const.
by case i.
 (* }}} *)
Qed.

Lemma const_mul : forall c1 c2 : R, const c1 * const c2 = const (c1 * c2)%R.
Proof.
 (* {{{ *)
move=> [|c1] [|c2] => //.
apply: coef_ext => i.
rewrite !coef_const.
case: i => [|i] //=.
case H : (nzring.mul_nz _ _) => [|x] //=.
contradiction (mul_nz_nz H).
 (* }}} *)
Qed.

Lemma cmul_add : forall c1 c2 p, cmul (c1 + c2)%R p = cmul c1 p + cmul c2 p.
Proof.
 (* {{{ *)

move=> c1 c2 p.
apply: coef_ext => i.
by rewrite coef_add !coef_cmul distPM.

 (* }}} *)
Qed.

Lemma cmul_nz_z : forall c p, cmul c (Nz p) = Zero -> c = 0.
Proof. by move=> [|c]. Qed.

Lemma hornerP : forall c p, horner c p = const c + X * p.
Proof.  move=> [|c] [|p] //=; by rewrite cmulnz1. Qed.

(* --------------------------------  Axioms  -------------------------------- *)

Lemma opppL : forall p : poly, - p + p = Zero.
Proof. 
 (* {{{ *)
move=> [|p] //.
apply coef_ext. 
move=> i. 
rewrite coef_add /opp /= coef_opp_nz.
by rewrite oppL.
 (* }}} *)
Qed.

Lemma addpA : forall p1 p2 p3 : poly, p1 + (p2 + p3) = p1 + p2 + p3.
Proof. 
 (* {{{ *)
move=> p1 p2 p3.
apply: coef_ext. 
move => i. 
rewrite !coef_add. 
exact: addA. 
 (* }}} *)
Qed.

Lemma addpC : forall p1 p2 : poly, p1 + p2 = p2 + p1.
Proof. 
 (* {{{ *)
move=> p1 p2. 
apply: coef_ext. 
move => i. 
rewrite !coef_add. 
exact: addC. 
 (* }}} *)
Qed.

Lemma mul1p : forall p : poly, 1 * p = p.
Proof.
 (* {{{ *)
move=> [|p] => //=.
rewrite cmulnz_cmul.
apply coef_ext => i.
rewrite coef_cmul.
exact: mul1r.
 (* }}} *)
Qed.

Lemma dist_horner : forall c p1 p2, horner c p1 * p2 = cmul c p2 + X * (p1 * p2).
Proof.
 (* {{{ *)
move=> [|c] [|p1] [|p2] //=.
  case H : (mul_nz _ _) => [|x] //.
  rewrite /horner.
  congr Nz; congr Pcons.
  by rewrite cmulnz1.
case H : (mul_nz _ _) => [|p] //=.
by rewrite cmulnz1.
 (* }}} *)
Qed.

Lemma distcMP : forall c p1 p2, cmul c (p1 + p2) = cmul c p1 + cmul c p2.
Proof.
 (* {{{ *)
move=> c p1 p2.
apply: coef_ext.
move=> i.
by rewrite coef_add coef_cmul coef_add distMP !coef_cmul.
 (* }}} *)
Qed.

Lemma distXMP : forall p1 p2, X * (p1 + p2) = X * p1 + X * p2.
Proof.
 (* {{{ *)
move=> [|p1] [|p2] //.
apply: coef_ext => i.
rewrite !mulX.
case i => {i}[|i] //=.
 (* }}} *)
Qed.

Lemma distpMP : forall p1 p2 p3 : poly, p1 * (p2 + p3) = p1 * p2 + p1 * p3.
Proof.
 (* {{{ *)
move=> p1 p2 p3.
move: p1.
elim/poly_indh => [|c p1 IH] //.
rewrite !dist_horner IH distcMP -!addpA.
congr add.
rewrite addpA.
rewrite {1}[add _ (cmul c _)]addpC -addpA.
congr add.
by rewrite !distXMP.
 (* }}} *)
Qed.

Lemma mulXA : forall p1 p2, X * (p1 * p2) = (X * p1) * p2.
Proof.
 (* {{{ *)
move=> [|p1] [|p2] //=.
rewrite cmulnz1.
case: (mul_nz _ _) => [|x] //.
by rewrite cmulnz1.
 (* }}} *)
Qed.

Lemma distcPM : forall p1 c p2, (const c + p1) * p2 = const c * p2 + p1 * p2.
Proof.
 (* {{{ *)
elim/poly_indh => [|d p1 IH] c p2 //=; first by rewrite !addp0.
by rewrite hornerP addpA const_add -!hornerP !dist_horner const_cmul addpA cmul_add.
 (* }}} *)
Qed.

Lemma distpPM : forall p1 p2 p3: poly, (p1 + p2) * p3 = p1 * p3 + p2 * p3.
Proof.
 (* {{{ *)
elim/poly_indh => [|c p1 IH] p2 p3 //=.
rewrite hornerP -addpA !distcPM -addpA.
congr add.
move: p2.
elim/poly_indh => [|d p2 IH2]; first by rewrite !addp0.
rewrite hornerP addpA [add (X * p1) _]addpC -addpA -distpMP -hornerP !dist_horner.
rewrite IH distpMP distcPM const_cmul !addpA !mulXA. 
congr add.
by rewrite addpC.
 (* }}} *)
Qed.

Lemma mulp1 : forall p:poly, p * 1 = p.
Proof.
 (* {{{ *)
elim/poly_indh => [|c p IH] //=.
rewrite hornerP distpPM -mulXA IH.
congr add.
rewrite const_cmul.
apply: coef_ext => i.
rewrite coef_cmul coef_const.
case: i => [|i] //.
  rewrite /=.
  exact: nzmulr1.
exact: mulr0.
 (* }}} *)
Qed.

Lemma mulcXC : forall c, const c * X = X * const c.
Proof.
 (* {{{ *)

move=> [|c] //=.
move: (nzmulC (Nz c) (Nz (one_nz R))) => /= ->.
case H: (nzring.mul_nz _ _) => //.
by move/mul_nz_nz: H.

 (* }}} *)
Qed.

Lemma mulXC : forall p:poly, X * p = p * X.
Proof.
 (* {{{ *)
elim/poly_indh => [|c p IH] //.
rewrite hornerP distpMP distpPM.
congr add; last by rewrite -mulXA IH.
symmetry.
exact: mulcXC.
 (* }}} *)
Qed.

Lemma mulcXA : forall c p, const c * (X * p) = const c * X * p.
Proof.
 (* {{{ *)
move=> [|c] [|p] //.
apply coef_ext => i /= .
rewrite cmulnz1.
case: i => [|i] //=.
suffices -> : (nzring.mul_nz c (one_nz _) = Nz c) => //.
rewrite mul_nz_mul. 
exact: nzmulr1.
 (* }}} *)
Qed.

Lemma mulcA : forall p1 p2 c, const c * (p1 * p2) = const c * p1 * p2.
Proof.
 (* {{{ *)
elim/poly_indh => [|c p1 IH] p2 d; first by rewrite !mulp0.
rewrite hornerP !distpPM !distpMP !distpPM.
congr add.
  apply: coef_ext => i.
  rewrite const_mul !const_cmul !coef_cmul.
  exact: mulA.
by rewrite -mulXA mulcXA -mulXC -mulXA IH !mulXA mulXC mulcXA.
 (* }}} *)
Qed.

Lemma mulpA : forall p1 p2 p3:poly, p1 * (p2 * p3) = p1 * p2 * p3.
Proof.
 (* {{{ *)
elim/poly_indh => [|c p1 IH] p2 p3 //.
rewrite hornerP !distpPM mulcA.
congr add.
by rewrite -mulXA IH !mulXA.
 (* }}} *)
Qed. 

Lemma mulcC : forall p (c:R), const c * p = p * const c.
Proof.
 (* {{{ *)
elim/poly_indh => [|d p IH] c //=; first by rewrite mulp0.
rewrite hornerP distpPM distpMP !const_mul. 
rewrite mulC.
by rewrite -mulpA -IH mulpA mulXC -mulpA mulXC mulpA. 
 (* }}} *)
Qed.

Lemma mulpC : forall p1 p2, p1 * p2 = p2 * p1.
Proof.
 (* {{{ *)
elim/poly_indh => [|c p1 IH] p2 //=; first by rewrite mulp0.
rewrite hornerP distpPM distpMP mulcC.
congr add.
by rewrite -mulpA IH mulpA mulXC mulpA.
 (* }}} *)
Qed.

(* ----------------------------  Ring structure  ---------------------------- *)

Definition pax := Ring_axioms opppL addpA addpC mul1p mulp1 mulpA distpPM distpMP mulpC.

Canonical Structure poly_ring := Nzring pax.

End Poly.

Notation "h :: t" := (Pcons h t) (at level 70) : poly_scope.
Delimit Scope poly_scope with P.

