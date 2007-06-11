
(** ** A library of useful definitions and theorems. *)

Require Import ssr.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

(* -------------------------------------------------------------------------- *)
(*  Functions                                                                 *)
(* -------------------------------------------------------------------------- *)

(** *** Functions *)

Lemma comb : forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y.
Proof. by move=> A B f x y ->. Qed.

Definition surj (S T : eqType) (S' : set S) (T' : set T) (f : S -> T) := 
  forall x', T' x' -> exists x, S' x /\ x' = f x.

(* -------------------------------------------------------------------------- *)
(*  Logic                                                                     *)
(* -------------------------------------------------------------------------- *)

(** *** Logic *)

Section Logic.

Variable U : eqType.

Lemma antsE : forall P Q R, P -> (Q -> R) -> ((P -> Q) -> R).
Proof. auto. Qed.

Lemma neq_true : forall b, (b != true) = (b == false).
Proof. by case. Qed.

Lemma neq_false : forall b, (b != false) = (b == true).
Proof. by case. Qed.

Lemma eq_trueE : forall b, (b = true) = b.
Proof. done. Qed.

Lemma eqfnP : forall p, p = false <-> ~ p.
Proof. move=> p; split; first by move=> ->. move/negP => H. by apply: negbET. Qed.

Lemma neq_sym : forall x y : U, (x != y) = (y != x).
Proof.
 (* {{{ *)

move=> x y.
apply/idP/idP.
  case H : (y == x).
    move/eqP.
    rewrite eq_sym in H.
    move/eqP: H => H.
    firstorder.
  firstorder.
move/eqP => H.
apply/eqP.
auto.

 (* }}} *)
Qed.

Lemma neq_refl : forall x : U,  (x != x) = false.
Proof.
 (* {{{ *)
move=> x.
apply/negP; rewrite eq_refl.
by apply/negP.
 (* }}} *)
Qed.

End Logic.

(* -------------------------------------------------------------------------- *)
(*  Natural Numbers                                                           *)
(* -------------------------------------------------------------------------- *)

(** *** Natural numbers *)

Section Nat.

Lemma ltnSS : forall n m, (S n < S m) = (n < m).
Proof. by elim => [|n IH] [|m]. Qed.

Lemma leqSS : forall n m, (S n <= S m)%N = (n <= m)%N.
Proof. by elim => [|n IH] [|m]. Qed.

(** Max *)

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

(** Complete induction *)
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

Definition divides n m := exists n', n * n' = m.

Fixpoint smallest_aux (P : nat -> bool) (m n : nat) {struct n} : nat := 
  match n with 
    | O => m
    | S n' => let m' := m - n in if P m' then m' else @smallest_aux P m n'
  end.

Definition smallest P n := smallest_aux P n n.

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

(** Well ordering *)
Fixpoint find_first (s : set nat_eqType) (w : nat_eqType) (ctr : nat) (n : nat) {struct ctr} :=
  match ctr with 
    | O => n
    | S ctr' => if s w then w else find_first s (S w) ctr' n
  end.

Lemma find_first_lt : forall ctr (s : set nat_eqType) i n, s n -> i + ctr = n -> find_first s i ctr n <= n.
Proof.
 (* {{{ *)
elim => [|ctr IH] s i n Hm1 Hm2 //=.
case H : (s i) => //=.
  by rewrite -Hm2 leq_addr.
apply: IH => //.
by rewrite -Hm2 addSnnS.
 (* }}} *)
Qed.

Lemma nat_wo : forall (s : set nat_eqType) n, 
  s n -> exists a, s a /\ forall m, s m -> a <= m.
Proof.
 (* {{{ *)
move=> s n Hn.
exists (find_first s 0 n n). 
split.
  suffices: forall ctr i, i <= n -> n - i = ctr -> s (find_first s i ctr n).
    apply => //.
    by rewrite subn0.
  elim => [|ctr Hctr] //=.
  move=> i Hi1 Hi2.
  have Hi : i < n.
    rewrite leq_eqVlt in Hi1.
    move/orP: Hi1 => [|] => //.
    move/eqP => H1.
    by rewrite H1 subnn in Hi2.
  case H : (s i) => //=.
  apply Hctr => //.
  rewrite (ltn_subS Hi) in Hi2.
  apply/eqP.
  by rewrite -eqSS; apply/eqP.
suffices H : forall d i m, i <= m -> i <= n -> d = n - i -> s m -> find_first s i d n <= m.
  move=> m Hm.
  apply: H => //.
  by rewrite subn0.
elim => [|d IH] i m Him Hin Hd Hm /=.
  move/eqP: Hd.
  rewrite eq_sym eqn_sub0 => Hd.
  move/andP: (conj Hin Hd).
  rewrite -eqn_leq.
  by move/eqP => <-.
rewrite leq_eqVlt in Him.
move/orP:Him => [|] //.
  move/eqP => Him.
  by rewrite Him Hm //.
move=> Him.
case: (s i) => //=.
  by rewrite leq_eqVlt Him orbT.
rewrite leq_eqVlt in Hin.
move/orP: Hin => [|] //.
  move/eqP => H.
  by rewrite H subnn in Hd.
move=> Hin.
apply: IH => //.
rewrite (ltn_subS Hin) in Hd.
apply/eqP.
by rewrite -eqSS; apply/eqP.
 (* }}} *)
Qed.
  
End Nat.

Notation "x |` y" := (divides x y) (at level 55) : dnat_scope.

(* -------------------------------------------------------------------------- *)
(*  Sequences                                                                 *)
(* -------------------------------------------------------------------------- *)

(** *** Sequences *)

Open Scope dnat_scope.

Section Seq_.

Variable d d' d'' : eqType.
Variable R : Type.

Lemma sub_nil : forall x i, sub (x : d) seq0 i = x.
Proof. by move=> x [| i]. Qed.

Lemma size0 : forall s : seq d, (size s == 0) = (s == seq0).
Proof. by elim. Qed.

Fixpoint foldrn_aux (f : nat -> d -> R -> R) (b : R) (s : seq d) (n : nat) {struct s} : R :=
  match s with
    | seq0 => b
    | Adds h t => f n h (foldrn_aux f b t (S n))
  end.

Definition foldrn f b s := @foldrn_aux f b s O.

Fixpoint chop_aux (l : seq d) (n : nat) (c : nat) {struct c} : seq (seq_eqType d) := 
  match l, n, c with
    | seq0, _, _ => seq0 
    | _, O, _ => seq0 
    | _, _, O => seq0
    | _, _, S c' => 
      if c == size l then Adds (take n l) (chop_aux (drop n l) n c') 
      else chop_aux l n c'
  end.

Definition chop l n := chop_aux l n (size l).

Lemma chop0 : forall n, chop seq0 n = seq0. 
Proof. by elim. Qed.

Lemma chop0' : forall s, chop s 0 = seq0. 
Proof. by elim. Qed.

Definition concat (s : seq (seq_eqType d)) := foldr cat seq0 s.
  
Lemma size_concat : forall (s : seq (seq_eqType d)), size (concat s) = natsum (maps size s).
Proof. by rewrite /concat /natsum; elim=> [|x s IH] => //=; rewrite size_cat IH. Qed.

Lemma chop_aux0 : forall n c, chop_aux seq0 n c = seq0.
Proof. by move=> [|n] [|c]. Qed.

Lemma chop_aux_oversize : forall l n c, 
  size l <= n -> size l <= c -> chop_aux l n c = Seq l.
Proof. Admitted.

Lemma chop_oversize : forall l n, size l <= n -> chop l n = Seq l.
Proof. Admitted.

Lemma adds_inj : forall (x:d) s1 s2, Adds x s1 = Adds x s2 -> s1 = s2.
Proof. by move=> x s1 s2 [H]. Qed.

End Seq_.

Section Seq1.

Variable d d' d'' : eqType.
Variable R : Type.

Lemma chop_aux0' : forall (l:seq d) c, chop_aux l 0 c = seq0.
Proof. by move=> [|x l] [|c]. Qed.

Lemma chop_aux0'' : forall (l:seq d) n, chop_aux l n 0 = seq0.
Proof. by move=> [|x l] [|c]. Qed.
 

Lemma chop_terminates : forall m (l : seq d) n, 
  size l <= m -> chop_aux l n m = chop_aux l n (size l).
Proof.
 (* {{{ *)
elim=> [|m IH] l n.
 rewrite leqn0.
 rewrite size0.
 move/eqP=> ->.
 by rewrite !chop_aux0.
move=> H.
case: l H => [|x l] H.
  by rewrite chop_aux0.
case: n => [|n].
  by rewrite chop_aux0'.
rewrite leq_eqVlt in H.
move/orP: H => [|] H.
  by move/eqP: H => ->.
set l' := Adds x l.
rewrite {3}[l']lock.
rewrite /= eqSS.
case Hm : (_ == _).
  move/eqP: Hm => Hm.
  by rewrite Hm /= ltnn in H.
by rewrite -lock IH //.
 (* }}} *)
Qed.

Lemma chopP : forall (l : seq d) n, 
  l <> seq0 -> n <> 0 -> chop l n = Adds (take n l) (chop (drop n l) n).
Proof.
 (* {{{ *)
elim => [|x l IH] [|n] //=.
move=> _ _.
rewrite /chop /= in IH *.
rewrite eq_refl.
congr Adds.
by rewrite chop_terminates // size_drop leq_subr.
 (* }}} *)
Qed.

Lemma chop_adds : forall x (l : seq d) n, 
  chop (Adds x l) (S n) = Adds (Adds x (take n l)) (chop (drop n l) (S n)).
Proof. move=> x l n. by apply: chopP. Qed.

Lemma size_chop : forall (s1 s2 : seq d) n,
  size s1 <= size s2 -> size (chop s1 n) <= size (chop s2 n).
Proof.
 (* {{{ *)
move=> s1.
elim: {s1} (S (size s1)) {-2}s1 (ltnSn (size s1)) => [|z IH] [|x s1] Hs1 [|y s2] [|n] H //=.
rewrite !chop_adds /=.
rewrite /= leqSS in H.
rewrite /= leqSS in Hs1.
rewrite leqSS.
have H' : size (drop n s1) < z.
  rewrite size_drop.
  by apply: ltn_sub.
apply: (IH _ H' _ (S n)).
rewrite !size_drop.
by apply: leq_sub2.
 (* }}} *)
Qed.

Lemma chop_cat : forall (l1 l2 : seq d),
  0 < size l1 -> 
  chop (cat l1 l2) (size l1) = Adds l1 (chop l2 (size l1)).
Proof.
 (* {{{ *)
elim=> [|x l1 IH] [|y l2] //= _.
  by rewrite chop_adds /= cats0 chop0 take_oversize ?leqnn // drop_oversize ?leqnn //. 
by rewrite chop_adds take_cat ltnn subnn take0 cats0 drop_cat ltnn subnn drop0.
 (* }}} *)
Qed.

Lemma chop_concat : forall (s:seq (seq_eqType d)) n, 
  O < n -> all (fun x => size x == n) s -> chop (concat s) n = s.
Proof.
 (* {{{ *)
elim=> [|x s IH] [|n] //= _.
move/andP=> [H1 H2].
rewrite eq_sym in H1.
move/eqP: H1 => H1.
rewrite H1 chop_cat; last by rewrite -H1.
congr Adds.
by rewrite IH => //; rewrite -H1.
 (* }}} *)
Qed.

Fixpoint maps2 (f : d -> d' -> d'') (s : seq d) (t : seq d') {struct s} : seq d'' :=
  match s, t with
    | Adds s s', Adds t t' => Adds (f s t) (maps2 f s' t')
    | _,_ => seq0
  end.

Lemma maps20 : forall f s, maps2 f s seq0 = seq0. Proof. by move=> f; case. Qed. 

End Seq1.

Section Seq2.

Variable d : eqType.

End Seq2.

Section Seq3.

Variable d : eqType.

Lemma take_all : forall P (l:seq d) n, all P l -> all P (take n l).
Proof.
 (* {{{ *)
move=> P.
elim=> [|x l IH] [|n] //=.
move/andP => [-> H] /=.
by apply: IH.
 (* }}} *)
Qed.

Lemma drop_all : forall P (l:seq d) n, all P l -> all P (drop n l).
Proof.
 (* {{{ *)
move=> P.
elim=> [|x l IH] [|n] //=.
move/andP => [H1 H2] /=.
by apply: IH.
 (* }}} *)
Qed.

Lemma all_chop : forall P (l:seq d) n, 0 < n -> all P l = all (all P) (chop l n).
Proof.
 (* {{{ *)

move=> P l.
elim: {l}(S (size l)) {-2}l (ltnSn (size l)) => [|z IH] [|x l] Hl [|n] Hn //=.
rewrite /= ltnSS in Hl.
apply/idP/idP.
  move/andP => [Hx Hl'].
  rewrite chop_adds /= Hx /= take_all //=.
  have H : size (drop n l) < z.
    rewrite size_drop.
    apply: (@leq_trans (S (size l))) => //.
    by rewrite leqSS leq_subr.
  move: (IH _ H (S n) (ltn0Sn _)) => <-.
  by apply: drop_all.
rewrite chop_adds /=.
rewrite -andbA.
move/and3P=> [H2 H1 H3].
rewrite H2 /=.
rewrite -(cat_take_drop n l) all_cat H1 /=.
have H : size (drop n l) < z.
  rewrite size_drop.
  apply: (@leq_trans (S (size l))) => //.
  by rewrite leqSS leq_subr.
by move: (IH _ H (S n) (ltn0Sn _)) => ->.

 (* }}} *)
Qed.

Lemma chop_size_leq : forall (l:seq d) n, all (fun x => size x <= n) (chop l n).
Proof.
 (* {{{ *)
move=> l.
elim: {l}(S (size l)) {-2}l (ltnSn (size l)) => [|z IH] [|x l] Hz [|n] //=.
rewrite /= ltnSS in Hz.
rewrite chop_adds /=.
rewrite size_take.
case H : (n < _) => /=.
  rewrite ltnSn /=.
  apply: IH.
  rewrite size_drop.
  by apply: ltn_sub.
apply/andP; split.
  move/negbT: H => H.
  move: leqNgt.
  rewrite -leqNgt in H.
  by rewrite leqSS.
apply: IH.
rewrite size_drop.
by apply: ltn_sub.
 (* }}} *)
Qed.

Lemma chop_seqn : forall vs ws : seq d, 
  ws <> seq0 -> size vs = size (chop (concat (seqn (size vs) ws)) (size ws)).
Proof.
 (* {{{ *)
elim=> [|v vs IH] [|w ws] //= _.
rewrite chop_adds /=.
rewrite drop_cat ltnn subnn /= drop0.
have Hw : Adds w ws <> seq0 by done.
congr S.
by move: (IH (Adds w ws) Hw).
 (* }}} *)
Qed.

Lemma drop_ind : forall v (vs:seq d) i, vs v -> head i (drop (index v vs) vs) = v.
Proof.
 (* {{{ *)
move=> v.
elim=> [|w vs IH] i Hv => //=.
case H : (_ == _).
  by move/eqP: H.
rewrite IH => //.
rewrite /= /setU1 in Hv.
move/orP: Hv => [|] //.
by rewrite eq_sym H.
 (* }}} *)
Qed.

Lemma rot_seq0 : forall n, rot n (seq0:seq d) = seq0.
Proof. by elim. Qed.

Lemma rot_drop_take : forall (v:seq d) k, rot k v = cat (drop k v) (take k v).
Proof. by elim=> [|v vs IH] [|k]. Qed.

Lemma drop_seq0 : forall n, drop n seq0 = (seq0:seq d).
Proof. by elim. Qed.

Lemma drop_behead : forall (fs:seq d) n, drop (S n) fs = behead (drop n fs).
Proof.  by elim => [|f fs IH] [|n] //=; rewrite drop0. Qed.

Lemma drop_sub0 : forall l n (i:d), sub i l n = head i (drop n l).
Proof.  by elim=> [|x l IH] [|n] i //=. Qed.

Lemma has_rev : forall p (s: seq d), has p s = has p (rev s).
Proof.
 (* {{{ *)
move=> p.
elim=> [|x s IH] //=.
by rewrite rev_adds has_add_last IH.
 (* }}} *)
Qed.

Lemma seqn0 : forall x:d, seqn O x = seq0.
Proof. done. Qed.

Lemma all_seqn : forall P n (x:d) , O < n -> all P (seqn n x) = P x.
Proof.
 (* {{{ *)
move=> P.
elim=> [|n IH] x //= _.
apply/idP/idP.
  by move/andP => [H1 H2].
move=> H.
rewrite H /=.
case: n IH => [|n] IH //.
by rewrite IH.
 (* }}} *)
Qed.

Lemma dropS : forall fs n (i:d), n < size fs -> 
  drop n fs = Adds (sub i fs n) (drop (S n) fs).
Proof.
 (* {{{ *)
elim=> [|f fs IH] [|n] i Hi //=.
  by rewrite drop0.
by rewrite -IH.
 (* }}} *)
Qed.

Lemma all_refl : forall s : seq d, all s s.
Proof. by move=>s; apply/allP. Qed.

Definition pop (l : seq d) n := cat (take n l) (drop (S n) l).

Lemma pop0 : forall f fs, pop (Adds f fs) O = fs.
Proof.  by move=> f fs; rewrite /pop /= drop0. Qed.

Lemma pop_size : forall l n, n < size l -> size (pop l n) = pred (size l).
Proof.
 (* {{{ *)
elim=> [|f fs IH] [|n] //=.
  by rewrite pop0.
rewrite ltnSS.
rewrite /pop in IH.
case: fs IH => [|x fs] IH //.
by move/IH => -> /=.
 (* }}} *)
Qed.

Lemma pop_all : forall (l:seq d) n, all l (pop l n).
Proof.
 (* {{{ *)
move=> l n.
apply/allP => x.
rewrite /pop.
rewrite mem_cat /setU.
move/orP => [|].
  exact: mem_take.
exact: mem_drop.
 (* }}} *)
Qed.

Lemma take_take : forall (v:seq d) n m, n <= m -> take n (take m v) = take n v.
Proof.
 (* {{{ *)
elim=> [|v vs IH] [|n] [|m] Hn => //=.
congr Adds.
by apply: IH.
 (* }}} *)
Qed.

Lemma subset_cat : forall s t : seq d, sub_set s (cat s t).
Proof. by move=> s t x Hx; rewrite mem_cat /setU Hx. Qed.

Lemma subset_cat2 : forall s1 s2 t1 t2 : seq d, sub_set s1 s2 -> sub_set t1 t2 -> sub_set (cat s1 t1) (cat s2 t2).
Proof.
 (* {{{ *)
move=> s1 t1 s2 t2 H1 H2 x.
rewrite !mem_cat /setU.
move/orP => [|] H.
  by move/H1: H => ->.
by move/H2: H => ->; rewrite orbT.
 (* }}} *)
Qed.

Lemma adds_subset : forall (s:seq d) x, sub_set s (Adds x s).
Proof.
 (* {{{ *)
elim => [|y s IH] x //=.
move=> k.
move/orP => [|].
  move/eqP => ->.
  rewrite /setU1.
  apply/or3P.
  by constructor 2.
move=> H.
rewrite /setU1.
apply/or3P.
by constructor 3.
 (* }}} *)
Qed.

Lemma seqn_mem : forall (x y : d) n, O < n -> seqn n x y -> y = x.
Proof.
 (* {{{ *)
move=> x y.
elim => [|n IH] Hn //=.
case H : (n == O).
  move/eqP: H => ->.
  move/orP => [|] //=.
  by move/eqP => ->.
move/neq0_lt0n: H.
move/IH => IH'.
move/orP => [|] //.
by move/eqP => ->.
 (* }}} *)
Qed.

End Seq3.

(* -------------------------------------------------------------------------- *)
(*  eqtypes                                                                   *)
(* -------------------------------------------------------------------------- *)

(** *** Eqtypes *)

Section Eqtype.

Variable d : eqType.

Definition empty := fun x : d => false.

Lemma subset_all : forall (s1 s2 : set d) l, sub_set s1 s2 -> all s1 l -> all s2 l.
Proof.
 (* {{{ *)
move=> s1 s2 l Hs.
move: l.
elim=> [|h t IH] //=.
move/andP => [H1 H2].
apply/andP; split; auto.
 (* }}} *)
Qed.

Lemma subset_trans : forall s1 s2 s3 : set d, sub_set s1 s2 -> sub_set s2 s3 -> sub_set s1 s3.
Proof. by intros => x; auto. Qed.

Lemma subset_refl : forall s : set d, sub_set s s.
Proof. by move=> s x. Qed.

Lemma subset0 : forall s : set d, sub_set seq0 s.
Proof. by move=> s x. Qed.

Lemma all_mem : forall P (s:seq d) x, all P s -> s x -> P x.
Proof.
 (* {{{ *)
move=> P.
elim=> [|y s IH] x //=.
move/andP=> [H1 H2].
move/orP => [|]; auto.
by move/eqP => <-.
 (* }}} *)
Qed.

Lemma subset_adds : forall (x:d) s w, sub_set (Adds x s) w -> sub_set s w.
Proof.
 (* {{{ *)
move=> x s w Hw k Hk.
apply: Hw => /=.
by rewrite /setU1 Hk orbT.
 (* }}} *)
Qed.

Lemma sub_mem : forall (s : seq d) (t: set d) i n, t i -> sub_set s t -> t (sub i s n).
Proof.
 (* {{{ *)
elim=> [|x s IH] t i [|n] Hi Ht => //=.
  apply: Ht => /=.
  exact: setU11.
apply: IH => //.
by apply: subset_adds; eauto.
 (* }}} *)
Qed.

Lemma index_not : forall (s:seq d) x, ~~ (s x) -> index x s = size s.
Proof.
 (* {{{ *)
elim=> [|y s IH] x Hx //=.
case H : (_ == _).
  move/eqP: H => H.
  by rewrite H /= setU11 in Hx.
congr S.
apply: IH.
rewrite /= /setU1 in Hx.
by move/norP: Hx; firstorder.
 (* }}} *)
Qed.

Lemma subset_addsn : forall s t (x:d), ~~ (s x) -> sub_set s (Adds x t) -> sub_set s t.
Proof.
 (* {{{ *)
move=> s t x Hx Ht k Hk.
move: (Ht k Hk) => /=.
move/orP => [|]; auto.
move/eqP => H.
rewrite -H in Hk.
by move/negP: Hx; firstorder.
 (* }}} *)
Qed.

Lemma all_subset : forall P (vs ws : seq d), sub_set ws vs -> all P vs -> all P ws.
Proof.
 (* {{{ *)
move=> P vs.
elim=> [|w ws IH] H1 H2 //=.
move/subset_adds: (H1) => H1'.
apply/andP;split; auto.
move=> {IH H1'}.
move: {H1}(H1 w).
apply: antsE => //=.
  by rewrite /setU1 eq_refl.
move=> H.
elim: vs H H2 => [|v vs IH] //=.
rewrite /setU1.
move/orP=> [|].
  move/eqP=> ->.
  by move/andP => [-> _].
move=> H.
move/andP=> [_ H']; auto.
 (* }}} *)
Qed.

Lemma subset_setU1 : forall s (t:set d) x, sub_set (setU1 x s) t -> sub_set s t.
Proof.
 (* {{{ *)
move=> s t x Hx y Hy.
move: (Hx y).
apply.
rewrite /setU1.
by case H : (_ == _).
 (* }}} *)
Qed.

Hint Resolve subset_setU1.

Lemma seq_subset : forall vs ws : seq d, sub_set vs ws <-> all ws vs.
Proof.
 (* {{{ *)
move=> vs ws; split.
  move=> H.
  elim: vs H => [|v vs IH] //= H.
  apply/andP;split;eauto.
  apply: (H v).
  by rewrite /setU1 eq_refl.
elim: vs => [|v vs IH] //=.
  move=> _;exact: subset0.
move/andP=> [H1 H2].
move=> x.
move/orP=> [|] //.
  by move/eqP=> <-.
move=> H.
by apply: (IH H2 x).
 (* }}} *)
Qed.

Lemma subset_catL : forall r s : seq d, sub_set r (cat r s).
Proof.
 (* {{{ *)
elim => [|r rs IH] s //=.
move=> x.
move/orP => [|].
  move/eqP => ->.
  exact: setU11.
move/IH => H.
by apply/orP; right.
 (* }}} *)
Qed.

Lemma subset_catR : forall r s : seq d, sub_set s (cat r s).
Proof.
 (* {{{ *)
elim => [|r rs IH] s //=.
move=> x.
move/IH => H.
by apply/orP; right.
 (* }}} *)
Qed.

Definition inter (s1 s2 : set d) := fun x => s1 x && s2 x.

End Eqtype.

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
