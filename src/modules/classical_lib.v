
(** ** A library of useful definitions and theorems. *)

(** We postulate a strongly classical world. *)

Require Import ssr.
Require Import ClassicalEpsilon.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

(** Extensionality *)
Axiom strong_ext : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x), 
  (forall x, f x = g x) -> f = g.

Lemma weak_ext : forall (A B : Type) (f g : A -> B),
  (forall x, f x = g x) -> f = g.
Proof. move=> A B f g H. exact: (@strong_ext A (fun x : A => B) f g H). Qed.

Lemma eta : forall (A B : Type) (s : A -> B), (fun x => s x) = s.
Proof. by move=> A B s; apply: weak_ext. Qed.

(** Classical logic *)
Definition Pb : Prop -> bool.
 (* {{{ *)
move=> P.
case H : (excluded_middle_informative P).
  exact: true.
exact: false.
 (* }}} *)
Defined.

Lemma PbP : forall P, reflect P (Pb P).
Proof.
 (* {{{ *)
move=> P.
case H : (Pb P).
  left; move: H; rewrite /Pb /=.
  by case: (excluded_middle_informative P).
right; move: H; rewrite /Pb /=.
by case: (excluded_middle_informative P).
 (* }}} *)
Qed.

Lemma LEM : forall P : Prop, P \/ ~ P.
Proof. move=> P; move: (PbP P); (case => H; first by left); by right. Qed.

(** Proof Irrelevance *)
Section PI.

Variable A : eqType.
Variable k : A.

Inductive neq_set (s t : set A) (H : s <> t) : Prop := 
  | IL : (exists x, s x && ~~ (t x)) -> neq_set H
  | IR : (exists x, t x && ~~ (s x)) -> neq_set H.

Lemma neq_setP : forall (s t : set A) (H : s <> t), neq_set H.
Proof.
 (* {{{ *)

move=> s t H.
case H1 : (Pb (exists x, s x && negb (t x))); move/PbP : H1; first by left.
move/(not_ex_all_not _ (fun x => _)) => H1.
right; apply: (not_all_not_ex _ (fun x => _)) => H2; elim: H.
apply: weak_ext => x.
move: (H1 x) (H2 x).
case Hs : (s x); first by move/negP; move/negbE2.
by rewrite /= andbT => _; move/negP => Ht; apply/eqP.

 (* }}} *)
Qed.

End PI.

(** *** Consequences *)

(** All types are eqtypes *)

Section EqType.

Variable A : Type.

Definition gen_eq (x y : A) := Pb (x = y).

Lemma gen_ref : reflect_eq gen_eq.
Proof.
 (* {{{ *)
move=> x y.
case H : (gen_eq _ _); first by left; move/PbP: H.
right => H'.
rewrite {}H' /gen_eq in H.
by move/PbP: H.
 (* }}} *)
Qed.

Canonical Structure type_to_eqType := EqType gen_ref.

End EqType.

Notation Ety := type_to_eqType.

(* ----------------------------  prop rewrites  ----------------------------- *)

Section P.

Variable P Q : Prop.

Lemma not_and : Pb (~(P /\ Q)) = Pb (~ P \/ ~ Q).
Proof.
apply/idP/idP; move/PbP.
  move/not_and_or => H.
  by apply/PbP.
move/or_not_and => H.
by apply/PbP.
Qed.

Lemma not_or : Pb (~(P \/ Q)) = Pb (~ P /\ ~ Q).
Proof.
apply/idP/idP; move/PbP.
  move/not_or_and => H.
  by apply/PbP.
move/and_not_or => H.
by apply/PbP.
Qed.

Lemma imp_or : Pb (P -> Q) = Pb (~ P \/ Q).
Proof.
apply/idP/idP; move/PbP.
  move/imply_to_or => H.
  by apply/PbP.
move/or_to_imply => H.
by apply/PbP.
Qed.

Lemma not_not : Pb (~ ~ P) = Pb P.
Proof.
apply/idP/idP; move/PbP.
  move/NNPP => H.
  by apply/PbP.
move=> H.
by apply/PbP => H'.
Qed.

Lemma not_pb : (~~ (Pb P)) = Pb (~ P).
Proof.
move: (LEM P) => [|] H.
move/PbP: (H) => ->.
  by case H' : (Pb (~ P)); first by move/PbP: H'.
move/PbP: (H) => ->.
by case H' : (Pb P); first by move/PbP: H'.
Qed.
  
End P.

(* -------------------------  quantifier rewrites  -------------------------- *)

Section Quant.

Variable A : Type.
Variable P : A -> Prop.

Lemma ex_not : Pb (exists x, P x) = Pb (~ forall x, ~ P x).
Proof.
apply/idP/idP; move/PbP.
  move=> [x Hx].
  apply/PbP.
  by move/(fun f => f x). 
move=> H.
apply/PbP.
by apply: not_all_not_ex.
Qed.

Lemma all_not : Pb (forall x, P x) = Pb (~ exists x, ~ P x).
Proof.
apply/idP/idP; move/PbP.
  move=> H.
  apply/PbP. (*XXX bug here, can't do [x Hx] *)
  move => [x Hx].
  auto.
move/not_ex_not_all => H.
by apply/PbP.
Qed.

End Quant.

(* 
Definition eqseq := type_to_eqType (seq (type_to_eqType R)).
Definition inters (s : eqseq (set d)) := fun x => all s x. 

Definition eqset (S : Type) := type_to_eqType (set (type_to_eqType S)).
Definition interd (s : eqset (set d)) := fun x => Pb(forall h, s h -> h x).

Lemma subset_eq : forall s1 s2 : set d, sub_set s1 s2 -> sub_set s2 s1 -> s1 = s2.
Proof.
 (* {{{ *)
move=> s1 s2 Hs1 Hs2.
apply: weak_ext => x.
case H : (s1 x).
  by move: (Hs1 x H).
case H' : (s2 x) => //.
by move: (Hs2 x H'); rewrite H.
 (* }}} *)
Qed.

Lemma subset_eq0 : forall s : set d, sub_set s seq0 -> (s = seq0).
Proof. 
 (* {{{ *)
move=> s H.
apply: weak_ext => x /=.
apply: negbE.
apply/negP => H'.
by move: (H x H').
 (* }}} *)
Qed.

Definition setmap (d' : eqType) (f : d -> d') (s : set d) : set d' := 
  fun x => Pb (exists t, f t = x).

Lemma all_rotL : forall (fs:seq d) n, all (rot n fs) = all fs.
Proof.
 (* {{{ *)
move=> fs n.
apply: subset_eq => x Hx.
  apply: subset_all; eauto.
  move=> y Hy.
  by rewrite mem_rot in Hy.
apply: subset_all; eauto.
move=> y Hy.
by rewrite mem_rot.
 (* }}} *)
Qed.

Lemma all_rotR : forall (fs:seq d) F n, all F (rot n fs) = all F fs.
Proof.
 (* {{{ *)
move=> fs F' n.
apply/idP/idP => H.
  apply/allP => x Hx.
  move/allP: H.
  apply.
  by rewrite mem_rot.
apply/allP => x Hx.
move/allP: H.
apply.
by rewrite mem_rot in Hx.
 (* }}} *)
Qed.


*) 