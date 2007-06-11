Require Import ssr.
Require Import lib.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

(** *** Withzero. *)

(* We include a type for a set with a syntactic zero element.
   While this is isomorphic to the option type, having a separate type
   makes notations cleaner and makes our intention more clear.  *)

Section Withzero.

Variable d : eqType.

Inductive withzero (s : Type) : Type := Zero | Nz (x : s).

(* Definition extract x := match x with Nz y => y | _ => t end.  *)

Lemma Nz_inj : forall x y : d, Nz x = Nz y -> x = y.
Proof. congruence. Qed. 

Definition eqwithzero (x y : withzero d) := 
  match x,y with
    | Zero, Zero => true 
    | Nz x, Nz y => x == y
    | _,_ => false 
  end.

Lemma eqwithzeroPx : reflect_eq eqwithzero.
Proof.
 (* {{{ *)
move=> [|x] [|y]; try by [constructor].
case H : (x == y).
  rewrite /= H (eqP H).
  by left.
rewrite /= H.
right.
move=> [H']; by rewrite H' eq_refl in H.
 (* }}} *)
Qed.

Canonical Structure withzeroData := EqType eqwithzeroPx.

End Withzero.

Implicit Arguments Zero [s].
