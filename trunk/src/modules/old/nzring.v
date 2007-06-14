Require Import ssr.
Require Import lib.
Require Import ring_sig.
Require Import ring.
Require Import withzero.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

Module Nzring : RING.

Section Ax.

Variable d' : eqType.
Notation d := (withzeroData d').

Notation "0" := (@Zero _).

Definition lift_opp (f : d' -> d') x :=
  match x with
    | Zero => 0
    | Nz x => Nz (f x)
  end.

Definition lift_add (add : d' -> d' -> d) x y := 
  match x, y with 
    | Zero, _ => y
    | _, Zero => x
    | Nz x, Nz y => add x y
  end.

Definition lift_addL (f : d' -> d' -> d) x y := 
  match x with
    | Zero => Nz y
    | Nz x => f x y
  end.

Definition lift_addR (f : d' -> d' -> d) x y := 
  match y with
    | Zero => Nz x
    | Nz y => f x y
  end.

Definition lift_mul (mul : d' -> d' -> d) x y := 
  match x, y with 
    | Nz x, Nz y => mul x y
    | _, _ => 0
  end.

Definition lift_mulL (f : d' -> d' -> d) x y :=
  match x with
    | Zero => 0
    | Nz x => f x y
  end.

Definition lift_mulR (f : d' -> d' -> d) x y := 
  match y with
    | Zero => 0
    | Nz y => f x y
  end.

Variable add_nz : d' -> d' -> d.
Variable mul_nz : d' -> d' -> d.
Variable opp_nz : d' -> d'.
Variable one_nz : d'.

Notation "x1 + x2" := (lift_add add_nz x1 x2).
Notation "x1 * x2" := (lift_mul mul_nz x1 x2).
Notation "- x" := (lift_opp opp_nz x).
Notation "1" := (Nz one_nz).

Structure ring_axioms : Type := Ring_axioms {
  oppL' : forall x : d,  - x + x = 0;
  addA': forall x1 x2 x3 : d, x1 + (x2 + x3) = (x1 + x2) + x3;   
  addC': forall x1 x2 : d, x1 + x2 = x2 + x1;
  mul1r' : forall x, 1 * x = x;
  mulr1' : forall x : d, x * 1 = x;
  mulA' : forall x1 x2 x3 : d, x1 * (x2 * x3) = x1 * x2 * x3;
  distPM' : forall x1 x2 x3 : d, (x1 + x2) * x3 = x1 * x3 + x2 * x3;
  distMP' : forall x1 x2 x3 : d, x1 * (x2 + x3) = x1 * x2 + x1 * x3;
  mulC' : forall x1 x2 : d, x1 * x2 = x2 * x1
}.

Definition integ' := forall x1 x2 : d', (Nz x1) * (Nz x2) <> 0.

End Ax.

(* -------------------------------------------------------------------------- *)
(*  Structure                                                                 *)
(* -------------------------------------------------------------------------- *)

Structure nzring : Type := Nzring {
  base' : eqType;
  add_nz : base' -> base' -> withzero base';
  opp_nz : base' -> base';
  one_nz : base';
  mul_nz : base' -> base' -> withzero base';
  axioms : ring_axioms add_nz mul_nz opp_nz one_nz
}.

Definition base r := withzeroData (base' r).

Coercion base : nzring >-> eqType.

Definition mulr (r : nzring) (x y : r) : r := lift_mul (@mul_nz r) x y.
Definition addr (r : nzring) (x y : r) : r := lift_add (@add_nz r) x y.
Definition oppr (r : nzring) (x : r) : r := lift_opp (@opp_nz r) x.
Definition oner (r : nzring) : r := Nz (one_nz r).

Implicit Arguments oner [r].

Structure nzidom : Type := Nz_idom {
  b_idom :> nzring;
  nz_integ : integ' (@mul_nz b_idom)}.

Structure nzfield : Type := Nz_field {
  fbase :> nzidom;
  inv_nz : base' fbase -> base' fbase;
  unitPL : forall x : base' fbase, mul_nz (inv_nz x) x = oner}.

Definition inv (F : nzfield) (x : F) := if x is Nz x' then Nz(inv_nz x') else Zero.

(* --------------------------------  Axioms  -------------------------------- *)

Section Axioms.

Variable R : nzring.

Notation "x1 + x2" := (addr x1 x2).
Notation "x1 * x2" := (mulr x1 x2).
Notation "- x" := (oppr x).
Notation "x - y" := (x + (- y)).
Notation "1" := oner.
Notation "0" := (@Zero _).

Lemma nzaddC : forall x y : R, x + y = y + x.
Proof. exact: addC' (axioms R). Qed.

Lemma nzaddA : forall x y z : R, x + (y + z) = (x + y) + z. 
Proof. exact: addA' (axioms R). Qed.

Lemma nzaddr0 : forall x: R, x + 0 = x.
Proof. by elim. Qed.

Lemma nzoppL : forall x : R, -x + x = 0.
Proof. exact: oppL' (axioms R). Qed. 

Lemma nzmulA : forall x y z : R, x * (y * z) = (x * y) * z. 
Proof. exact: mulA' (axioms R). Qed.

Lemma nzdistPM : forall x1 x2 x3 : R, (x1 + x2) * x3 = (x1 * x3) + (x2 * x3).
Proof.  exact: distPM' (axioms R). Qed.

Lemma nzdistMP : forall x1 x2 x3 : R, x1 * (x2 + x3) = (x1 * x2) + (x1 * x3).
Proof. exact: distMP' (axioms R). Qed.

Lemma nzmul1r : forall x : R, 1 * x = x. 
Proof. exact: mul1r' (axioms R). Qed.

Lemma nzmulr1 : forall x : R, x * 1 = x.
Proof. exact: mulr1' (axioms R). Qed.

Lemma nzmulC : forall x y : R, x * y = y * x.
Proof. exact: mulC' (axioms R). Qed.

Definition nzring_axioms := ring.Ring_axioms nzaddC nzaddA nzaddr0 nzoppL nzmulA nzdistPM nzdistMP nzmul1r nzmulr1 nzmulC.

Canonical Structure ring_of_nzring := Ring.Ring nzring_axioms.

Lemma nzP : 1 <> 0 :> R. Proof. done. Qed.

End Axioms.

Print nzring.

Definition ring := nzring.

Definition zeror (r : withzero ) := @Zero r.
Check zeror.
End Nzring.