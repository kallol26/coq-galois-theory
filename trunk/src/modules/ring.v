
Require Import ssr.
Require Import lib.
Require Import withzero.

Set Implicit Arguments. 
Unset Strict Implicit. 
Import Prenex Implicits.

Open Scope dnat_scope.

(* -------------------------------------------------------------------------- *)
(*  Rings                                                                     *)
(* -------------------------------------------------------------------------- *)

Module Ring.
  
  Section Axioms.

    Variable d' : eqType.
    Notation d := (withzeroData d').
    Notation "0" := (@Zero _).

    Definition lift_opp (f:d'->d') x :=
      match x with
        | Zero => 0
        | Nz x => Nz (f x)
      end.

    Definition lift_add (add:d'->d'->d) x y := 
      match x, y with 
        | Zero, _ => y
        | _, Zero => x
        | Nz x, Nz y => add x y
      end.

    Definition lift_mul (mul:d'->d'->d) x y := 
      match x, y with 
        | Nz x, Nz y => mul x y
        | _, _ => 0
      end.

    Variable addr' : d'->d'->d.
    Variable mulr' : d'->d'->d.
    Variable oppr' : d'->d'.
    Variable oner' : d'.

    Notation "x1 + x2" := (lift_add addr' x1 x2).
    Notation "x1 * x2" := (lift_mul mulr' x1 x2).
    Notation "- x" := (lift_opp oppr' x).
    Notation "1" := (Nz oner').

    Structure ring_axioms : Type := Ring_axioms {
      oppL'    : forall x,  - x + x = 0;
      addA'    : forall x1 x2 x3, x1 + (x2 + x3) = (x1 + x2) + x3;   
        addC'    : forall x1 x2, x1 + x2 = x2 + x1;
      mul1r'   : forall x, 1 * x = x;
      mulr1'   : forall x, x * 1 = x;
      mulA'    : forall x1 x2 x3, x1 * (x2 * x3) = x1 * x2 * x3;
      distPM'  : forall x1 x2 x3, (x1 + x2) * x3 = x1 * x3 + x2 * x3;
      distMP'  : forall x1 x2 x3, x1 * (x2 + x3) = x1 * x2 + x1 * x3;
      mulC'    : forall x1 x2, x1 * x2 = x2 * x1
    }.

  End Axioms.

  Structure prering : Type := Ring {
    rbase'    : eqType;
    addr'     : rbase' -> rbase' -> withzero rbase';
    oppr'     : rbase' -> rbase';
    oner'     : rbase';
    mulr'     : rbase' -> rbase' -> withzero rbase';
    axioms    : ring_axioms addr' mulr' oppr' oner'
  }.

  Definition rbase r := withzeroData (rbase' r).
  Coercion rbase : prering >-> eqType.

  Variable r:prering.

  Definition addr (x y:r) := lift_add (@addr' r) x y.
  Definition mulr (x y:r) := lift_mul (@mulr' r) x y.
  Definition oppr (x:r)   := lift_opp (@oppr' r) x.
  Definition oner         := Nz (oner' r).

  Notation "x1 + x2" := (addr x1 x2).
  Notation "x1 * x2" := (mulr x1 x2).
  Notation "- x"     := (oppr x).
  Notation "x - y"   := (x + (- y)).
  Notation "1"       := (oner).
  Notation "0"       := (@Zero _).

  Axiom addC   : forall x y:r, x + y = y + x.
  Axiom addA   : forall x y z:r, x + (y + z) = (x + y) + z. 
  Axiom addr0  : forall x:r, x + 0 = x.
  Axiom oppL   : forall x:r, -x + x = 0.
  Axiom mulA   : forall x y z:r, x * (y * z) = (x * y) * z. 
  Axiom distPM : forall x1 x2 x3:r, (x1 + x2) * x3 = (x1 * x3) + (x2 * x3).
  Axiom distMP : forall x1 x2 x3:r, x1 * (x2 + x3) = (x1 * x2) + (x1 * x3).
  Axiom mul1r  : forall x:r, 1 * x = x. 
  Axiom mulC   : forall x y:r, x * y = y * x.

End Ring.

Notation "x1 + x2" := (Ring.addr x1 x2)         : ring_scope.
Notation "x1 * x2" := (Ring.mulr x1 x2)         : ring_scope.
Notation "- x"     := (Ring.oppr x)             : ring_scope.
Notation "0"       := (@Zero _)            : ring_scope.
Notation "1"       := (Ring.oner _)             : ring_scope.
Notation "x - y"   := (x + Ring.oppr y)         : ring_scope.
Notation addrr   := (fun x y => y + x).
Notation mulrr   := (fun x y => y * x).
