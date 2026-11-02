(** Federer (1969), 2.2.15, p. 71: private existence of h_i. The integer
    floor of i*f(x) identifies the unique interval cell. Floor and integer
    arithmetic are existing scalar background from reals; no external
    measurable- or Baire- function approximation theorem is imported. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals.
From Federer Require Import RealIntegerCells RealQuantisationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_quantisation_exists]: existence of the
    cellwise-constant approximant h_i in Federer 2.2.15, p. 71.
    The private floor witness proves the abstract cell and value
    laws; the later sum representation uses only those laws. *)
Theorem real_quantisation_exists (R : realType) (X : Type) (f : X -> R) k :
  exists q : X -> R, is_real_quantisation f q k.
Proof.
exists (fun x => (Num.floor (f x * (k.+1)%:R))%:~R / (k.+1)%:R)=> x.
exists (Num.floor (f x * (k.+1)%:R)); split=> //.
apply: (proj2 (real_integer_cell_scaled f k _ x)); exact: mem_rg1_floor.
Qed.
