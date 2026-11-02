(** Federer (1969), 3.1.11, p. 223: evaluating an
    existing differential in a coordinate direction gives the partial
    derivative on the function's actual domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  NormTaylorLineValues NormIteratedDirectionalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_line]: the implication from
    differentiability to directional differentiability, 3.1.1,
    pp. 209–211, used recursively in Federer 3.1.11,
    p. 223. The interval domain is derived from the differential. *)
Lemma norm_differential_line (R : realType) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : X->Prop) (f : X->Y) a (L : Hom X Y) :
  has_norm_differential NX NY A f a L -> forall v,
    has_norm_line_derivative NY A f a v (L v).
Proof.
move=>hf v; split.
- have [r [hr hA]] := norm_differential_interior hf.
  have [d [hd hb]] := norm_scalar_line_small_increments hNX v hr.
  exists d; split=> // t ht; exact: hA _ (hb t ht).
- exact (norm_differential_directional_limit hNX hNY hf v).
Qed.
