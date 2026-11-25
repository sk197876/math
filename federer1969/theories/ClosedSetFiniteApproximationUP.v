(** Federer (1969), 2.4.19, p. 91: finite-image approximations with values
    in the closed convex set C. These supporting laws use a fixed point of C
    in place of zero. Convexity is unnecessary for approximation itself. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric BorelFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_closed_set_finite_approximation]: supporting abstract
    approximation laws for Federer 2.4.19, p. 91 The pointwise majorant is
    distance to a fixed point in C, rather than distance to zero. *)
Record is_closed_set_finite_approximation (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (C : set (real_norm_metric_space hN))
    (z : V) (a : nat -> real_norm_metric_space hN -> real_norm_metric_space hN) : Prop := {
  (** Source for [closed_set_finite_borel]: measurable approximants supporting
    Federer 2.4.19, p. 91 *)
  closed_set_finite_borel : forall n, is_borel_function (a n);
  (** Source for [closed_set_finite_image]: finite images in the
      approximation step of Federer 2.4.19, p. 91. *)
  closed_set_finite_image : forall n, finite_set (a n @` setT);
  (** Source for [closed_set_finite_range]: values stay in C,
      as required in Federer 2.4.19, p. 91. *)
  closed_set_finite_range : forall n x, C (a n x);
  (** Source for [closed_set_finite_error]: supporting integrable
      error majorant for Federer 2.4.19, p. 91. *)
  closed_set_finite_error : forall n x, C x -> N (x-a n x) <= N (x-z);
  (** Source for [closed_set_finite_converges]: supporting pointwise
    convergence for Federer 2.4.19, p. 91 *)
  closed_set_finite_converges : forall x, C x -> (fun n => a n x) @ \oo --> x
}.
