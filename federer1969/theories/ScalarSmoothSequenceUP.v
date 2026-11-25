(** Federer (1969), 3.1.11, pp. 220–223:
    successive real-source derivative coefficients are
    specified by exact ordinary differential laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import NormDifferentialUP NormHigherCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_scalar_smooth_derivative_sequence]:
    successive ordinary derivatives, in the
    real-source convention of Federer 3.1.11,
    p. 220. This predicate records
    proved differential graphs at every order,
    rather than postulating differentiability. *)
Definition is_scalar_smooth_derivative_sequence (R : realType)
    (f : R->R) (F : nat->R->R) : Prop :=
  (forall x, F 0%N x=f x) /\
  forall k a, has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) (fun _=>True) (F k) a
    (@scalar_coefficient_linear_map R R^o (F k.+1 a)).
