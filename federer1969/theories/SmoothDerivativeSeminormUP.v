(** Federer (1969), 4.1.1, p. 343: nu^i_K is specified by
    its least nonnegative derivative bound, including K empty.
    This definition does not choose a supremum construction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section SmoothDerivativeSeminormSpecification.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).

(** Source for [is_smooth_derivative_seminorm]: independent
    exact-supremum laws for nu^i_K in Federer 4.1.1, p. 343.
    The nonnegative least-bound formulation assigns zero on an
    empty compact set, as required of a seminorm. *)
Record is_smooth_derivative_seminorm (K:smooth_compact_set hNX U)
    (i:nat) (p:E->R) : Prop := {
  (** Source for [smooth_derivative_seminorm_nonnegative]: the
      derivative seminorm is nonnegative, Federer 4.1.1, p. 343. *)
  smooth_derivative_seminorm_nonnegative : forall f,0<=p f;
  (** Source for [smooth_derivative_seminorm_bound]: nu^i_K
      bounds each original derivative through order i on K,
      Federer 4.1.1, p. 343. *)
  smooth_derivative_seminorm_bound : forall f j,(j<=i)%N ->
    forall x,smooth_compact_carrier K x -> @ZN j (@D j x f)<=p f;
  (** Source for [smooth_derivative_seminorm_least]: nu^i_K
      is the least nonnegative common derivative bound,
      Federer 4.1.1, p. 343. *)
  smooth_derivative_seminorm_least : forall f C,0<=C ->
    (forall j,(j<=i)%N -> forall x,smooth_compact_carrier K x -> @ZN j (@D j x f)<=C) -> p f<=C
}.
End SmoothDerivativeSeminormSpecification.
