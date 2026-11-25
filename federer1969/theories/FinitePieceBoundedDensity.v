(** Federer (1969), 2.5.10, p. 101: local densities for a bounded L1
    functional on the disjoint finite-measure pieces. This interface
    supplies the actual local integrals and a common pointwise bound; no
    implementation of the local density is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureRestriction FunctionLatticeSeminormUP TotalScalarLpUP
  TotalScalarLpFiniteSeminorm LpFunctionalDensityUP RestrictedLoneFunctional BoundedDensityRepresentative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_piece_bounded_functional_density]: supporting
    complete local representation for Federer 2.5.10, p. 101 Zero measure
    and M=0 are allowed. *)
Theorem finite_piece_bounded_functional_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (B : set X) (A : (X -> R) -> R) (M : R) :
  measure_measurable mu B -> mu B < +oo -> (0 <= M)%R ->
  is_linear_functional_on_functions (total_scalar_lp mu 1) A ->
  (forall f, total_scalar_lp mu 1 f -> (`|A f| <= M * finite_total_scalar_lp_norm mu 1 f)%R) ->
  exists k : X -> R, is_lp_functional_density (measure_restrict mu B) 1 +oo
    (restricted_total_lone_functional B A) k /\ forall x, (`|k x| <= M)%R.
Proof.
move=> hB hfin hM hA hb.
have [k [hk hkn]] := @finite_piece_lone_functional_density R X mu hm B A M hB hfin hM hA hb.
exact: (@lp_density_pointwise_bounded_representative R X (measure_restrict mu B)
  (measure_restrict_is_measure hm B) _ k M hM hk hkn).
Qed.
