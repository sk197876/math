(** Federer (1969), 4.1.24, p. 381: integral
    polyhedral zero-currents depend on finitely many scalar
    point values, and send integer-valued point data
    to integers. These independent finite-action laws
    retain cancellation without assuming that a chosen
    sum has distinct points or positive coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra finmap
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingZero CurrentSpaces SmoothCompactSet VitaliNonmeasurableSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope ring_scope.

Section FiniteIntegerPointActionUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation DT:=(@current_test_space R h2 n U hU 0%N).
Local Notation C:=(@current_space R h2 n U hU 0%N).
Local Notation coeff:=(fun (phi:DT) x=>zero_form_value
  (@current_test_value R h2 n U hU 0%N phi x)).
Local Notation action:=(@current_value R h2 n U hU 0%N).

(** Source for [is_finite_integer_point_action]: independent
    finite point-data and integrality laws for the
    zero-degree assertion of 4.1.24, p. 381.
    Locality in values excludes derivative evaluations. *)
Record is_finite_integer_point_action (H:{fset R_n R n}) (T:C):Prop:={
  (** Source: a finite combination of original zero-simplexes
      depends only on its point values, p. 381. *)
  finite_integer_point_action_locality:forall phi psi:DT,
    (forall x,x\in H->coeff phi x=coeff psi x)->action T phi=action T psi;
  (** Source: its multiplicities are integral, including
      all cancellation and negative multiplicities, p. 381. *)
  finite_integer_point_action_integrality:forall phi:DT,
    (forall x,x\in H->@real_integers R (coeff phi x))->
    @real_integers R (action T phi)
}.

(** Source for [has_finite_integer_point_action]: some original
    finite point set in the exact compact K
    carries these independent action laws, 4.1.24, p. 381. *)
Definition has_finite_integer_point_action
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T:C):Prop:=exists H:{fset R_n R n},
      (forall x,x\in H->smooth_compact_carrier K x) /\is_finite_integer_point_action H T.
End FiniteIntegerPointActionUP.
