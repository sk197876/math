(** Federer (1969), 4.1.12, p. 368: T equals
    its scalar contraction when the scalar equals one
    near spt T. This follows from the original
    near-support test agreement and pointwise exterior
    product, without a measure-representation premise. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero AlternatingProduct
  ZeroFormScalarProduct CurrentSpaces CurrentContraction CurrentTestFormProduct CurrentEvaluation
  CurrentTestNearSupportAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentScalarSupportPlateau.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.

(** Source for [current_scalar_support_plateau]:
    if spt T is contained in an open set W
    where gamma is one, T=T contracted gamma,
    the exact localisation identity of Federer
    4.1.12, p. 368, for arbitrary currents. *)
Theorem current_scalar_support_plateau (T:@current_space R h2 n U hU m)
    (gamma:@current_smooth_space R h2 n U hU 0%N) (W:set X):
  @open (real_norm_metric_space hNX) W->
  @current_support R h2 n U hU m T `<=` W->W `<=` U->
  (forall x,W x->@current_smooth_value R h2 n U hU 0%N gamma x=@zero_form R X R^o 1)->
  T=@current_contraction R h2 n 0%N m U hU gamma T.
Proof.
move=>hW hSW hWU hOne;apply:current_values_extensional=>psi.
rewrite current_contraction_evaluation.
apply:(@current_test_near_support_values_equal R h2 n m U hU T psi
  (@current_test_form_product R h2 n 0%N m U hU gamma psi) W hW hSW).
move=>x hx.
rewrite (@current_test_form_product_values R h2 n 0%N m U hU gamma psi x (hWU x hx))
  (@hOne x hx) original_zero_form_wedge_scalar scale1r.
by [].
Qed.
End CurrentScalarSupportPlateau.
