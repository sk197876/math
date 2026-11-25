(** Federer (1969), 4.1.14, p. 370: actual differentials of the
    chosen smooth approximants obey their sharp Lipschitz bound.
    Reuse the directional differential bound of 3.1.1, p. 209,
    and the original operator norm of 1.7.6, pp. 33–34. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness FiniteCoordinates RealNormUP NormDifferentialUP
  NormDifferentialLocal NormDifferentialLipschitzBound NormRegularity
  HomSpaceTopology EuclideanHomOperator CurrentMapDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [smooth_global_lipschitz_differential_restriction]:
    the common actual Dg_i bound in Federer 4.1.14, p. 370.
    The derivative is derived from the smooth map. Restricting to Z
    keeps the original graph value and introduces no derivative witness. *)
Theorem smooth_global_lipschitz_differential_restriction (R:realType) n nu
    (g:R_n R n->R_n R nu) L (Z:set (R_n R n)):
  0<=L ->
  norm_class_all_orders
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R nu)) setT g ->
  (forall x y,inner_norm (@euclidean_inner_productP R nu) (g x-g y)<=
    L*inner_norm (@euclidean_inner_productP R n) (x-y)) ->
  (forall x,Z x->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R n)) Z x) ->
  forall x,Z x->
    @euclidean_operator_norm R n nu (@current_map_differential R n nu Z g x)<=L.
Proof.
move=>hL hSmooth hBound hZ x hx.
have hActual:=@current_map_differential_actual R n nu setT g hSmooth x Logic.I.
have hRestricted:=@norm_differential_restrict R (R_n R n) (R_n R nu)
  (inner_norm (@euclidean_inner_productP R n))
  (inner_norm (@euclidean_inner_productP R nu)) setT Z g x
  (@current_map_differential R n nu setT g x) (fun _ _=>Logic.I) (hZ x hx) hActual.
rewrite (@current_map_differential_unique R n nu Z g x _ hRestricted).
apply:hom_operator_norm_least;first exact:hL.
exact:(@norm_differential_global_lipschitz_bound R (R_n R n) (R_n R nu)
  (inner_norm (@euclidean_inner_productP R n))
  (inner_norm (@euclidean_inner_productP R nu))
  (inner_norm_real_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R nu))
  g x (@current_map_differential R n nu setT g x) L hActual hBound).
Qed.
