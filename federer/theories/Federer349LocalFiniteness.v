(** Federer (1969), 3.4.9, p. 337:
    the original family of all connected components of
    the difference of two analytic subvarieties is locally
    finite throughout the original open domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness AnalyticVarietyGermUP LocallyFiniteFamilyUP
  AnalyticDifferenceLocalComponents ComponentImageLocalFiniteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_9_local_finiteness]: the complete
    first assertion of 3.4.9, p. 337. Both
    sets retain the original local analytic definition;
    global finite equations are not assumed. *)
Theorem federer_3_4_9_local_finiteness (R:realType) n (U S D:set (R_n R n)):
  let NX:=inner_norm (@euclidean_inner_productP R n) in
  let hNX:=inner_norm_real_norm (@euclidean_inner_productP R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->@is_analytic_set_in R (R_n R n) NX hNX U S ->
  @is_analytic_set_in R (R_n R n) NX hNX U D ->
  @is_locally_finite_family_on T [the choiceType of (set T)] U
    (@connected_component T (S `\` D) @` (S `\` D)) (fun C=>C).
Proof.
move=>NX hNX T hU hS hD.
apply:component_image_locally_finite=>a ha.
exact:(@analytic_difference_local_components R n S D a (hS a ha) (hD a ha)).
Qed.
