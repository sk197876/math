(** Federer (1969), 3.2.48, p. 285: combine the actual
    manifold Jacobian values on countably many measurable pieces.
    The original source Jacobian is preserved by proved locality;
    no uncountable intersection of exceptional sets is used. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  NormDifferentialUP PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic MeasureAlmostOnCover HausdorffMeasure
  MeasureApproximateJacobian DifferentiableSubsetJacobianAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_differentiable_jacobian_profile]: the
    countable manifold reduction in 3.2.48, p. 285, expanded with
    3.2.16 and the null-union laws. This supporting statement takes
    independent local graph and cover laws, all discharged by the
    actual spherical partition in the numbered theorem. *)
Theorem countable_differentiable_jacobian_profile (R:realType) m n v q (I:choiceType)
    (D:set I) (W:set (R_n R n)) (S:I->set (R_n R n))
    (F:R_n R n->R_n R v) (j:I->R_n R n->R) (J:R_n R n->R):
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m in
  countable D ->measure_measurable H W ->(H W< +oo)%E ->
  (forall i,D i ->measure_measurable H (S i)) ->(forall i,D i ->S i `<=` W) ->
  H (W `\` \bigcup_(i in D) S i)=0%E ->
  (forall x,W x ->exists L:Hom (R_n R n) (R_n R v),
    has_norm_differential (inner_norm (@euclidean_inner_productP R n))
      (inner_norm (@euclidean_inner_productP R v)) (fun _=>True) F x L) ->
  (forall i,D i ->forall x,S i x ->J x=j i x) ->
  (forall i,D i ->measure_almost_everywhere_on H (S i) [set x|partial_function_graph
    (measure_approximate_jacobian (measure_restrict H (S i)) m q
      (partial_function_source_restrict (S i) (partial_function_total F))) x (j i x)]) ->
  measure_almost_everywhere_on H W [set x|partial_function_graph
    (measure_approximate_jacobian (measure_restrict H W) m q
      (partial_function_source_restrict W (partial_function_total F))) x (J x)].
Proof.
move=>H hCount hW hFinite hSM hSW hLoss hDiff hJ hLocal.
have hH:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
apply:(@measure_almost_on_countable_cover R
  (inner_metric_space (@euclidean_inner_productP R n)) I H W D S _ hH hCount hLoss)=>i hi.
have hData:=@differentiable_subset_jacobian_agreement R m n v q W (S i) F
  hW (hSM i hi) (hSW i hi) hFinite (fun x hx=>hDiff x (hSW i hi x hx)).
have hBoth:=measure_almost_everywhere_and hH
  ((measure_almost_everywhere_on_implication _ _ _).1 hData)
  ((measure_almost_everywhere_on_implication _ _ _).1 (hLocal i hi)).
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hH _ hBoth)=>x [hDataX hLocalX] hx.
have hResult:=((hDataX hx (j i x)).2 (hLocalX hx)).
rewrite -(hJ i hi x hx) in hResult; exact hResult.
Qed.
