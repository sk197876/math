(** Federer (1969), 3.2.3, p. 243: each Borel
    distortion piece has matching area and Jacobian integral
    up to lambda^(2m). The intermediate determinant is the
    same automorphism's determinant in both comparisons. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormMetric EuclideanLinearMaps EuclideanLinearJacobian
  EuclideanLebesgueDimensions MeasureUP MeasureIntegralUP MeasureSubsetIntegral
  PartialFunctionUP JacobianUP Jacobian EuclideanJacobianMeasurable
  InjectiveDifferentialPieceUP SubsetIntegralConstantBounds BorelPieceImageBounds
  InnerOwnNormTopology HausdorffMeasure LipschitzUP AreaPieceScalarBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [area_piece_integral_bounds]: the
    lambda^(2m) integral/image sandwich in Federer 3.2.3,
    p. 243. Both extended integral values and infinite
    image measure are allowed. The original Borel piece
    laws supply every differential and inverse property. *)
Theorem area_piece_integral_bounds (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (lambda:R) (E B:set (R_n R m)):
  is_metric_lipschitz setT f -> (1<lambda)%R -> is_injective_differential_piece f lambda E ->
  measure_measurable (@euclidean_lebesgue_measure R m) B -> B `<=` E ->
  exists a,is_measure_subset_integral (@euclidean_lebesgue_measure R m) B
      (extended_euclidean_jacobian f) a /\
    a<=(lambda^+(m+m)%N)%R%:E* @hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m (f @` B) /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (f @` B)<=
      (lambda^+(m+m)%N)%R%:E*a.
Proof.
move=>hLip hl hPiece hB hBE.
have hl0:(0<lambda)%R:=lt_trans ltr01 hl.
have hInv0:(0<lambda^-1)%R by rewrite invr_gt0.
have [s [t [g [hst [hts [hg [hForward [hInverse hModel]]]]]]]]:=hPiece.2.2.2.
pose d:=`|euclidean_det (hom_as_linear s)|%R.
have hs:injective s:=can_inj hst.
have hDet:euclidean_det (hom_as_linear s)!=0%R:=(euclidean_det_injective _).2 hs.
have hd:(0<d)%R by rewrite /d normr_gt0.
have hc:(0<(lambda^-1^+m*d)%R)%R:=mulr_gt0 (exprn_gt0 m hInv0) hd.
have hC:(0<(lambda^+m*d)%R)%R:=mulr_gt0 (exprn_gt0 m hl0) hd.
have [a hI]:=euclidean_jacobian_subset_integrable hLip hB.
have hBound x j:B x -> partial_function_graph (extended_euclidean_jacobian f) x j ->
    (lambda^-1^+m*d)%R%:E<=j /\ j<=(lambda^+m*d)%R%:E.
  move=>hx [r [hr <-]].
  have [D [hD hJ]]:=(euclidean_jacobian_graph m setT f x r).1 hr.
  have [hLow hUp]:=(hModel x (hBE x hx) D hD).2.
  rewrite hJ in hLow hUp.
  split; rewrite lee_fin; [exact hLow|exact hUp].
have [hLow hUp]:=@subset_integral_constant_bounds R _ _ (euclidean_lebesgue_is_measure R m)
  B (extended_euclidean_jacobian f) a (lambda^-1^+m*d)%R (lambda^+m*d)%R hB hc hC hBound hI.
rewrite EFinM -muleA in hLow.
rewrite EFinM -muleA in hUp.
have [hF hG]:=@borel_piece_image_bounds R m n f E B s t g lambda hst hg hForward hInverse hBE.
rewrite inner_own_norm_hausdorff in hF hG.
have hBounds:=area_piece_scalar_bounds hl0 hLow hUp hF hG.
exists a; by split.
Qed.
