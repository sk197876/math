(** Federer (1969), 3.2.10, p. 248: supporting almost-everywhere
    agreement of the differentials of maps agreeing on E.
    This expands the density argument also used in 3.2.8,
    p. 247, using the existing first-order density uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP EuclideanLebesgueDimensions
  CenteredBallRelations PartialFunctionUP MeasureSetDensity MeasureUP MeasureAlmostUP
  MeasureAlmostBasic EuclideanFullDensityCore NormDifferentialUP NormDifferentialSubtraction
  NormDifferentialZeroOnDensitySet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [density_differential_agreement]: the identification
    of Du with the derivative of (f,p) on E in Federer 3.2.10,
    p. 248. Supporting first-order uniqueness at density-one points;
    arbitrary normed targets and dimension-zero sources are included. *)
Theorem density_differential_agreement (R:realType) m
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (f g:R_n R m->Y) (S:set (R_n R m)) a
    (L M:Hom (R_n R m) Y):
  S a -> (forall x,S x -> f x=g x) ->
  partial_function_graph
    (measure_set_density (@euclidean_lebesgue_measure R m)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R m)])
      (~` S)) a 0%E ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m)) NY setT f a L ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m)) NY setT g a M ->
  L=M.
Proof.
case:m f g S a L M=>[|m] f g S a L M ha hEq hDensity hF hG.
- apply:hom_ext=>x; by rewrite (coordinate_zero x) !linear0.
- pose NX:=inner_norm (@euclidean_inner_productP R m.+1).
  have hNX:=inner_norm_real_norm (@euclidean_inner_productP R m.+1).
  have hDiff:=norm_differential_subtract hNX hNY hF hG.
  have hZero:L-M=0.
    apply:(@norm_differential_zero_on_density_set R m Y NY hNY setT S
      (fun x=>f x-g x) a _ ha _ hDensity hDiff).
    move=>x hx; by rewrite (hEq x hx) subrr.
  move/eqP:hZero; by rewrite subr_eq0=>/eqP.
Qed.

(** Source for [measurable_set_differential_agreement_almost]:
    Federer 3.2.10, p. 248, supporting equality of the actual
    differentials almost everywhere on a measurable equality set.
    Differential existence is deliberately not supplied by defaults;
    each pointwise implication concerns actual differential witnesses. *)
Theorem measurable_set_differential_agreement_almost (R:realType) m
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (f g:R_n R m->Y) (E:set (R_n R m)):
  measure_measurable (@euclidean_lebesgue_measure R m) E ->
  (forall x,E x -> f x=g x) ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) E
    [set a|forall L M:Hom (R_n R m) Y,
      has_norm_differential (inner_norm (@euclidean_inner_productP R m)) NY setT f a L ->
      has_norm_differential (inner_norm (@euclidean_inner_productP R m)) NY setT g a M ->L=M].
Proof.
move=>hE hEq.
have [S [hSE [hNull hDensity]]]:=euclidean_full_density_core_exists hE.
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R m) _ _ _
  ((measure_almost_everywhere_on_implication _ _ _).1 hNull))=>a hCore ha L M hL hM.
have hSa:=hCore ha.
apply:(density_differential_agreement hNY hSa _ (hDensity a hSa) hL hM).
move=>x hx; exact (hEq x (hSE x hx)).
Qed.
