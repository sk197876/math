(** Federer (1969), 4.1.5, p. 350:
    the original norm presentation of Euclidean
    space also has the finite localized
    centered-ball derivation context of 2.8.18
    and 2.9.8. Reuse the proved finite-dimensional
    directional limitation and countable base. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates LinearBasis
  EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanNormCountableBase CountableBaseDenseSet
  NormDirectionalLimitation DirectionalLimitationUP MeasureUP MeasureBasic BorelRegularMeasureUP
  MeasureDerivationContext CoveringFamilyUP CoveringRelationUP CenteredBallRelations CenteredBallVitali
  MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_euclidean_norm_centered_derivation_context]:
    the exact original Euclidean norm context
    for the ball formula of Federer 4.1.5,
    p. 350, in every source dimension. *)
Lemma finite_euclidean_norm_centered_derivation_context (R:realType) n
    (mu:set (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))->\bar R):
  is_measure mu ->is_borel_regular_measure mu ->(mu setT< +oo)%E ->
  is_measure_derivation_context mu (@centered_closed_ball_relation R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))).
Proof.
move=>hm hr hFinite.
pose X:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)).
pose V:=@centered_closed_ball_relation R X.
have hContext:is_covering_theory_context (covering_relation_image V setT) mu.
  constructor=>//.
  - move=>B [x [_ [r [hR ->]]]]; exact:metric_closed_ball_closed.
  - move=>W hW; exact:(@borel_regular_open_measurable R X mu hr W hW).
  - move=>A _; exact:le_lt_trans (measure_mono hm (subsetT A)) hFinite.
have[B hB]:=@euclidean_norm_countable_open_base R n.
have hSeparable:=@countable_open_base_dense_set X 0 B hB.
have hThird:(0<((1:R)/3)%R<=1/3)%R.
  apply/andP; split; last exact:lexx; by rewrite divr_gt0 // ltr0n.
have[zeta hDirectional]:=@finite_norm_directional_limitation R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R n))
  n (@coordinate_basis R n) (@coordinate_basisP R n) (1/3) hThird.
pose C:set (set X):=[set setT].
have hCover:(\bigcup_(A in C) A)=setT.
  apply/seteqP; split=>x _; first exact I; by exists setT.
have hLimited A:C A ->exists (xi: \bar R) (eta:R) (k:nat),is_directionally_limited_at A xi eta k.
  move=>hA; change (A=setT) in hA; rewrite hA; by exists +oo%E,(1/3),zeta.
constructor.
- constructor=>// A _; exact:le_lt_trans (measure_mono hm (subsetT A)) hFinite.
- exact:(@federer_2_8_18 R X mu C hContext hSeparable (countable1 setT) hCover hLimited).
Qed.
