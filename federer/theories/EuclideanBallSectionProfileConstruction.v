(** Federer (1969), 2.10.27, pp. 190–191: existence of the specified
    ball-section profile and its displayed integral. Realize the profile as
    the k-dimensional Lebesgue volume of sections of an auxiliary closed
    ball in R^(m+k). The proved block-product identity and set Fubini
    theorem give its integral, without importing an external beta-integral
    formula. Empty blocks and radius zero are included. This witness remains
    behind the profile's opaque public interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  InnerNormedTopology EuclideanBlockCoordinates EuclideanBlockMeasure EuclideanMetricProduct
  EuclideanBallSections EuclideanClosedBallVolume EuclideanBallVolume EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes MetricClosedBalls MetricCartesianProductUP EuclideanBallSectionProfileUP
  TopologicalBorel MeasureUP MeasureBasic MeasurePushforward PushforwardMeasurableSets
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic MeasureIntegralUP ProductMeasure ProductSections ProductSetFubini
  CountablyMeasurableUP CountablyMeasurableSubsets CountablyMeasurableProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_ball_section_profile_exists]: supporting
    existence and exact integral of the profile in
    the first display of 2.10.27, p. 191.
    The auxiliary vertical dimension is k, regardless
    of the dimension of the original section space. *)
Theorem euclidean_ball_section_profile_exists (R : realType) m k
    (u : inner_metric_space (@euclidean_inner_productP R m)) (r : R) :
  (0<=r)%R -> exists q, is_euclidean_ball_section_profile k u r q /\
    is_measure_integral (@euclidean_lebesgue_measure R m)
      (partial_function_total (fun y=>(q y : extended_real_line R)))
      (euclidean_unit_ball_volume R (k+m)*r^+(k+m))%R%:E.
Proof.
move=> hr.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Z := inner_metric_space (@euclidean_inner_productP R k).
pose P := inner_metric_space (@euclidean_inner_productP R (m+k)).
pose B := metric_closed_ball (@euclidean_block_join R m k (u,0%R)) r.
pose S := (@euclidean_block_join R m k) @^-1` B.
pose q y := @euclidean_lebesgue_measure R k (product_vertical_section S y).
have hprofile : is_euclidean_ball_section_profile k u r q.
  constructor.
  - move=> y hy.
    change (@euclidean_lebesgue_measure R k
      (metric_product_section (fun a b=>@euclidean_block_join R m k (a,b)) B y)=
      (euclidean_unit_ball_volume R k*Num.sqrt (r^+2-mdist u y^+2)^+k)%R%:E).
    rewrite (@euclidean_closed_ball_section R m k u y 0%R r hr hy).
    exact: euclidean_closed_ball_normalized_volume (sqrtr_ge0 _).
  - move=> y hy.
    have he : product_vertical_section S y=set0.
      apply/seteqP; split=> [z hz|z []].
      have hmem : ((fun p=>(@euclidean_block_split R m k p).1) @` B) y.
        exists (euclidean_block_join (y,z)); last by rewrite euclidean_block_joinK.
        exact hz.
      rewrite (@euclidean_closed_ball_first_projection R m k u 0%R r hr) in hmem.
      have hle : (mdist u y<=r)%R := hmem.
      by have hh := lt_le_trans hy hle; rewrite ltxx in hh.
    rewrite /q he; exact: measure_empty (euclidean_lebesgue_is_measure R k).
have hpre : (@euclidean_block_split R m k) @^-1` S=B.
  by apply/seteqP; split=> x; rewrite /S /= euclidean_block_splitK.
pose ha := euclidean_lebesgue_is_measure R m.
pose hb := euclidean_lebesgue_is_measure R k.
have hp := euclidean_block_measure R m k.
have hB : measure_measurable (@euclidean_lebesgue_measure R (m+k)) B.
  apply: euclidean_borel_measurable; apply: closed_borel_set; exact: metric_closed_ball_closed.
have hS : measure_measurable (product_measure ha hb) S.
  rewrite -hp; apply: pushforward_measurable_from_preimage; by rewrite hpre.
have hSc : measure_countably_measurable (product_measure ha hb) S.
  apply: (measurable_subset_countably_measurable (product_measure_is_measure ha hb) hS (subsetT S)).
  exact: product_whole_countably_measurable (euclidean_lebesgue_countably_measurable R m)
    (euclidean_lebesgue_countably_measurable R k).
have hi := (@product_set_fubini R X Z _ _ ha hb S hSc).2.2.1.
have hmass : product_measure ha hb S=(euclidean_unit_ball_volume R (k+m)*r^+(k+m))%R%:E.
  rewrite -hp /measure_pushforward hpre.
  rewrite (@euclidean_closed_ball_normalized_volume R (m+k) _ r hr) (addnC m k); reflexivity.
exists q; split=> //; by rewrite hmass in hi.
Qed.
