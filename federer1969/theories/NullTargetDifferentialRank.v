(** Federer (1969), 3.2.22, pp. 258–259:
    apply the rank lemma 3.2.21 above the null
    target-chart remainder Q. The remainder need not be
    Borel, so use a Borel null cover first. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  LipschitzUP NormDifferentialUP LinearRankUP EuclideanLebesgueDimensions HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP
  RectifiableSetUP PureUnrectifiableLaws PureUnrectifiableRank.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_target_differential_rank]: the
    invocation of 3.2.21 on the null target remainder
    Q in Federer 3.2.22, pp. 258–259.
    A Borel null cover is purely unrectifiable and
    satisfies the printed Borel premise of 3.2.21.
    Restriction returns the conclusion on the original Q,
    with no Borel or measurability assumption on Q. *)
Theorem null_target_differential_rank (R:realType) m n mu
    (v:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (Q:set (inner_metric_space (@euclidean_inner_productP R n))):
  (0<mu)%N ->is_metric_lipschitz setT v ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) mu Q=0 ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) (v @^-1` Q)
    [set x|exists D r,
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R n)) setT v x D /\
      has_linear_rank D r /\ (r<mu)%N].
Proof.
move=>hMu hLip hQ.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose beta:=@hausdorff_measure R Y mu.
have hb:=@hausdorff_measure_is_measure R Y mu.
have [B [hQB [hB hMass]]]:=borel_regular_cover (@hausdorff_measure_borel_regular R Y mu) Q.
have hNull:beta B=0 by rewrite /beta -hMass.
have hPure:is_purely_measure_m_unrectifiable beta mu B.
  apply:(@pure_unrectifiable_iff_rectifiable_subsets_null R Y beta mu B).2.
  split; first exact hb; move=>S hSB _; exact:(measure_null_subset hb hSB hNull).
have h:=@federer_3_2_21 R m n mu v B hMu hLip hB hPure.
have hAll:=(measure_almost_everywhere_on_implication _ _ _).1 h.
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono (euclidean_lebesgue_is_measure R m) _ hAll)=>x hx hQx.
exact:(hx (hQB _ hQx)).
Qed.
