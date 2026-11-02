(** Federer (1969), 3.2.22, p. 259: null
    target-coordinate exceptions can be used in every
    degree. The positive-degree argument is 3.2.21;
    a degree-zero Hausdorff-null target is empty. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  LipschitzUP NormDifferentialUP LinearRankUP EuclideanLebesgueDimensions
  HausdorffMeasure HausdorffZeroNullEmpty NullTargetDifferentialRank MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_target_rank_all_degrees]: supporting
    preimages of bad target-chart parameters in Federer
    3.2.22, p. 259. For positive degree use
    3.2.21 with a Borel null hull. In degree
    zero the null target is empty, so the conditional
    conclusion is vacuous without changing any derivative
    convention or asserting a negative rank. *)
Lemma null_target_rank_all_degrees (R:realType) m n mu
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (N:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_metric_lipschitz setT f ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) mu N=0 ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) (f @^-1` N)
    [set x|exists D r,
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R n)) setT f x D /\
      has_linear_rank D r /\ (r<mu)%N].
Proof.
move=>hF hN; have [hZero|hZero]:=eqVneq mu 0%N.
- subst mu; have hEmpty:=hausdorff_zero_null_set_empty hN.
  rewrite /measure_almost_everywhere_on hEmpty preimage_set0 set0D.
  exact:measure_empty (euclidean_lebesgue_is_measure R m).
- have hPos:(0<mu)%N by rewrite lt0n.
  exact:(null_target_differential_rank hPos hF hN).
Qed.
