(** Federer (1969), 3.2.11, p. 249: invariance
    of the translated fibre-mass integral, by 2.7.16. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanAdditiveGroup
  EuclideanLebesgueDimensions EuclideanLebesgueTranslation MeasureBijectionTotalIntegral
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_scaled_translation_integral]: the
    inner y-integral is independent of z in Federer
    3.2.11, p. 249. Infinite nonnegative integral
    values and every natural target dimension are retained. *)
Lemma coarea_scaled_translation_integral (R:realType) n
    (theta:inner_metric_space (@euclidean_inner_productP R n)->extended_real_line R)
    e (z: R_n R n) a:
  (forall y,0<=theta y) ->
  is_measure_integral (@euclidean_lebesgue_measure R n) (partial_function_total theta) a ->
  is_measure_integral (@euclidean_lebesgue_measure R n)
    (partial_function_total (fun y=>theta (y-e*:z)%R)) a.
Proof.
move=>hp hi.
have ht:=@measure_bijection_total_nonnegative_integral R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
  [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
  _ _ (euclidean_lebesgue_is_measure R n) (euclidean_lebesgue_is_measure R n)
  _ _ theta a (euclidean_lebesgue_translation_bijection (-e*:z)%R) hp hi.
apply:(measure_integral_graph_equivalent _ ht)=>y t.
change (theta ((-e)*:z+y)%R=t <->theta (y-e*:z)%R=t).
by rewrite scaleNr addrC.
Qed.
