(** Federer (1969), 3.2.3, p. 243: both integrals
    vanish on a null source set. This uses 2.10.11,
    2.10.35 and the exact partial-integral conventions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureSubsetIntegral NullSubsetIntegral MeasureConullZeroIntegral
  HausdorffMeasure HausdorffLipschitzImages LipschitzUP
  MappingMultiplicity MappingMultiplicityLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_hausdorff_lipschitz_image]: the use
    of 2.10.11 in Federer 3.2.3, p. 243: a
    null source set has null image in the same natural
    Hausdorff degree, regardless of measurability. *)
Lemma null_hausdorff_lipschitz_image (R:realType) (X Y:metricType R)
    (f:X->Y) L k (A:set X):
  is_metric_lipschitz_bound setT f L -> @hausdorff_measure R X k A=0 ->
  @hausdorff_measure R Y k (f @` A)=0.
Proof.
move=>hf hA; have hh:=hausdorff_lipschitz_image_bound k hf A.
rewrite hA mule0 in hh.
by apply/eqP; rewrite eq_le hh (measure_nonnegative (@hausdorff_measure_is_measure R Y k)).
Qed.

(** Source for [null_hausdorff_multiplicity_integral]: the
    zero right-hand integral in Federer 3.2.3, p. 243.
    Multiplicity vanishes off the null image, so its exact
    total counting function is integrable with value zero. *)
Lemma null_hausdorff_multiplicity_integral (R:realType) (X Y:metricType R)
    (f:X->Y) L k (A:set X):
  is_metric_lipschitz_bound setT f L -> @hausdorff_measure R X k A=0 ->
  is_measure_integral (@hausdorff_measure R Y k)
    (partial_function_total (fun y=>(@mapping_multiplicity R X Y f A y:extended_real_line R))) 0.
Proof.
move=>hf hA.
pose beta:=@hausdorff_measure R Y k.
pose hb:=@hausdorff_measure_is_measure R Y k.
have hImage:beta (f @` A)=0:=null_hausdorff_lipschitz_image hf hA.
have hAE:measure_almost_everywhere beta (~` (f @` A)) by rewrite /measure_almost_everywhere setCK.
apply:(@measure_almost_zero_integral R Y beta hb _).
apply:(@measure_almost_everywhere_mono R Y beta hb (~` (f @` A)) _ _ hAE)=>y hy.
exact ((@mapping_multiplicity_zero_iff R X Y f A y).2 hy).
Qed.
