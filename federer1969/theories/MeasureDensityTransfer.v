(** Federer (1969), 2.4.10, p. 85: transfer of measurable functions and null
    replacements to the density measure. These supporting lemmas retain the
    original partial graphs outside the conull comparison sets. Source
    editions: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP PartialExtendedOrderLoci
  MeasureDensityUP MeasureDensityMeasurable MeasureDensityNullSets MeasureSubsetIntegral
  MeasureUpperAlmostEquality PartialDensityProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_density_measurable_function]: supporting
    transfer of phi-measurability to psi-measurability for the
    integrand in Federer 2.4.10, p. 85. *)
Lemma measure_density_measurable_function (R : realType) (X : choiceType) (Y : topologicalType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (h : partial_function X (extended_real_line R)) (f : partial_function X Y) :
  is_measure_density mu h nu -> measure_almost_everywhere mu (partial_extended_nonnegative_locus h) ->
  is_measure_measurable_function mu f -> is_measure_measurable_function nu f.
Proof.
move=> hn hp hf; constructor.
- exact (@measure_density_almost_everywhere R X mu nu hm h _ hn (measurable_function_domain hf)).
- move=> U hU; exact (@measure_density_preserves_measurable_sets R X mu nu hm h _ hn hp
    (measurable_function_open_preimage hf hU)).
Qed.

(** Source for [zero_extension_almost_equal]: supporting
    compatibility of null replacements and subset integrals in
    Federer 2.4.10, p. 85. No measurability of
    the restricting set is required. *)
Lemma zero_extension_almost_equal (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (zero : Y) (A : set X)
    (f g : partial_function X Y) :
  measure_almost_equal mu f g -> measure_almost_equal mu
    (partial_function_zero_extension zero A f) (partial_function_zero_extension zero A g).
Proof.
move=> he; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ he)=> x [y [hf hg]].
have [ha|ha] := pselect (A x).
- exists y; split; apply/partial_function_zero_extension_graph; left; by split.
- exists zero; split; apply/partial_function_zero_extension_graph; right; by split.
Qed.

(** Source for [measure_density_almost_equal]: null modifications of the
    density leave its set function unchanged, supporting the
    total-representative reduction in Federer 2.4.10, p. 85. *)
Lemma measure_density_almost_equal (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (h k : partial_function X (extended_real_line R)) :
  is_measure_density mu h nu -> measure_almost_equal mu h k -> is_measure_density mu k nu.
Proof.
move=> hn he A; rewrite (hn A).
apply: (@measure_upper_integral_almost_equal R X mu hm).
exact (@zero_extension_almost_equal R X (extended_real_line R) mu hm 0 A h k he).
Qed.

(** Source for [partial_density_product_almost_equal]: supporting
    invariance of the product fg under the null replacements
    in the proof of Federer 2.4.10, p. 85.
    The zero-infinity convention is respected in both products. *)
Lemma partial_density_product_almost_equal (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g h k : partial_function X (extended_real_line R)) :
  measure_almost_equal mu f g -> measure_almost_equal mu h k ->
  measure_almost_equal mu (partial_density_product f h) (partial_density_product g k).
Proof.
move=> he hf; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ he hf)).
move=> x [[a [ha hag]] [b [hb hbk]]]; exists (a*b); split;
  apply/partial_density_product_graph; exists a,b; by split=> //; split.
Qed.
