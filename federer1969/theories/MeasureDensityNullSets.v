(** Federer (1969), 2.4.10, p. 85: supporting preservation of null sets for
    the density measure, allowing total representatives in the
    change-of-density proof. Source context: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureStepConstants MeasureStepIntegralIdentification MeasureIntegralGraphEquivalence
  MeasureSubsetIntegral MeasureDensityUP MeasureUpperAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_extended_zero_integral]: supporting
    total zero integral for the subset convention in Federer
    2.4.10, p. 85, valid even on infinite-measure spaces. *)
Lemma measure_extended_zero_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_measure_integral mu (partial_function_total (fun _ : X => (0 : extended_real_line R))) 0.
Proof.
have ha := @measure_step_constant_integral R X mu hm 0%R; rewrite mul0e in ha.
have hi := @measure_step_function_integral R X mu hm _ 0 (@measure_step_constant R X mu hm 0%R) ha.
apply: (@measure_integral_graph_equivalent R X mu _ _ 0 _ hi)=> x y; split.
- by move=> [r [hr ery]]; rewrite -(hr : 0%R=r) in ery.
- move=> hy; exists 0%R; by split.
Qed.

(** Source for [measure_upper_extended_zero]: upper-integral
    version of the total zero boundary in Federer 2.4.10, p. 85. *)
Lemma measure_upper_extended_zero (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  measure_upper_integral mu (partial_function_total (fun _ : X => (0 : extended_real_line R))) = 0.
Proof.
exact: measure_upper_integral_unique (measure_upper_integral_specification mu _)
  (measure_extended_zero_integral hm).2.1.
Qed.

(** Source for [measure_density_null_set]: Supporting Federer 2.4.10, p. 85. *)
Lemma measure_density_null_set (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (g : partial_function X (extended_real_line R)) (A : set X) :
  is_measure_density mu g nu -> mu A=0 -> nu A=0.
Proof.
move=> hn hA; rewrite (hn A) /measure_subset_upper_integral.
have hAc : measure_almost_everywhere mu (~` A) by rewrite /measure_almost_everywhere setCK.
have heq : measure_almost_equal mu
    (partial_function_zero_extension (0 : extended_real_line R) A g)
    (partial_function_total (fun _ : X => (0 : extended_real_line R))).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hAc)=> x hx.
  exists 0; split=> //; apply/partial_function_zero_extension_graph; right; by split.
rewrite (@measure_upper_integral_almost_equal R X mu hm _ _ heq).
exact: measure_upper_extended_zero.
Qed.

(** Source for [measure_density_almost_everywhere]: supporting transfer of
    almost-everywhere statements from phi to psi in the proof of Federer
    2.4.10, p. 85 *)
Lemma measure_density_almost_everywhere (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (g : partial_function X (extended_real_line R)) (P : set X) :
  is_measure_density mu g nu -> measure_almost_everywhere mu P -> measure_almost_everywhere nu P.
Proof. move=> hn hp; exact (@measure_density_null_set R X mu nu hm g (~` P) hn hp). Qed.
