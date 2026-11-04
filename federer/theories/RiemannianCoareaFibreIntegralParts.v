(** Federer (1969), 3.2.46, p. 282, extending 3.2.12, p. 250: the
    signed reduction applies 2.4.4(6) on each fibre and
    then on the target. Exact inner-integrability graphs
    determine where the differences are defined. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff
  RiemannianCoareaFibreIntegral ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionPostcomposition PartialFunctionIntegralParts MeasureUpperIntegralPositivePart PartialExtendedArithmetic
  PartialZeroExtension PartialZeroExtensionLaws MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralPartsDifference
  MeasureIntegralAddition MeasureIntegralNegationLaw MeasureIntegralAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_coarea_fibre_parts_graph]: the
    2.4.4(6) step on actual Riemannian fibres in 3.2.46, p. 282, extending Federer
    3.2.12, p. 250. A defined difference
    of the two actual inner part integrals is the
    actual signed inner integral; no default is assigned. *)
Lemma riemannian_coarea_fibre_parts_graph (R:realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hpFibre : (0<=(m-n)%:R :> R)%R) u y a:
  partial_function_graph (partial_extended_function_subtract
    (riemannian_coarea_fibre_integral f hpFibre (partial_extended_function_positive_part u))
    (riemannian_coarea_fibre_integral f hpFibre (partial_extended_function_negative_part u))) y a ->
  partial_function_graph (riemannian_coarea_fibre_integral f hpFibre u) y a.
Proof.
move=>/(partial_extended_function_add_graph _ _ y a) [P [N [hP [[Q [hQ hN]] hSum]]]].
have hIP:=(riemannian_coarea_fibre_integral_graph f hpFibre _ y P).1 hP.
have hIN:=(riemannian_coarea_fibre_integral_graph f hpFibre _ y Q).1 hQ.
pose X:=[the choiceType of riemannian_metric_space hg].
pose beta:=riemannian_hausdorff_measure hg (m-n)%:R hpFibre.
pose cut:=partial_function_zero_extension (0:extended_real_line R) [set x|f x=y] u.
have hP0:(@extended_positive_part R 0)=0 by rewrite /extended_positive_part maxxx.
have hN0:(@extended_negative_part R 0)=0 by rewrite /extended_negative_part oppe0 /extended_positive_part maxxx.
have hp:is_measure_integral beta (partial_extended_function_positive_part cut) P.
  apply:(measure_integral_graph_equivalent _ hIP)=>x z.
  exact:iff_sym (partial_zero_extension_postcompose [set x|f x=y] u x z hP0).
have hn:is_measure_integral beta (partial_extended_function_negative_part cut) Q.
  apply:(measure_integral_graph_equivalent _ hIN)=>x z.
  exact:iff_sym (partial_zero_extension_postcompose [set x|f x=y] u x z hN0).
apply:(riemannian_coarea_fibre_integral_graph f hpFibre u y a).2.
apply:(measure_integral_from_parts (@riemannian_hausdorff_is_measure R m A g hg (m-n)%:R hpFibre) hp hn).
change (extended_add P (-Q)=Some a).
rewrite hN; exact hSum.
Qed.

(** Source for [riemannian_coarea_fibre_integral_parts]: the
    outer signed reduction for 3.2.46, p. 282, extending Federer 3.2.12, p. 250.
    A defined difference of the two outer part integrals
    gives the original iterated integral, including either infinite value. *)
Theorem riemannian_coarea_fibre_integral_parts (R:realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hpFibre : (0<=(m-n)%:R :> R)%R) u
    (alpha:set (riemannian_metric_space hh)->\bar R)
    (ha:is_measure alpha) P N a:
  is_measure_integral alpha (riemannian_coarea_fibre_integral f hpFibre (partial_extended_function_positive_part u)) P ->
  is_measure_integral alpha (riemannian_coarea_fibre_integral f hpFibre (partial_extended_function_negative_part u)) N ->
  extended_subtract P N=Some a ->
  is_measure_integral alpha (riemannian_coarea_fibre_integral f hpFibre u) a.
Proof.
move=>hP hN hDifference.
have hDiff:=measure_integral_add ha hP (measure_integral_negation ha hN) hDifference.
apply:(measure_integral_almost_equal ha hDiff).
apply:(@measure_almost_everywhere_mono R _ alpha ha _ _ _
  (measurable_function_domain hDiff.1))=>y [z hz].
exists z; split=> //; exact (riemannian_coarea_fibre_parts_graph hz).
Qed.
