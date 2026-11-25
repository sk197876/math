(** Federer (1969), 3.2.7, p. 246: supporting
    divergence criterion for the weighted multiplicity.
    Infinitely many disjoint measurable sets of uniformly
    positive density mass force an infinite upper integral.
    Use 2.1.3(3), p. 55, and 2.4.10, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension PartialZeroExtensionLaws PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureBasic MeasureIntegralUP MeasureIntegralBounds MeasureBoundGraphEquivalence MeasureSubsetIntegral
  MeasureDensity MeasureDensityUP MeasureCountableAdditivity NonnegativeSum NonnegativeSumConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [density_disjoint_uniform_mass_divergence]:
    countable disjoint-set argument supporting the third
    example in Federer 3.2.7, p. 246. The
    density itself need not be measurable; all
    measures and upper integrals are the project's
    sealed operators rather than assigned default values. *)
Theorem density_disjoint_uniform_mass_divergence (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (h:X->extended_real_line R)
    (E:nat->set X) (d:R):
  (forall x,0<=h x) ->
  (forall k,measure_measurable mu (E k)) ->
  (forall i j,i!=j -> forall x,E i x -> E j x -> False) ->
  (0<d)%R ->
  (forall k,d%:E<=measure_with_density mu (partial_function_total h) (E k)) ->
  measure_upper_integral mu (partial_function_total h)=+oo.
Proof.
move=>hp hE hd hdPos hMass.
pose H:=partial_function_total h.
pose nu:=measure_with_density mu H.
have hNonneg:measure_almost_everywhere mu (partial_extended_nonnegative_locus H).
  apply:(@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=>x _.
  exists (h x); by split.
have hn:is_measure nu:=measure_with_density_is_measure hm hNonneg.
have hEn k:measure_measurable nu (E k):=measure_with_density_measurable hm hNonneg (hE k).
have hSum:=measure_sequence_disjoint_additivity hn hEn hd.
have hLower:nonnegative_sum setT (fun _ : nat=>d%:E)<=nonnegative_sum setT (fun k=>nu (E k)).
  apply:nonnegative_sum_mono=>k _; exact:hMass.
rewrite (nonnegative_sum_infinite_constant hdPos infinite_nat) -hSum in hLower.
have hWhole:nu setT=+oo.
  apply/eqP; rewrite eq_le; apply/andP; split; first exact:leey.
  apply:le_trans hLower _; apply:(measure_mono hn)=>x _; exact Logic.I.
have hLaw:=measure_with_density_laws mu H setT.
rewrite /measure_subset_upper_integral in hLaw.
have hEq:measure_upper_integral mu
    (partial_function_zero_extension (0:extended_real_line R) setT H)=measure_upper_integral mu H.
  apply:measure_upper_integral_graph_equivalent=>x z.
  exact:partial_zero_extension_whole_graph.
exact (eq_trans (Logic.eq_sym (eq_trans hLaw hEq)) hWhole).
Qed.
