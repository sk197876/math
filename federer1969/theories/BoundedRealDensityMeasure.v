(** Federer (1969), 4.1.7, p. 358:
    a scalar density between zero and one
    gives a dominated Radon measure on U.
    The actual density outer measure is retained;
    its bound is the earlier 2.4.10 comparison. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  SummableRealFunctionUP MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP BorelRegularMeasureUP RadonMeasureUP RadonBorelRegularity
  MeasureDensityUP MeasureDensity NonnegativeDensitySetUpperBound RealFiniteDensityIntegral
  CountableRadonDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section BoundedRealDensityMeasure.
Variable R:realType.
Variable X:metricType R.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hr:is_radon_measure mu.
Variable k:X->R.
Hypothesis hk:is_measure_measurable_function mu (real_total_integrand k).
Hypothesis hRange:forall x,0<=k x<=1.
Local Notation nu := (measure_with_density mu (real_total_integrand k)).

(** Source for [unit_real_density_measure_bound]:
    the density outer mass is at most the
    original outer mass on every set, supporting
    Federer 4.1.7, p. 358, by 2.4.10,
    p. 85. Arbitrary and infinite-mass sets
    are included. *)
Lemma unit_real_density_measure_bound A:(nu A<=mu A)%E.
Proof.
have hRegular:=borel_regular_is_regular hm (radon_borel_regular hm hr).
have hDensity:=real_finite_density_total_laws (measure_with_density_laws mu (real_total_integrand k)).
have hBound:=@nonnegative_density_set_upper_bound R X mu nu hm
  (fun x=>(k x)%:E) A 1 hRegular hDensity ltr01.
have hUpper:forall x,A x->((k x)%:E<=1%:E)%E.
  move=>x _; rewrite lee_fin; exact:(andP (hRange x)).2.
by have:=hBound hUpper; rewrite mul1e.
Qed.

(** Source for [unit_real_density_measure_nonnegative]:
    the bounded original real density is
    nonnegative almost everywhere, supporting Federer
    4.1.7, p. 358. *)
Lemma unit_real_density_measure_nonnegative:
  measure_almost_everywhere mu (partial_extended_nonnegative_locus (real_total_integrand k)).
Proof.
apply:(@measure_almost_everywhere_mono R X mu hm setT _ _
  (measure_almost_everywhere_true hm))=>x _.
exists (k x)%:E; split; first by rewrite real_total_integrand_graph.
rewrite lee_fin; exact:(andP (hRange x)).1.
Qed.

(** Source for [unit_real_density_measure_radon]:
    the original bounded-density outer measure is
    Radon on the given countably covered open
    domain, supporting Federer 4.1.7, p. 358,
    by 2.2.5 and 2.4.10. *)
Theorem unit_real_density_measure_radon (C W:nat->set X):
  (forall j,compact (C j)) ->(forall j,open (W j)) ->(forall j,W j `<=` C j) ->
  setT `<=` \bigcup_j C j ->setT `<=` \bigcup_j W j ->is_radon_measure nu.
Proof.
move=>hC hW hWC hCover hWCover.
have hFinite K (hK:compact K):(nu K< +oo)%E.
  exact:le_lt_trans (unit_real_density_measure_bound K) (radon_compact_finite hr hK).
exact:(@countable_compact_finite_radon_density R X mu nu hm hr (real_total_integrand k) C W
  (measure_with_density_laws mu (real_total_integrand k)) hk unit_real_density_measure_nonnegative
  hFinite hC hW hWC hCover hWCover).
Qed.
End BoundedRealDensityMeasure.
