(** Federer (1969), 4.1.14, p. 371: the continuous
    weight sigma^m gives the original Radon variation measure.
    This supporting measure lemma reuses 2.4.10, p. 85,
    and the countable compact-neighbourhood criterion of 2.2.5,
    pp. 62–63. Neither a global weight bound nor finite
    total mass is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology normedtype lra.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  SummableRealFunctionUP PartialExtendedOrderLoci MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureDensity
  MeasureIntegralUP MeasureStepIntegralIdentification RealFiniteDensityIntegral RadonMeasureUP RadonBorelRegularity
  BorelRegularMeasureUP NonnegativeDensitySetUpperBound CountableRadonDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ContinuousRadonDensity.
Variable R:realType.
Variable X:metricType R.
Variable mu:set X->\bar R.
Hypotheses (hm:is_measure mu) (hr:is_radon_measure mu).
Variable w:X->R^o.
Hypothesis hW:continuous w.
Hypothesis hPositive:forall x,0<=w x.
Local Notation H:=(real_total_integrand w).
Local Notation lambda:=(measure_with_density mu H).

(** Source for [continuous_radon_density_measurable]:
    the original continuous scalar weight is measurable,
    supporting Federer 4.1.14, p. 371, by 2.3.2(4), p. 73. *)
Lemma continuous_radon_density_measurable:
  is_measure_measurable_function mu H.
Proof.
have hScalar:is_measure_measurable_function mu
    (partial_function_total (fun x=>(w x:real_line_metric R))).
  constructor.
  - rewrite partial_function_total_domain;exact:measure_almost_everywhere_true hm.
  - move=>O hO;rewrite partial_function_total_preimage.
    exact:(@radon_open_measurable R X mu hr (w @^-1` O)
      (((@continuousP X (real_line_metric R) w).1 hW) O hO)).
exact:(@measurable_partial_real_embedding R X mu hm _ hScalar).
Qed.

(** Source for [continuous_radon_density_nonnegative]:
    the original weight is nonnegative almost everywhere,
    supporting Federer 4.1.14, p. 371. *)
Lemma continuous_radon_density_nonnegative:
  measure_almost_everywhere mu (partial_extended_nonnegative_locus H).
Proof.
apply:(@measure_almost_everywhere_mono R X mu hm setT _ _
  (measure_almost_everywhere_true hm))=>x _.
exists (w x)%:E;split;first by rewrite real_total_integrand_graph.
rewrite lee_fin;exact:hPositive.
Qed.

(** Source for [continuous_radon_density_compact_finite]:
    the weight is bounded on each original compact set;
    its density measure is therefore finite there, supporting
    Federer 4.1.14, p. 371, by 2.4.10, p. 85. *)
Lemma continuous_radon_density_compact_finite K:
  compact K->(lambda K< +oo)%E.
Proof.
move=>hK.
have hImage:compact (w @` K:set R^o).
  exact:continuous_compact (continuous_subspaceT hW) hK.
have[B hB]:=@filter_ex _ _ proper_pinfty_nbhs _ (compact_bounded hImage).
pose C:R:=`|B|+1.
have hC:0<C by rewrite /C;have:=normr_ge0 B;lra.
have hUpper:forall x,K x->((w x)%:E<=C%:E)%E.
  move=>x hx;rewrite lee_fin.
  have hBound:`|w x|<=B:=hB (w x) (imageP w hx).
  have hAbs:=ler_norm B.
  have hValue:=ler_norm (w x).
  rewrite /C;lra.
have hRegular:=borel_regular_is_regular hm (radon_borel_regular hm hr).
have hDensity:=real_finite_density_total_laws (measure_with_density_laws mu H).
have hBound:=@nonnegative_density_set_upper_bound R X mu lambda hm
  (fun x=>(w x)%:E) K C hRegular hDensity hC hUpper.
have hFinite:mu K \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm K)).
  exact:(@radon_compact_finite R X mu hr K hK).
apply:le_lt_trans hBound _.
by rewrite -(fineK hFinite) -EFinM ltry.
Qed.

(** Source for [continuous_radon_density_radon]: the actual
    continuous nonnegative density gives a Radon measure,
    supporting Federer 4.1.14, p. 371. The supplied compact
    neighbourhoods are the preceding original open-domain exhaustion. *)
Theorem continuous_radon_density_radon (C W:nat->set X):
  (forall j,compact (C j))->(forall j,open (W j))->
  (forall j,W j `<=` C j)->setT `<=` \bigcup_j C j->
  setT `<=` \bigcup_j W j->is_radon_measure lambda.
Proof.
move=>hC hOpen hWC hCover hWCover.
exact:(@countable_compact_finite_radon_density R X mu lambda hm hr H C W
  (measure_with_density_laws mu H) continuous_radon_density_measurable
  continuous_radon_density_nonnegative
  (fun K hK=>@continuous_radon_density_compact_finite K hK)
  hC hOpen hWC hCover hWCover).
Qed.
End ContinuousRadonDensity.
