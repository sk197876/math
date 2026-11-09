(** Federer (1969), 3.4.5, p. 319: the actual
    analytic germ space with the exact displayed derivative metric. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm AnalyticGermUP AnalyticGermJetsSealed AnalyticGermTaylorInjective
  JetSequenceMetricUP JetSequenceMetricLaws JetSequenceMetricSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section GermMetric.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation NS:=(fun t:R^o=>`|t|).
Local Notation hNS:=(@scalar_absolute_value_norm R).
Local Notation Z:=(fun m=>@ContinuousMultilinear.space R m X R^o NX NS hNX hNS).
Local Notation ZN:=(fun m=>@ContinuousMultilinear.norm R m X R^o NX NS hNX hNS).
Local Notation hZN:=(fun m=>continuous_multilinear_norm_is_norm hNS
  (@ContinuousMultilinear.laws R m X R^o NX NS hNX hNS)).
Local Notation jet:=(@AnalyticGermJets.value R X NX hNX a).

(** Source for [analytic_germ_metric]: the original germs,
    equipped below with the metric of 3.4.5, p. 319.
    The underlying quotient carrier remains opaque. *)
Definition analytic_germ_metric:Type:=analytic_germ_space hNX a.
HB.instance Definition _:=Choice.copy analytic_germ_metric (analytic_germ_space hNX a).

(** Source for [analytic_germ_distance]: the actual distance
    in 3.4.5, p. 319, selected from the independent
    exact jet-series laws and hidden by their seal. *)
Definition analytic_germ_distance (alpha beta:analytic_germ_metric):R:=
  @JetSequenceMetric.distance R (analytic_germ_space hNX a) Z ZN hZN jet alpha beta.

(** Source for [analytic_germ_distance_formula]: exact equality
    with Federer's series in 3.4.5, p. 319,
    including m=0 and the coefficient 2^(-m). *)
Lemma analytic_germ_distance_formula:is_jet_sequence_distance ZN jet analytic_germ_distance.
Proof. exact:JetSequenceMetric.laws. Qed.

HB.instance Definition _:=isMetric.Build R analytic_germ_metric
  (@jet_sequence_distance_self R (analytic_germ_space hNX a) Z ZN hZN jet
    analytic_germ_distance analytic_germ_distance_formula)
  (@jet_sequence_distance_separates R (analytic_germ_space hNX a) Z ZN hZN jet
    analytic_germ_distance analytic_germ_distance_formula
    (@analytic_germ_jets_injective R X NX hNX a))
  (@jet_sequence_distance_symmetric R (analytic_germ_space hNX a) Z ZN hZN jet
    analytic_germ_distance analytic_germ_distance_formula)
  (fun beta alpha gamma=>@jet_sequence_distance_triangle R (analytic_germ_space hNX a) Z ZN hZN jet
    analytic_germ_distance analytic_germ_distance_formula alpha beta gamma).

(** Source for [analytic_germ_metric_distanceE]: the metric
    hierarchy uses precisely the public distance defined by
    the original series, 3.4.5, p. 319. *)
Lemma analytic_germ_metric_distanceE (alpha beta:analytic_germ_metric):
  mdist alpha beta=analytic_germ_distance alpha beta.
Proof. by []. Qed.
End GermMetric.
