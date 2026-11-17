(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: the actual
    analytic germ space with the exact displayed derivative metric. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermOperationsUP RealNormUP NormMetric ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm HolomorphicGermUP HolomorphicGermJetsSealed HolomorphicGermTaylorInjective
  JetSequenceMetricUP JetSequenceMetricLaws JetSequenceMetricSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section GermMetric.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable a:X.
Local Notation NS:=(@complex_modulus R).
Local Notation hNS:=(@complex_modulus_real_norm R).
Local Notation Z:=(fun m=>@ContinuousMultilinear.space R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NS hNX hNS).
Local Notation ZN:=(fun m=>@ContinuousMultilinear.norm R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NS hNX hNS).
Local Notation hZN:=(fun m=>continuous_multilinear_norm_is_norm hNS
  (@ContinuousMultilinear.laws R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX NS hNX hNS)).
Local Notation jet:=(@HolomorphicGermJets.value R X NX hNX a).

(** Source for [holomorphic_germ_metric]: the original germs,
    equipped below with the metric of 3.4.5, p. 319.
    The underlying quotient carrier remains opaque. *)
Definition holomorphic_germ_metric:Type:=holomorphic_germ_space hNX a.
HB.instance Definition _:=Choice.copy holomorphic_germ_metric (holomorphic_germ_space hNX a).

(** Source for [holomorphic_germ_distance]: the actual distance
    in 3.4.5, p. 319, selected from the independent
    exact jet-series laws and hidden by their seal. *)
Definition holomorphic_germ_distance (alpha beta:holomorphic_germ_metric):R:=
  @JetSequenceMetric.distance R (holomorphic_germ_space hNX a) Z ZN hZN jet alpha beta.

(** Source for [holomorphic_germ_distance_formula]: exact equality
    with Federer's series in 3.4.5, p. 319,
    including m=0 and the coefficient 2^(-m). *)
Lemma holomorphic_germ_distance_formula:is_jet_sequence_distance ZN jet holomorphic_germ_distance.
Proof. exact:JetSequenceMetric.laws. Qed.

HB.instance Definition _:=isMetric.Build R holomorphic_germ_metric
  (@jet_sequence_distance_self R (holomorphic_germ_space hNX a) Z ZN hZN jet
    holomorphic_germ_distance holomorphic_germ_distance_formula)
  (@jet_sequence_distance_separates R (holomorphic_germ_space hNX a) Z ZN hZN jet
    holomorphic_germ_distance holomorphic_germ_distance_formula
    (@holomorphic_germ_jets_injective R X NX hNX a))
  (@jet_sequence_distance_symmetric R (holomorphic_germ_space hNX a) Z ZN hZN jet
    holomorphic_germ_distance holomorphic_germ_distance_formula)
  (fun beta alpha gamma=>@jet_sequence_distance_triangle R (holomorphic_germ_space hNX a) Z ZN hZN jet
    holomorphic_germ_distance holomorphic_germ_distance_formula alpha beta gamma).

(** Source for [holomorphic_germ_metric_distanceE]: the metric
    hierarchy uses precisely the public distance defined by
    the original series, 3.4.5, p. 319. *)
Lemma holomorphic_germ_metric_distanceE (alpha beta:holomorphic_germ_metric):
  mdist alpha beta=holomorphic_germ_distance alpha beta.
Proof. by []. Qed.
End GermMetric.
