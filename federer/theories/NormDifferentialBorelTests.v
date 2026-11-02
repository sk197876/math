(** Federer (1969), 3.2.2, p. 242: the simultaneous
    differential and finite-radius remainder conditions define Borel
    sets. Project their single-valued Borel graph as in 3.1.1,
    using the proved injective Borel image theorem of 2.2.10. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis NormDifferentialUP NormDifferentialDirectional
  NormClassOneUP ContinuousOperatorUP ContinuousOperatorNorm NormDifferentialBorelGraph
  FiniteNormMetricPolish MetricProductBackground TopologicalBorel BorelFamilyBasic BorelSingleValuedProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [norm_differential_borel_domain_test]: supporting
    the Borel assertion for Z(s,i) in Federer 3.2.2, p. 242.
    Any Borel condition on a point and its actual differential
    has a Borel point locus when the source and operator spaces
    are finite dimensional. No differential field or arbitrary
    total extension is supplied as an extra hypothesis. *)
Theorem norm_differential_borel_domain_test (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (ev:Hom Z (Hom X Y)) (ZN:Z->R)
    (hZ:is_continuous_operator_space NX NY ev ZN)
    m (e:'I_m->X) (he:is_basis e) q (b:'I_q->Z) (hb:is_basis b)
    (A:X->Prop) (f:X->Y) :
  norm_class_zero NX NY A f ->
  forall C:set (metric_product (real_norm_metric_space hNX)
      (real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ))),
    borel_set C -> @borel_set [the topologicalType of real_norm_metric_space hNX]
      [set a|exists z,has_norm_differential NX NY A f a (ev z) /\ C (a,z)].
Proof.
move=>hf C hC.
pose E:=real_norm_metric_space hNX.
pose hZN:=continuous_operator_norm_is_norm hNY hZ.
pose T:=real_norm_metric_space hZN.
pose P:=metric_product E T.
pose D:=@norm_differential_operator_graph R X Y Z NX NY hNX hNY ev ZN hZ A f.
pose G:set P:=D `&` C.
have hD:borel_set D:=@norm_differential_operator_graph_borel R X Y Z NX NY hNX hNY ev ZN hZ A f hf.
have hG:borel_set G:=borel_family_binary_intersection (borel_sets_family P) hD hC.
have hUnique a u v:G (a,u) -> G (a,v) -> u=v.
  move=>[hu _] [hv _]; apply:(continuous_operator_injective hZ).
  exact (@norm_differential_unique R X Y NX NY hNX hNY A f a (ev u) (ev v) hu hv).
have htest:=@borel_single_valued_graph_preimage R E T G
  (@finite_norm_metric_complete R X NX hNX m e he)
  (@finite_norm_metric_complete R Z ZN hZN q b hb)
  (@finite_norm_metric_separable R X NX hNX m e he)
  (@finite_norm_metric_separable R Z ZN hZN q b hb)
  hG hUnique setT (open_borel_set (@openT T)).
have heq:[set a:E|exists z,G (a,z) /\ setT z]=
    [set a:E|exists z,has_norm_differential NX NY A f a (ev z) /\ C (a,z)].
  apply/seteqP; split=>a.
  - move=>[z [[hz hcz] _]]; by exists z.
  - move=>[z [hz hcz]]; exists z; by split; first split.
by rewrite heq in htest.
Qed.
