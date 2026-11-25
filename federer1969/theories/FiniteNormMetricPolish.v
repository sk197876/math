(** Federer (1969), 3.1.1, p. 211: the finite-dimensional normed
    source is complete and separable, as required by the projection
    theorem 2.2.10. These supporting facts use the existing compact
    norm balls and the sealed countable closed-linear-span laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals topology.
From Federer Require Import ModuleQuotient Hom RealNormUP NormMetric LinearBasis Annihilator
  FiniteNormBoundedCompact CompleteMetricUP CompactCauchyLimits MetricClosedBalls
  ClosedLinearSpanUP ClosedLinearSpanSealed MetricSubsetBackground MetricSubsetDenseImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_norm_metric_complete]: completeness of
    finite-dimensional X, supporting the Borel projection in
    3.1.1, p. 211. A compact closed ball contains an eventual
    Cauchy tail; dimension zero requires no exception. *)
Theorem finite_norm_metric_complete (R : realType) (X : lmodType R)
    (N : X -> R) (hN : is_real_norm N) n (e : 'I_n -> X) :
  is_basis e -> is_complete_metric_space (real_norm_metric_space hN).
Proof.
move=> he F PF hc.
pose E := real_norm_metric_space hN.
have [a ha] := proj1 (@cauchyP R E F PF) hc 1 ltr01.
pose K := @metric_closed_ball R E a 1.
have hK : compact K := @finite_norm_metric_boundedly_compact R X N hN n e he a 1 ler01.
have FF : Filter F := @filter_filter _ F PF.
have hFK : F K.
  apply: (@filterS _ F FF _ _ _ ha)=> x hx.
  rewrite ballEmdist in hx; exact: ltW hx.
have [x [_ hx]] := @compact_cauchy_filter_limit R E K F PF hK hFK hc.
by exists x.
Qed.

(** Source for [finite_norm_metric_separable]: separability of
    finite-dimensional X, supporting 3.1.1, p. 211. The closed
    span of its finite basis is the whole space and has a
    countable dense subset by the already proved span laws. *)
Theorem finite_norm_metric_separable (R : realType) (X : lmodType R)
    (N : X -> R) (hN : is_real_norm N) n (e : 'I_n -> X) :
  is_basis e -> exists D : set (real_norm_metric_space hN), countable D /\ dense D.
Proof.
move=> he.
pose D := (fun i => (e i : real_norm_metric_space hN)) @` setT.
have hD : countable D := sub_countable (card_image_le _ _) (countableP _).
pose Z := ClosedLinearSpan.value D.
have hZ := ClosedLinearSpan.laws D.
have hall x : Z x.
  rewrite (@basis_vector_expansion R X n e he x).
  apply: big_ind; [exact: subspace_zero|move=> u v; exact: subspace_add|move=> i _].
  apply: subspace_scale.
  apply: (closed_linear_span_contains hZ); by exists i.
have [H [hc hd]] := ClosedLinearSpan.countable_separable hD.
exists ((fun z : metric_subset (fun x : real_norm_metric_space hN => Z x) =>
  (val z : real_norm_metric_space hN)) @` H).
split; first exact: metric_subset_dense_image_countable hc.
move=> U [a ha] ho.
have hcl := metric_subset_dense_image_closure hd (hall a).
have hn : nbhs a U by rewrite openE in ho; exact: ho a ha.
have [b [hb hbU]] := hcl U hn; by exists b; split.
Qed.
