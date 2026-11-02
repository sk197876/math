(** Federer (1969), 2.9.22, p. 167, separability reduction: "Y* are
    separable" when Y is separable and reflexive. We prove the required dual
    separability, rather than assuming a countable norm-dense dual family.
    The proof uses unit norming functionals, the closed-span interface, and
    Hahn–Banach separation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric
  ContinuousDualUP ContinuousDualNorm ContinuousBidualUP DenseNormingFunctionals
  ClosedLinearSpanUP ClosedLinearSpanSealed MetricSubsetBackground MetricSubsetDenseImage
  ReflexiveTotalDualSpan.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [separable_reflexive_dual]: supporting complete
    dual-separability assertion in Federer 2.9.22, p. 167.
    A countable dense subset of Y yields a countable total
    norming family in Y*. Its closed linear span is Y* by
    reflexivity, and the already proved countable-span theorem
    supplies a countable norm-dense dual subset. No finite
    dimension, explicit basis, or additional project axiom is used. *)
Theorem separable_reflexive_dual (R : realType)
    (E D B : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B) (C : set (real_norm_metric_space hN)) :
  is_bidual_embedding ed eb tau -> is_reflexive_embedding tau ->
  countable C -> dense C ->
  exists F : set (real_norm_metric_space (continuous_dual_norm_is_norm hD)),
    countable F /\ dense F.
Proof.
move=> ht hr hCc hCd.
have [k hk] := dual_norming_family_exists hD.
pose F : set (real_norm_metric_space (continuous_dual_norm_is_norm hD)) := k @` C.
have hFc : countable F := sub_countable (card_image_le _ _) hCc.
pose Z := ClosedLinearSpan.value F.
have hZ := ClosedLinearSpan.laws F.
have htotal y : (forall a, F a -> ed a y=0) -> y=0.
  move=> hy; apply: (dense_norming_family_separates hk hCd)=> c hc.
  apply: hy; by exists c.
have hZall := @reflexive_total_dual_closed_span R E D B N hN ed DN hD eb BN hB
  tau F Z ht hr (closed_linear_span_closed hZ) (closed_linear_span_contains hZ) htotal.
have [H [hHc hHd]] := ClosedLinearSpan.countable_separable hFc.
pose j (z : metric_subset (fun a : real_norm_metric_space (continuous_dual_norm_is_norm hD) => Z a)) :=
  (val z : real_norm_metric_space (continuous_dual_norm_is_norm hD)).
exists (j @` H); split; first exact: metric_subset_dense_image_countable hHc.
move=> U [a ha] ho.
have hcl := metric_subset_dense_image_closure hHd (hZall a).
have hn : nbhs a U by rewrite openE in ho; exact: ho a ha.
have [b [hb hbU]] := hcl U hn.
by exists b; split.
Qed.
