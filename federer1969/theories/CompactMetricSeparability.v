(** Federer (1969), 2.5.20, p. 114: the compact metric factors have
    countable bases. This supporting general topology argument chooses
    finite covers by shrinking balls, giving a countable dense set without
    assuming an inhabited space. Source context: CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals topology.
From Federer Require Import CompactFiniteCover MetricClosedBalls ArchimedeanReciprocal
  CountableOpenBaseUP SeparableMetricBaseSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_metric_countable_dense_set]: general
    topology supporting the separability requirement in the
    application of 2.5.12 to Federer 2.5.20, p. 114.
    Finite shrinking-ball covers yield a countable dense subset,
    including when the compact metric space is empty. *)
Theorem compact_metric_countable_dense_set (R : realType) (Y : metricType R) :
  compact (@setT Y) -> exists D : set Y, countable D /\ dense D.
Proof.
move=> hY.
have hcover n : exists F : {fset Y}, forall y : Y, exists z, z \in F /\ mdist z y<n.+1%:R^-1.
  pose U z := [set y : Y | mdist z y<n.+1%:R^-1].
  have hc : setT `<=` \bigcup_(z in setT) U z.
    move=> y _; exists y=> //; rewrite /U /= mdistxx invr_gt0 ltr0n; by [].
  have [F hF hf] := @compact_open_finite_cover Y Y setT U setT hY
    (fun z _ => metric_open_ball_open z _) hc.
  exists F=> y; have [z hz hzy] := hf y I; by exists z.
pose F n := projT1 (cid (hcover n)).
have hF n y := projT2 (cid (hcover n)) y.
pose D := \bigcup_n [set` F n].
exists D; split.
- apply: bigcup_countable; first exact: countableP.
  move=> n _; exact: finite_set_countable (finite_fset (F n)).
- move=> U [y hy] hU.
  have hn : nbhs y U by rewrite openE in hU; exact: hU y hy.
  have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP y U) hn.
  have [n hsmall] := real_reciprocal_below he.
  have [z [hz hzy]] := hF n y.
  exists z; split.
  + apply: hb; change (is_true (mdist y z<e)).
    rewrite metric_sym; exact: lt_trans hzy hsmall.
  + by exists n.
Qed.

(** Source for [compact_metric_countable_open_base]: countable
    base for compact metric X or Y in Federer 2.5.20,
    p. 114, obtained from the proved countable dense set
    and the sealed metric-base construction. *)
Theorem compact_metric_countable_open_base (R : realType) (Y : metricType R) :
  compact (@setT Y) -> exists B : nat -> set Y, is_countable_open_base B.
Proof.
move=> hc; have [D [hD hd]] := compact_metric_countable_dense_set hc.
exists (@SeparableMetricBase.value R Y D hD hd).
exact: SeparableMetricBase.laws.
Qed.
