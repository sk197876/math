(** General-topology connections for the project test of
    Federer 2.10.11, p. 176. Reuse the original binary product's
    compactness, then the existing compact metric completeness and
    separability theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import BinarySequenceCylinders BinaryCylinderPrefixLaws
  BinaryPrefixDistanceUP BinaryPrefixMetric DyadicScaleBounds
  CompactCauchyLimits CompleteMetricUP CompactMetricSeparability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_prefix_identity_continuous]: finite-prefix
    topology connection for the project example testing Federer
    2.10.11, p. 176. No metric compactness is assumed. *)
Lemma binary_prefix_identity_continuous (R:realType):
  continuous (fun x:binary_sequence_space=>(x:binary_prefix_metric R)).
Proof.
move=> a U hU.
have [e he hball]:=proj1 (metricType_numDomainType.nbhs_mdistP
  (a:binary_prefix_metric R) U) hU.
have [n hn]:=dyadic_sides_arbitrarily_small he.
pose C:=binary_cylinder (binary_sequence_prefix n a).
have hC:C a:=@binary_sequence_in_prefix n a.
have hOpen:open C:=binary_cylinder_open _.
apply:filterS _ (open_nbhs_nbhs (conj hOpen hC)).
move=> x hx;apply:hball.
have hp:binary_common_prefix n a x.
  move=> k hk.
  have hkn:(k<size (binary_sequence_prefix n a))%N by rewrite size_tuple.
  have h1:=@binary_sequence_in_prefix n a k hkn.
  have h2:=hx k hkn.
  exact:eq_trans h1 (esym h2).
apply:le_lt_trans _ hn.
exact (@binary_prefix_distance_prefix_bound R (@BinaryPrefixDistance.distance R)
  (BinaryPrefixDistance.laws R) n a x hp).
Qed.

(** Source for [binary_prefix_metric_compact]: compactness of the
    actual project test space for Federer 2.10.11, p. 176, by the
    existing binary-product compactness and the identity map. *)
Lemma binary_prefix_metric_compact (R:realType):
  compact (@setT (binary_prefix_metric R)).
Proof.
have h:=continuous_compact (continuous_subspaceT
  (@binary_prefix_identity_continuous R)) binary_sequence_compact.
have he:(fun x:binary_sequence_space=>(x:binary_prefix_metric R)) @` setT=setT.
  apply/seteqP;split=> // x _;by exists x.
by rewrite he in h.
Qed.

(** Source for [binary_prefix_metric_complete]: the original
    completeness hypothesis in the project test of Federer 2.10.11,
    p. 176, follows from proved compactness. *)
Lemma binary_prefix_metric_complete (R:realType):
  is_complete_metric_space (binary_prefix_metric R).
Proof. exact:compact_metric_space_complete (@binary_prefix_metric_compact R). Qed.

(** Source for [binary_prefix_metric_separable]: the original
    separability hypothesis in the project test of Federer 2.10.11,
    p. 176, follows from proved compactness. *)
Lemma binary_prefix_metric_separable (R:realType):exists D:set (binary_prefix_metric R),
  countable D /\ dense D.
Proof. exact:compact_metric_countable_dense_set (@binary_prefix_metric_compact R). Qed.
