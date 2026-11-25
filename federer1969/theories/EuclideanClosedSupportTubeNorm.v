(** Federer (1969), 4.1.18, pp. 375–376:
    closed support tubes in the actual current
    norm topology. Reuse the original opaque set
    sum and nearest-point distance identity; empty
    supports remain empty.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology num_normedtype.
From Federer Require Import RealNormUP NormMetric InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteNormEquivalence InnerNormTopologyAdapters
  EuclideanClosedSupportTube MetricSetDistanceSealed MetricSetDistanceContinuity
  MetricSetDistanceUP RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_norm_compact_topology_iff]: compactness
    depends only on the identical norm and inner
    product neighbourhoods, by 2.7.16, p. 134,
    supporting the actual current tubes of 4.1.18. *)
Theorem inner_norm_compact_topology_iff (R:realType) (X:lmodType R)
    (B:X->X->R) (hB:is_inner_product B) (A:set X):
  @compact (inner_metric_space hB) A <->
  @compact (real_norm_metric_space (inner_norm_real_norm hB)) A.
Proof.
pose IT:=inner_metric_space hB.
pose NT:=real_norm_metric_space (inner_norm_real_norm hB).
have hIN:continuous (fun x:IT=>(x:NT)).
  move=>x O hO;exact:(@inner_real_norm_same_nbhs R X B hB x O).2 hO.
have hNI:continuous (fun x:NT=>(x:IT)).
  move=>x O hO;exact:(@inner_real_norm_same_nbhs R X B hB x O).1 hO.
have hImage:(fun x:X=>x) @` A=A.
  apply:funext=>x;apply:propext;split.
  - by move=>[y hy <-].
  - move=>hx;exists x;by [].
split=>hA;rewrite -hImage.
- exact:continuous_compact (continuous_subspaceT hIN) hA.
- exact:continuous_compact (continuous_subspaceT hNI) hA.
Qed.

Section EuclideanClosedSupportTubeNorm.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NT:=(real_norm_metric_space (inner_norm_real_norm hB)).
Local Notation IT:=(inner_metric_space hB).

(** Source for [euclidean_closed_support_tube_norm_closed]:
    the literal closed epsilon neighbourhood of a
    closed current support is closed, Federer
    4.1.18, p. 375. The empty case requires
    no point or distance to an empty set. *)
Theorem euclidean_closed_support_tube_norm_closed (A:set X) r:
  @closed NT A->@closed NT (@euclidean_closed_support_tube R n A r).
Proof.
move=>hA.
case:(pselect (A=set0))=>[->|hNonempty].
- rewrite euclidean_closed_support_tube_empty;exact:closed0.
- have hNE:(A:set IT)!=set0.
    apply:contrapT=>hEmpty;apply:hNonempty.
    apply:funext=>x;apply:propext;split;last by move=>[].
    by move=>hx;apply:hEmpty;exists x.
  pose d:=@MetricSetDistance.value R IT A hNE.
  have hD:=@MetricSetDistance.laws R IT A hNE.
  have hClosedInner:@closed IT A:=(inner_norm_closedP hB A).2 hA.
  apply:(inner_norm_closedP hB _).1.
  rewrite (@euclidean_closed_support_tube_distance R n A d r hClosedInner hNE hD).
  apply:((@continuous_closedP [the topologicalType of IT]
    [the topologicalType of real_line_metric R] d).1
    (@metric_set_distance_continuous R IT A d hD) [set t|t<=r]).
  exact:closed_le.
Qed.

(** Source for [euclidean_closed_support_tube_norm_compact]:
    finite-radius tubes of compact supports are
    compact in the actual current domain topology,
    Federer 4.1.18, pp. 375–376. *)
Theorem euclidean_closed_support_tube_norm_compact (A:set X) r:
  @compact NT A->@compact NT (@euclidean_closed_support_tube R n A r).
Proof.
move=>hA;apply:(inner_norm_compact_topology_iff hB _).1.
apply:euclidean_closed_support_tube_compact.
exact:(inner_norm_compact_topology_iff hB A).2 hA.
Qed.
End EuclideanClosedSupportTubeNorm.
