(** Supporting separability transport for Federer (1969), 2.9.22, p. 167: a
    closed separable linear subspace, with its inherited norm, is the same
    metric subspace used in the separable-range reduction. These adapters
    identify the project's two existing subspace carriers by their inclusion
    values and distances. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals topology.
From Federer Require Import ModuleQuotient SubspaceCarrier RealNormUP NormMetric NormedSubspace
  MetricSubsetBackground SeparableClosedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_subset_subspace_lift]: supporting carrier
    identification for the closed-subspace reduction in Federer
    2.9.22, p. 167. A point of the actual metric subset
    lifts to the vector subspace carrier with the same inclusion. *)
Definition metric_subset_subspace_lift (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (Z : subspace E)
    (x : metric_subset (fun y : real_norm_metric_space hN => Z y)) : subspace_space Z :=
  @subspace_lift R E Z (val x) (set_valP x).

(** Source for [metric_subset_subspace_lift_value]: supporting
    unchanged inclusion value in the subspace reduction of
    Federer 2.9.22, p. 167. No vector value is chosen anew. *)
Lemma metric_subset_subspace_lift_value (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (Z : subspace E)
    (x : metric_subset (fun y : real_norm_metric_space hN => Z y)) :
  subspace_val (metric_subset_subspace_lift x)=val x.
Proof. by []. Qed.

(** Source for [metric_subset_subspace_lift_distance]: supporting
    isometry of the two subspace carriers used for Federer
    2.9.22, p. 167. Both distances are the original
    ambient norm of the difference of their inclusion values. *)
Lemma metric_subset_subspace_lift_distance (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (Z : subspace E)
    (x y : metric_subset (fun z : real_norm_metric_space hN => Z z)) :
  mdist (metric_subset_subspace_lift x : real_norm_metric_space (subspace_norm_laws hN Z))
    (metric_subset_subspace_lift y)=mdist x y.
Proof.
rewrite -(@subspace_norm_inclusion_distance R E N hN Z
  (metric_subset_subspace_lift x) (metric_subset_subspace_lift y)).
by rewrite !metric_subset_subspace_lift_value metric_subset_distanceE.
Qed.

(** Source for [subspace_norm_separable]: supporting transfer
    of the countable dense set in the closed-subspace reduction,
    Federer 2.9.22, p. 167. Separability in the induced
    ambient metric implies separability for the inherited norm
    on the actual vector subspace carrier. *)
Theorem subspace_norm_separable (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (Z : subspace E) :
  (exists D : set (metric_subset (fun y : real_norm_metric_space hN => Z y)), countable D /\ dense D) ->
  exists C : set (real_norm_metric_space (subspace_norm_laws hN Z)), countable C /\ dense C.
Proof.
move=> [D [hDc hDd]].
pose j (x : metric_subset (fun y : real_norm_metric_space hN => Z y)) :
    real_norm_metric_space (subspace_norm_laws hN Z) := metric_subset_subspace_lift x.
exists (j @` D); split; first exact: sub_countable (card_image_le _ _) hDc.
move=> U [w hw] ho.
have hn : nbhs w U by rewrite openE in ho; exact: ho w hw.
have [e he hball] := (metricType_numDomainType.nbhs_mdistP _ _).1 hn.
pose A : set (real_norm_metric_space hN) := fun y => Z y.
pose x : metric_subset A :=
  @exist (real_norm_metric_space hN) (fun y => y \in A)
    (subspace_val w) (mem_set (subspace_valP w)).
have hx : metric_subset_subspace_lift x=w.
  apply: subspace_val_injective; by rewrite metric_subset_subspace_lift_value.
have [a [ha hnear]] := metric_dense_point_near hDd x he.
have hd : mdist w (j a)<e.
  by rewrite -hx /j metric_subset_subspace_lift_distance.
exists (j a); split; first exact: hball (j a) hd.
by exists a.
Qed.
