(** Federer (1969), 4.1.24, p. 382: the
    original fixed-K rectifiable group is complete for
    the mass metric. The preceding actual mass Cauchy
    sequence limit and exact opaque carrier image give
    sequential completeness. The independent general-topology
    bridge then proves completeness for every proper
    Cauchy filter. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentMassSealed CurrentMassConvergenceUP
  AdditiveSubgroupRepresentationUP IntegralCurrentGroupSpaces RectifiableCurrentMassMetric
  RectifiableCurrentMassSequenceLimit CompleteMetricUP MetricSequentialCompleteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section RectifiableCurrentMassComplete.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation G:=(@rectifiable_current_mass_metric R h2 n m U hU K).
Local Notation inc:=(@rectifiable_current_inclusion R h2 n m U hU K).
Local Notation hG:=(@rectifiable_current_group_laws R h2 n m U hU K).

(** Source for [rectifiable_current_mass_metric_sequence_complete]:
    every actual mass-metric Cauchy sequence has a
    limit in exactly the original R_(m,K), as used
    in the series proof of 4.1.24, p. 382. *)
Theorem rectifiable_current_mass_metric_sequence_complete (u:nat->G):
  (forall epsilon:R,0<epsilon->exists N,forall i j,
    (N<=i)%N->(N<=j)%N->mdist (u i) (u j)<epsilon)->
  exists z:G,forall epsilon:R,0<epsilon->exists N,forall i,
    (N<=i)%N->mdist z (u i)<epsilon.
Proof.
move=>hCauchy.
have hMember i:=additive_subgroup_representation_member hG (u i).
have hActualCauchy:@is_current_mass_cauchy_sequence R h2 n m U hU (fun i=>inc (u i)).
  move=>epsilon hEpsilon;have[N hN]:=hCauchy epsilon hEpsilon.
  exists N=>i j hNi hNj.
  rewrite (@rectifiable_current_mass_distance_value R h2 n m U hU K (u i) (u j)) lte_fin.
  exact:hN i j hNi hNj.
have[T [hT [hMassLimit hWeak]]]:=@rectifiable_current_mass_cauchy_sequence_limit
  R h2 n m U hU K (fun i=>inc (u i)) hMember hActualCauchy.
have[z hZ]:=additive_subgroup_representation_full hG hT.
exists z=>epsilon hEpsilon;have[N hN]:=hMassLimit epsilon hEpsilon.
exists N=>i hNi;have h:=hN i hNi.
by rewrite -hZ (@rectifiable_current_mass_distance_value R h2 n m U hU K z (u i))
  lte_fin in h.
Qed.

(** Source for [rectifiable_current_mass_complete]: the full
    original mass completeness assertion of 4.1.24,
    p. 382, for every proper Cauchy filter on
    the actual opaque rectifiable group. *)
Theorem rectifiable_current_mass_complete:is_complete_metric_space G.
Proof.
apply:metric_sequentially_complete_is_complete.
exact:rectifiable_current_mass_metric_sequence_complete.
Qed.
End RectifiableCurrentMassComplete.
