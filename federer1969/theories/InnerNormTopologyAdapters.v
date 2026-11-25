(** General topology supporting the use of 3.1.13 in Federer
    (1969), 3.1.20, p. 232. The inner-product metric and its
    norm metric have the same neighbourhoods; transfer openness,
    closedness and local finiteness without identifying their
    implementation records. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  NormMetric FiniteNormEquivalence LocallyFiniteFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [inner_norm_openP]: the same open sets in the
    two metric presentations, supporting the coordinate cover in
    Federer 3.1.20, p. 232. General topology adapter. *)
Lemma inner_norm_openP (R:realType) (X:lmodType R) (B:X->X->R)
    (hB:is_inner_product B) (A:set X) :
  @open [the topologicalType of inner_metric_space hB] A <->
  @open [the topologicalType of real_norm_metric_space (inner_norm_real_norm hB)] A.
Proof.
rewrite !openE; split=>ho x hx.
- exact: (inner_real_norm_same_nbhs hB x A).1 (ho x hx).
- exact: (inner_real_norm_same_nbhs hB x A).2 (ho x hx).
Qed.

(** Source for [inner_norm_closedP]: transfer closed selected
    balls between the two ambient metric presentations, supporting
    Federer 3.1.20, p. 232. General topology adapter. *)
Lemma inner_norm_closedP (R:realType) (X:lmodType R) (B:X->X->R)
    (hB:is_inner_product B) (A:set X) :
  @closed [the topologicalType of inner_metric_space hB] A <->
  @closed [the topologicalType of real_norm_metric_space (inner_norm_real_norm hB)] A.
Proof. rewrite -!openC; exact: inner_norm_openP. Qed.

(** Source for [inner_norm_locally_finiteP]: local finiteness
    is independent of the two identical metric presentations,
    supporting the P_i family in Federer 3.1.20, pp. 232–233. *)
Lemma inner_norm_locally_finiteP (R:realType) (X:lmodType R) (B:X->X->R)
    (hB:is_inner_product B) (J:choiceType) (U:set X) (S:set J) (F:J->set X) :
  @is_locally_finite_family_on [the topologicalType of inner_metric_space hB] J U S F <->
  @is_locally_finite_family_on [the topologicalType of real_norm_metric_space (inner_norm_real_norm hB)] J U S F.
Proof.
split=>hLF x hx; have [O [hO [hxO hfin]]]:=hLF x hx; exists O; by split=>//.
Qed.
