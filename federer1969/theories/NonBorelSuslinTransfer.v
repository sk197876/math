(** Federer (1969), 2.2.11, p. 68, final paragraph: transfer the
    sequence-space example through the 2.2.9 embedding. The image remains
    Suslin by 2.2.10 and cannot be Borel, since its continuous inverse image
    would recover the original non-Borel set. Source context:
    CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot classical_sets cardinality reals topology.
From Federer Require Import CompleteMetricUP SuslinSetUP SuslinContinuousImages
  MetricSubsetBackground TopologicalBorel ContinuousBorelPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [injective_continuous_non_borel_suslin_image]:
    supporting transfer in Federer 2.2.11, p. 68.
    An injective continuous map from a complete separable metric
    space to a Hausdorff space takes a Suslin non-Borel subset
    to a Suslin non-Borel subset. Only the source is required
    to be separable. *)
Lemma injective_continuous_non_borel_suslin_image (R : realType) (T : metricType R)
    (Y : topologicalType) (g : T -> Y) (A : set T) :
  is_complete_metric_space T ->
  (exists D : set T, countable D /\ dense D) -> hausdorff_space Y ->
  continuous g -> injective g -> is_suslin_set R A -> ~ borel_set A ->
  is_suslin_set R (g @` A) /\ ~ borel_set (g @` A).
Proof.
move=> hT hsep hY hg hinj hA hnot.
pose f (a : metric_subset A) := g (val a).
have hf : continuous f.
  move=> a; exact: continuous_comp (@metric_subset_inclusion_continuous R T A a) (hg (val a)).
have he : f @` setT = g @` A.
  apply/seteqP; split.
  - move=> y [a _ <-]; exists (val a)=> //; exact: set_valP.
  - move=> y [x hx <-]; exists (@exist T (fun z => z \in A) x (mem_set hx))=> //.
split.
- rewrite -he; exact: (@continuous_suslin_subspace_image R T Y A f hT hsep hA hY hf).
- move=> hb; apply: hnot.
  have hpre := @continuous_borel_preimage T Y g hg (g @` A) hb.
  have heq : g @^-1` (g @` A) = A.
    apply/seteqP; split.
    + move=> x [z hz hez]; have hzx := hinj z x hez; by rewrite -hzx.
    + move=> x hx; by exists x.
  by rewrite heq in hpre.
Qed.
