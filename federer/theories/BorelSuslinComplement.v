(** Federer (1969), 2.2.10, p. 68, final paragraph: in a complete separable
    metric space, Borel sets are exactly the Suslin sets whose complements
    are Suslin. The reverse implication follows from (1) by separating
    closed witnesses; the forward implication uses the Borel representation
    on p. 66. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import CompleteMetricUP SuslinSetUP TopologicalBorel
  BorelSeparation BorelClosedProjection SuslinImageSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_iff_suslin_and_complement_suslin]: direct
    final characterization in Federer 2.2.10, p. 68:
    Borel membership is equivalent to Suslin membership of both
    the set and its complement. Completeness and separability
    are retained for the separation direction. *)
Theorem borel_iff_suslin_and_complement_suslin (R : realType) (T : metricType R)
    (S : set T) : is_complete_metric_space T ->
  (exists H : set T, countable H /\ dense H) ->
  (borel_set S <-> is_suslin_set R S /\ is_suslin_set R (~` S)).
Proof.
move=> hT hsep; split.
- move=> hS; split; apply: metric_borel_suslin=> //; exact: borel_set_complement hS.
- move=> [hS hSC].
  have hid : continuous (@id T) by move=> x; exact: cvg_id.
  have hdis : (id @` S) `&` (id @` ~` S) = set0 by rewrite !image_id setICr.
  have hs := @disjoint_suslin_images_borel_separated R T T id S (~` S)
    hT hsep (@metric_hausdorff R T) hid hS hSC hdis.
  rewrite !image_id in hs.
  have [B [hB [hSB hCB]]] := proj1 (borel_separated_one_separator _ _) hs.
  have he : B = S.
    apply/seteqP; split=> // x hx; apply: contrapT=> hnx; exact: hCB x hnx hx.
  by rewrite -he.
Qed.
