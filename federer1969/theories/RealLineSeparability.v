(** Scalar topology for the real-valued corollary in Federer (1969), 2.3.6,
    p. 77: the real line is separable. Source context:
    TietzeNormalisation.v. Rational density is Archimedean real-field
    background, already used in 2.3.2. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [real_line_countable_dense]: supporting separability
    needed to apply Federer 2.3.5 in the real case of 2.3.6,
    p. 77. The dense set is the image of the rational numbers. *)
Lemma real_line_countable_dense (R : realType) :
  exists D : set (real_line_metric R), countable D /\ dense D.
Proof.
exists ((fun q : rat => (ratr q : real_line_metric R)) @` setT); split.
- exact: sub_countable (card_image_le _ _) (countableP _).
- exact: dense_rat.
Qed.
