(** Federer (1969), 2.10.36, printed p. 198: after Steiner symmetrisation, a
    chord of length h supplies the two centred endpoints at distance h/2
    from its hyperplane foot. The scalar supporting statement below derives
    that inclusion from convexity and the abstract equal-length laws.
    Compactness is unnecessary for this inclusion. No relevant entry in the
    working erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground InnerConvex ScalarConvexLength
  CenteredSectionUP CenteredSectionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [centered_section_contains_chord_interval]: supporting
    centred-chord inclusion in the convex-hull
    paragraph of 2.10.36, p. 198.
    Any two original scalar endpoints give
    a centred interval with their separation;
    a zero separation is also included. *)
Theorem centered_section_contains_chord_interval (R : realType)
    (A B : set (real_line_metric R)) (s t beta : R) :
  is_centered_section A B -> @is_inner_convex R R^o A ->
  A s -> A t -> 2*`|beta|<=`|s-t| -> B beta.
Proof.
move=> hs hconv hAs hAt hbeta.
have hne : A !=set0 by exists s.
have [r [hr [hlen hmem]]] := centered_section_membership hs hne.
have hh := real_convex_pair_length_bound hconv hAs hAt.
rewrite hlen lee_fin in hh.
apply: (hmem beta).2.
have htwo : 0<(2 : R) by rewrite ltr0n.
have he : r+r= 2*r by ring.
have hb := le_trans hbeta hh.
by move: hb; rewrite he (ler_pM2l htwo).
Qed.
