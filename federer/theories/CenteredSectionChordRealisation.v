(** Scalar chord choices in Federer (1969), 2.10.32, p. 196, the displayed
    original points a'_i,a''_i and b'_i,b''_i. A scalar coordinate alpha in
    a centred compact convex section is realised by two original section
    points separated by 2 alpha. The choices are existential consequences of
    compactness, convexity and the abstract equal-length laws; no section
    construction is unfolded. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground InnerConvex ScalarConvexLength
  LebesgueScalarMeasure CenteredSectionUP CenteredSectionLaws CenteredSectionBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [centered_compact_convex_section_chord]: direct
    supporting choice of gamma_i with both
    gamma_i and gamma_i+2 alpha_i in the
    original scalar section in 2.10.32, p. 196.
    Negative alpha and nonempty zero-length sections
    are included; compactness supplies attained endpoints. *)
Theorem centered_compact_convex_section_chord (R : realType)
    (A B : set (real_line_metric R)) (alpha : R) :
  is_centered_section A B -> compact A -> @is_inner_convex R R^o A -> B alpha ->
  exists gamma : R, A gamma /\ A (gamma+2*alpha).
Proof.
move=> hs hc hconv halpha.
have hneB : B !=set0 by exists alpha.
have hne := (centered_section_support_law hs).2 hneB.
have [a [b [ha [hb [hab hsub]]]]] := compact_scalar_interval_hull hne hc.
have hfill := real_convex_contains_segment hconv ha hb hab.
have hA : A=`[a,b] by apply/seteqP; split.
have hseg : lebesgue_scalar_measure A=(b-a)%:E.
  by rewrite hA lebesgue_scalar_segment.
have [s [hs0 [hlen hm]]] := centered_section_membership hs hne.
have hwidth : s+s=b-a.
  have hh : (s+s)%:E=(b-a)%:E by rewrite -hlen hseg.
  by move/eqP: hh; rewrite eqe=> /eqP.
have hal := (hm alpha).1 halpha.
case: (leP 0 alpha)=> hsign.
- exists a; split=> //; apply: hfill.
  rewrite /= in_itv /=; apply/andP; split.
  + lra.
  + rewrite (ger0_norm hsign) in hal; lra.
- exists b; split=> //; apply: hfill.
  rewrite /= in_itv /=; apply/andP; split.
  + rewrite (ltr0_norm hsign) in hal; lra.
  + lra.
Qed.
