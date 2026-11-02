(** Scalar length bounds supporting the containing-ball and boundary
    assertions of Federer (1969), 2.10.30, p. 195. Compact scalar sections
    attain their endpoints; full interval length forces both containing
    endpoints to belong to the original section. These are supporting
    lemmas, not separately numbered assertions in the book. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal
  topology num_normedtype normed_module lra.
From Federer Require Import RealMetricBackground CenteredSectionUP CenteredSectionLaws ScalarBoundedLength
  LebesgueScalarMeasure MeasureUP MeasureBasic CompactMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [centered_section_norm_bound]: supporting
    interval containment underlying T contained in the
    closed ball in 2.10.30, p. 195. The
    source section need not be closed or measurable. *)
Lemma centered_section_norm_bound (R : realType) (A B : set (real_line_metric R)) (r : R) :
  is_centered_section A B -> 0<=r ->
  (forall t, A t -> `|t|<=r) -> forall t, B t -> `|t|<=r.
Proof.
move=> h hr hA t ht.
have hB : B !=set0 by exists t.
have hne := (centered_section_support_law h).2 hB.
have [s [hs [hlen hmem]]] := centered_section_membership h hne.
have hh := scalar_length_norm_bound hr hA.
rewrite hlen lee_fin in hh.
have hsr : s<=r by lra.
exact: le_trans ((hmem t).1 ht) hsr.
Qed.

(** Source for [compact_scalar_interval_hull]: supporting
    attained extreme scalar coordinates for compact source
    sections in 2.10.30, p. 195. No claim
    that the source itself is an interval is made. *)
Lemma compact_scalar_interval_hull (R : realType) (A : set (real_line_metric R)) :
  A !=set0 -> compact A ->
  exists a b : R, A a /\ A b /\ a<=b /\ A `<=` `[a,b].
Proof.
move=> hne hc.
have hid : continuous (fun t : real_line_metric R => (t : R^o)) by move=> t.
have hneg : continuous (fun t : real_line_metric R => (-t : R^o)).
  move=> t; exact: (@continuousN R R^o [the topologicalType of real_line_metric R]
    (fun x=>x) t (hid t)).
have [a [ha hmin]] := continuous_compact_maximum hne hc hneg.
have [b [hb hmax]] := continuous_compact_maximum hne hc hid.
have hab := hmax a ha.
exists a,b; split=> //; split=> //; split=> // t ht.
rewrite /= in_itv /=; apply/andP; split; last exact: hmax t ht.
by move: (hmin t ht); rewrite lerN2.
Qed.

(** Source for [compact_scalar_full_length_endpoints]: supporting
    strictness on the boundary sphere in 2.10.30,
    p. 195. A nonempty compact subset of [-r,r]
    with full length contains both endpoints. The
    nonempty hypothesis is essential when r=0. *)
Lemma compact_scalar_full_length_endpoints (R : realType) (A : set (real_line_metric R)) (r : R) :
  A !=set0 -> compact A -> 0<=r ->
  (forall t, A t -> `|t|<=r) ->
  lebesgue_scalar_measure A=(r+r)%:E -> A (-r) /\ A r.
Proof.
move=> hne hc hr hnorm hlen.
have [a [b [ha [hb [hab hsub]]]]] := compact_scalar_interval_hull hne hc.
have hh := @measure_mono R R (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) A `[a,b] hsub.
rewrite hlen (lebesgue_scalar_segment hab) lee_fin in hh.
have /andP[ha0 ha1] : -r<=a<=r by rewrite -ler_norml; exact: hnorm a ha.
have /andP[hb0 hb1] : -r<=b<=r by rewrite -ler_norml; exact: hnorm b hb.
have har : a= -r by lra.
have hbr : b=r by lra.
by rewrite -har -hbr.
Qed.

(** Source for [centered_section_boundary_endpoints]: supporting
    linewise form of the boundary exclusion in
    2.10.30, p. 195. A symmetrised point
    at the containing interval endpoint forces both
    reflected original endpoints to be present. *)
Theorem centered_section_boundary_endpoints (R : realType) (A B : set (real_line_metric R)) (r : R) :
  is_centered_section A B -> compact A -> 0<=r ->
  (forall t, A t -> `|t|<=r) -> B r -> A (-r) /\ A r.
Proof.
move=> h hc hr hnorm hBr.
have hB : B !=set0 by exists r.
have hne := (centered_section_support_law h).2 hB.
have [s [hs [hlen hmem]]] := centered_section_membership h hne.
have hh := scalar_length_norm_bound hr hnorm; rewrite hlen lee_fin in hh.
have hrs : r<=s by move: ((hmem r).1 hBr); rewrite ger0_norm.
have he : s=r by lra.
apply: compact_scalar_full_length_endpoints hne hc hr hnorm _.
by rewrite hlen he.
Qed.
