(** Scalar convex-section lengths supporting Federer (1969), 2.10.30, p.
    195, the assertion that convexity is preserved by Steiner
    symmetrisation. A bounded nonempty convex scalar section has length
    equal to its supremum minus its infimum, whether or not its endpoints
    belong to it. The scalar Lebesgue and convexity ingredients are already
    proved within the project. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CoveringFamilyUP MetricBoundedUnion
  InnerConvex ScalarConvexLength LebesgueScalarMeasure LebesgueDiameterBound ScalarBoundedLength
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_scalar_order_bounds]: supporting
    finite section endpoints for 2.10.30, p. 195.
    Empty sets are allowed in this boundedness statement. *)
Lemma bounded_scalar_order_bounds (R : realType) (A : set (real_line_metric R)) :
  metric_set_bounded A -> has_lbound A /\ has_ubound A.
Proof.
move=> hb.
have [r [hr hA]] := @metric_bounded_distance_bound R [the metricType R of real_line_metric R] A 0 hb.
have hnorm t : A t -> `|t|<=r.
  by move=> ht; move: (hA t ht); rewrite real_line_metric_distanceE sub0r normrN.
split; [exists (-r)|exists r]; move=> t ht;
  have /andP[h1 h2] : -r<=t<=r by rewrite -ler_norml; exact: hnorm t ht.
- exact h1.
- exact h2.
Qed.

(** Source for [scalar_convex_section_length]: supporting
    exact length of a bounded convex scalar section
    in 2.10.30, p. 195. No closedness or
    attained-endpoint hypothesis is introduced. *)
Theorem scalar_convex_section_length (R : realType) (A : set (real_line_metric R)) :
  @is_inner_convex R R^o A -> A !=set0 -> metric_set_bounded A ->
  lebesgue_scalar_measure A=(sup A-inf A)%:E.
Proof.
move=> hC hne hb.
have [hlo hhi] := bounded_scalar_order_bounds hb.
have [x hx] := hne.
have hlow := ge_inf hlo hx.
have hupp := sup_upper_bound (conj hne hhi) hx.
have hab : inf A<=sup A := le_trans hlow hupp.
have hsub : A `<=` `[inf A,sup A].
  move=> z hz; rewrite /= in_itv /=; apply/andP; split.
  - exact (ge_inf hlo hz).
  - exact (sup_upper_bound (conj hne hhi) hz).
have hup := @measure_mono R R (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
  A `[inf A,sup A] hsub.
rewrite (lebesgue_scalar_segment hab) in hup.
pose d := fine (lebesgue_scalar_measure A).
have hfin : lebesgue_scalar_measure A \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (lebesgue_scalar_is_measure R) A)).
  exact: scalar_bounded_length_finite hb.
have hd : lebesgue_scalar_measure A=d%:E by rewrite /d fineK.
have htop a : A a -> sup A<=a+d.
  move=> ha; apply (ge_sup hne); move=> b hbA.
  have hh := real_convex_pair_length_bound hC hbA ha.
  rewrite hd lee_fin in hh.
  have hba := le_trans (ler_norm (b-a)) hh; lra.
have hbot : lbound A (sup A-d).
  move=> a ha; have hh := htop a ha; lra.
have hh := lb_le_inf hne hbot.
apply/eqP; rewrite hd eqe eq_le; apply/andP; split.
- by move: hup; rewrite hd lee_fin.
- lra.
Qed.

(** Source for [nonnegative_multiple_supremum_bound]: supporting
    passage from all scalar section points to their
    supremum in the convexity proof of 2.10.30,
    p. 195. Zero coefficients are handled explicitly. *)
Lemma nonnegative_multiple_supremum_bound (R : realType) (A : set R) (a b : R) :
  A !=set0 -> 0<=a -> (forall x, A x -> a*x<=b) -> a*sup A<=b.
Proof.
move=> hne ha hbound; case: (eqVneq a 0)=> [haE|ha0].
- have [x hx] := hne; have hh := hbound x hx.
  rewrite haE mul0r in hh; rewrite haE mul0r; exact hh.
have hap : 0<a by rewrite lt_neqAle eq_sym ha0 ha.
have hu : ubound A (b/a).
  by move=> x hx; rewrite ler_pdivlMr // mulrC; exact: hbound x hx.
have hh := ge_sup hne hu.
by rewrite mulrC -ler_pdivlMr.
Qed.

(** Source for [nonnegative_multiple_infimum_bound]: supporting
    passage to the lower scalar section endpoint for
    convexity in 2.10.30, p. 195. Zero
    coefficients and unattained infima are included. *)
Lemma nonnegative_multiple_infimum_bound (R : realType) (A : set R) (a b : R) :
  A !=set0 -> 0<=a -> (forall x, A x -> b<=a*x) -> b<=a*inf A.
Proof.
move=> hne ha hbound; case: (eqVneq a 0)=> [haE|ha0].
- have [x hx] := hne; have hh := hbound x hx.
  rewrite haE mul0r in hh; rewrite haE mul0r; exact hh.
have hap : 0<a by rewrite lt_neqAle eq_sym ha0 ha.
have hl : lbound A (b/a).
  by move=> x hx; rewrite ler_pdivrMr // mulrC; exact: hbound x hx.
have hh := lb_le_inf hne hl.
by rewrite mulrC -ler_pdivrMr.
Qed.
