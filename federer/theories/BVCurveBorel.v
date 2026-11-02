(** Federer (1969), 2.9.22, pp. 167–168: measurable norm derivatives are
    needed for the vector-integral extension of 2.9.20(1), p. 165. Locally
    BV curves have countably many discontinuities by 2.5.16, p. 109, so they
    are Borel maps; difference quotients can then be used in the proved
    measurable- limit theorem of 2.3.2(6), pp. 73–74. These are supporting
    Borel arguments, not a new derivative-existence assertion. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals topology.
From Federer Require Import TopologicalBorel BorelFamilyBasic BorelFunctionUP
  RealMetricBackground CompleteMetricUP CurveArcLength CurveDiscontinuities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_metric_set_borel]: supporting Borel
    exception-set fact in Federer 2.9.22, pp. 167–168, from
    closed singletons and countable unions in 2.2.1, p. 60.
    It is used for the discontinuities of 2.5.16, p. 109. *)
Lemma countable_metric_set_borel (R : realType) (X : metricType R) (A : set X) :
  countable A -> borel_set A.
Proof.
move=> hA.
have he : A=\bigcup_(x in A) [set x].
  apply/seteqP; split; first by move=> x hx; exists x.
  by move=> x [y hy ->].
rewrite he; apply: borel_set_countable_union hA _=> x hx.
apply: closed_borel_set; apply: accessible_closed_set1.
apply: hausdorff_accessible; exact: metric_hausdorff.
Qed.

(** Source for [countably_discontinuous_map_borel]: supporting
    measurability in Federer 2.9.22, pp. 167–168, using
    2.2.14, p. 70, and the discontinuities of 2.5.16, p. 109.
    For an open target set, remove the interior of its inverse
    image; the remaining points are among the countable exceptions.
    No separability of the target is needed. *)
Theorem countably_discontinuous_map_borel (R : realType) (X : metricType R)
    (Y : topologicalType) (f : X -> Y) (D : set X) :
  countable D -> (forall x, ~D x -> f @ x --> f x) -> is_borel_function f.
Proof.
move=> hD hf U hU.
pose A := f @^-1` U.
pose V := interior A.
have hV : open V := open_interior A.
have hE : countable (A `\` V).
  apply: sub_countable _ hD; apply: subset_card_le=> x [hx hn].
  apply: contrapT=> hxD; apply: hn.
  have hnb : nbhs (f x) U by rewrite openE in hU; exact: hU (f x) hx.
  exact: (hf x hxD) U hnb.
have he : A=V `|` (A `\` V).
  apply/seteqP; split=> x.
  - move=> hx; case: (pselect (V x))=> h; [by left|right; by split].
  - move=> [hx|[hx _]]=> //; exact: interior_subset hx.
change (borel_set A); rewrite he.
exact (@borel_family_binary_union X setT _ (borel_sets_family X) V (A `\` V)
  (open_borel_set hV) (countable_metric_set_borel hE)).
Qed.

(** Source for [complete_metric_bv_curve_borel]: supporting Borel
    measurability for Federer 2.9.22, pp. 167–168, using the
    proved discontinuity theorem of 2.5.16, p. 109. In the
    complete metric target, the countable arc-length jump locus is
    exactly the curve discontinuity locus. In particular this applies
    to the Banach target of the printed theorem. *)
Theorem complete_metric_bv_curve_borel (R : realType) (Y : metricType R) (g : R -> Y) :
  is_complete_metric_space Y -> curve_locally_finite_variation g ->
  is_borel_function (g : real_line_metric R -> Y).
Proof.
move=> hY hg.
apply: (@countably_discontinuous_map_borel R [the metricType R of real_line_metric R]
  Y g (curve_jump_points g)).
- exact (@curve_jump_points_countable R Y g hg).
- move=> x hx; apply: contrapT=> hn; apply: hx.
  exact ((@curve_jump_points_iff R Y g hg hY x).2 hn).
Qed.
