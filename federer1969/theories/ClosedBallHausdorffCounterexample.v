(** Local correction to Federer (1969), 2.10.24, p. 188, the sentence
    asserting Hausdorff closedness of the family of closed balls in a
    boundedly compact metric space. The compact real subspace X=[-1,-1/2]
    union [1/2,1] union {-2,2} is a counterexample. All distances below are
    the restricted real distance. Closed balls with centres 1/2+h and radii
    3/2-2h converge to C=[-1,-1/2] union [1/2,1], which is not a ball in X.
    This corrects that proof remark; it does not disprove the spherical
    integral equality. The local erratum p. 4, book p. 188 line 21, corrects
    the script S notation only. Source context: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import RealMetricBackground CompactSetDistanceProfile MetricSetDistanceUP
  HausdorffDistanceUP HausdorffDistanceBasic HausdorffDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [split_ball_core]: local counterexample
    target for the Hausdorff-closed-ball remark in
    2.10.24, p. 188. It is the union of two
    closed real intervals, separated by a central gap. *)
Definition split_ball_core (R : realType) : set (real_line_metric R) :=
  `[-1,-(2:R)^-1] `|` `[(2:R)^-1,1].

(** Source for [split_ball_space]: local compact ambient
    subspace for the same remark in 2.10.24,
    p. 188. The two isolated outer points obstruct
    every possible centre of a ball equal to the core. *)
Definition split_ball_space (R : realType) : set (real_line_metric R) :=
  (@split_ball_core R `|` [set -2]) `|` [set 2].

(** Source for [is_split_space_positive_closed_ball]: local
    relative-ball specification for 2.10.24, p. 188.
    Centres lie in the specified subspace and the
    radius is strictly positive, as in 2.8.1.
    The distance is exactly the induced real metric. *)
Definition is_split_space_positive_closed_ball (R : realType) (B : set (real_line_metric R)) :=
  exists a r : R, split_ball_space a /\ 0<r /\
    forall x, B x <-> split_ball_space x /\ `|a-x|<=r.

(** Source for [split_ball_interval_bounds]: supporting
    elementary interval identity for the local correction
    to 2.10.24, p. 188; not a claim attributed
    separately to the book. *)
Lemma split_ball_interval_bounds (R : realType) (a b x : R) :
  `[a,b] x <-> a<=x /\ x<=b.
Proof. rewrite /mkset in_itv /=; split; [by move/andP|by move=> [ha hb]; apply/andP]. Qed.

(** Source for [split_ball_core_compact]: local compactness
    check for the counterexample to the closed-ball
    remark in 2.10.24, p. 188. *)
Lemma split_ball_core_compact (R : realType) : compact (@split_ball_core R).
Proof. apply: compactU; exact: segment_compact. Qed.

(** Source for [split_ball_space_compact]: local ambient
    compactness in the correction to 2.10.24, p. 188.
    The induced metric is therefore boundedly compact.
    Only compact intervals and singleton points are used. *)
Lemma split_ball_space_compact (R : realType) : compact (@split_ball_space R).
Proof. apply: compactU; [apply: compactU; [exact: split_ball_core_compact|exact: compact_set1]|exact: compact_set1]. Qed.

(** Source for [split_ball_core_not_closed_ball]: local
    counterexample to the Hausdorff-closed-ball remark
    in 2.10.24, p. 188. A centre in either
    interval needs a radius that also includes one
    isolated outer point; an outer centre includes itself. *)
Theorem split_ball_core_not_closed_ball (R : realType) :
  ~ is_split_space_positive_closed_ball (@split_ball_core R).
Proof.
move=> [a [r [ha [hr hball]]]].
have hleft : @split_ball_core R (-1) by left; apply/split_ball_interval_bounds; split; lra.
have hright : @split_ball_core R 1 by right; apply/split_ball_interval_bounds; split; lra.
have houterL : @split_ball_space R (-2) by left; right.
have houterR : @split_ball_space R 2 by right.
have hnotL : ~ @split_ball_core R (-2).
  move=> [hx|hx]; move/split_ball_interval_bounds: hx=> [h1 h2]; lra.
have hnotR : ~ @split_ball_core R 2.
  move=> [hx|hx]; move/split_ball_interval_bounds: hx=> [h1 h2]; lra.
have hacore : @split_ball_core R a.
  apply/(hball a); split=> //; rewrite subrr normr0; exact: ltW hr.
case: hacore=> /split_ball_interval_bounds [ha1 ha2].
- have hrad := (hball 1).1 hright.
  have hdist : `|1-a|<=r by rewrite -opprB normrN; exact: hrad.2.
  have hrr : 1-a<=r := le_trans (ler_norm _) hdist.
  apply: hnotL; apply/(hball (-2)); split=> //.
  rewrite ler_norml; apply/andP; split; lra.
- have hrad := (hball (-1)).1 hleft.
  have hrr : a+1<=r by have hh := le_trans (ler_norm (a-(-1))) hrad.2; lra.
  apply: hnotR; apply/(hball 2); split=> //.
  rewrite ler_norml; apply/andP; split; lra.
Qed.
