(** Federer (1969), 2.10.40, printed p. 200: the contact-centre set A is
    compact as the projection of the closed contact pairs in compact P. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric
  WeightedBallMinimumUP WeightedBallContactProfiles TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_ball_contact_pairs_closed]: supporting
    closed equality constraint |b-a|=r c in
    2.10.40, p. 200. The equality is the
    zero level of the continuous scalar slack profile. *)
Lemma weighted_ball_contact_pairs_closed (R : realType) n
    (b : inner_metric_space (@euclidean_inner_productP R n)) (c : R) :
  closed [set p : (inner_metric_space (@euclidean_inner_productP R n))*R^o |
    weighted_ball_slack b c p=0].
Proof.
have he : [set p : (inner_metric_space (@euclidean_inner_productP R n))*R^o |
    weighted_ball_slack b c p=0]=
  (@weighted_ball_slack R n b c) @^-1` [set z : R^o | z=0] by [].
rewrite he.
apply: preimage_closed; last exact: closed_eq.
move=> p hp; exact: weighted_ball_slack_continuous.
Qed.

(** Source for [weighted_ball_contact_centres_compact]: direct
    compactness of A in 2.10.40, p. 200.
    No feasibility or minimality premise is needed
    for this closed-pair projection argument. *)
Theorem weighted_ball_contact_centres_compact (R : realType) n
    (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R^o))
    (b : inner_metric_space (@euclidean_inner_productP R n)) (c : R) :
  compact P -> compact (weighted_ball_contact_centres P b c).
Proof.
move=> hP.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose Z := [set p : E*R^o | weighted_ball_slack b c p=0].
have hZ : closed Z := @weighted_ball_contact_pairs_closed R n b c.
have hK : compact (P `&` Z) := compact_closedI hP hZ.
have he : weighted_ball_contact_centres P b c=(@fst E R^o) @` (P `&` Z).
  apply/seteqP; split=> a.
  - move=> [r [hp hc]].
    exists (a,r); last by [].
    split=> //; by rewrite /Z /weighted_ball_slack /= hc subrr.
  - move=> [[x r] [hp hz] <-] /=.
    exists r; split=> //.
    have hh : r*c-inner_norm (@euclidean_inner_productP R n) (b-x)=0 := hz.
    apply/eqP; by rewrite eq_sym -subr_eq0 hh eqxx.
rewrite he; apply: continuous_compact hK.
apply: continuous_subspaceT; exact: first_projection_continuous.
Qed.
