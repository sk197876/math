(** Boundary cases of Federer (1969), 2.10.40, printed pp. 199–200. A family
    with a common prescribed centre has scale zero; at zero scale the
    contact-centre set is exactly the minimum centre. These consequences use
    the public order laws alone. Source context: WeightedBallMinimumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric WeightedBallMinimumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_ball_common_centre_minimum]: supporting
    zero-scale boundary of 2.10.40, pp. 199–200.
    If all prescribed centres coincide, the minimum
    scale is zero and its centre is that common point.
    The radii need not be equal; compactness is unnecessary
    once the abstract minimum laws are supplied. *)
Lemma weighted_ball_common_centre_minimum (R : realType) n P D
    (a : inner_metric_space (@euclidean_inner_productP R n)) :
  P !=set0 -> @is_weighted_ball_minimum R n P D ->
  (forall p, P p -> p.1=a) ->
  weighted_minimum_scale D=0 /\ weighted_minimum_centre D=a.
Proof.
move=> hne hD hsame.
have hz : weighted_ball_centres P 0 a.
  by move=> p hp; rewrite (hsame p hp) subrr inner_norm0 mulr0.
have hle := @weighted_minimum_least_law R n P D hD 0 a (lexx 0) hz.
have hc : weighted_minimum_scale D=0.
  by apply/eqP; rewrite eq_le hle (weighted_minimum_scale_nonnegative_law hD).
split=> //.
have [p hp] := hne.
have hh := weighted_minimum_feasible_law hD hp.
rewrite (hsame p hp) hc mulr0 in hh.
have hnorm : inner_norm (@euclidean_inner_productP R n) (weighted_minimum_centre D-a)=0.
  by apply/eqP; rewrite eq_le hh (inner_norm_nonnegative _ _).
apply/eqP; by rewrite -subr_eq0 -(inner_norm_eq0 (@euclidean_inner_productP R n)) hnorm eqxx.
Qed.

(** Source for [weighted_ball_zero_scale_contacts]: supporting
    zero-scale boundary of the contact-hull conclusion
    in 2.10.40, pp. 199–200. For a nonempty
    family and a feasible zero scale, the actual
    contact-centre set is the singleton feasible centre. *)
Lemma weighted_ball_zero_scale_contacts (R : realType) n P
    (b : inner_metric_space (@euclidean_inner_productP R n)) :
  P !=set0 -> weighted_ball_centres P 0 b -> weighted_ball_contact_centres P b 0=[set b].
Proof.
move=> hne hb.
have hsame p : P p -> p.1=b.
  move=> hp; have hh := hb p hp.
  rewrite mulr0 in hh.
  have hz : inner_norm (@euclidean_inner_productP R n) (b-p.1)=0.
    by apply/eqP; rewrite eq_le hh (inner_norm_nonnegative _ _).
  apply/eqP; by rewrite eq_sym -subr_eq0 -(inner_norm_eq0 (@euclidean_inner_productP R n)) hz eqxx.
apply/seteqP; split=> a.
- move=> [r [hp _]]; exact: hsame (a,r) hp.
- move=> ->; have [p hp] := hne.
  exists p.2; split; last by rewrite subrr inner_norm0 mulr0.
  have he : (b,p.2)=p by rewrite -(hsame p hp) -surjective_pairing.
  by rewrite he.
Qed.
