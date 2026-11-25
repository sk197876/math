(** Radius fineness and open localization in Federer (1969), 2.8.15, p. 150.
    The zero-infimum hypothesis concerns positive eligible radii; it
    provides arbitrarily small balls centered at each target point. We
    retain the strict cap of Federer's 2.8.14. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls ExtendedRealBounds NonnegativeInfimumZero
  CenteredBallCoverUP DisjointDenseBallFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [centered_ball_radii]: the radius set in the
    infimum displayed in Federer 2.8.15, p. 150. Positive
    real radii follow the standing parameter convention of 2.8.9,
    p. 146; they are embedded in the extended reals for the
    existing infimum interface. *)
Definition centered_ball_radii (R : realType) (X : metricType R)
    (F : set (set X)) (a : X) : set (\bar R) :=
  [set t | exists r : R, 0 < r /\ F (metric_closed_ball a r) /\ t = r%:E].

(** Source for [has_zero_centered_radius_infimum]: the condition
    inf{r:B(a,r) in F}=0 for every a in A, Federer 2.8.15, p. 150 Infima are
    used only through the previously proved abstract laws. *)
Definition has_zero_centered_radius_infimum (R : realType) (X : metricType R)
    (F : set (set X)) (A : set X) :=
  forall a, A a -> extended_real_inf (centered_ball_radii F a) = 0%E.

(** Source for [has_arbitrarily_small_centered_balls]: the operational
    radius consequence used to form F' in Federer 2.8.15, p. 150 This is a
    supporting formulation; its equivalence with the printed infimum premise
    is proved below. *)
Definition has_arbitrarily_small_centered_balls (R : realType) (X : metricType R)
    (F : set (set X)) (A : set X) :=
  forall a, A a -> forall e : R, 0 < e ->
    exists r, 0 < r < e /\ F (metric_closed_ball a r).

(** Source for [centered_radius_infimum_zero_iff_small_balls]: the passage
    from the zero infimum to small centered balls in Federer 2.8.15, p. 150
    The supporting equivalence includes the empty target, while an empty
    radius family at a target point fails both conditions. *)
Lemma centered_radius_infimum_zero_iff_small_balls (R : realType) (X : metricType R)
    (F : set (set X)) (A : set X) :
  has_zero_centered_radius_infimum F A <-> has_arbitrarily_small_centered_balls F A.
Proof.
have hn a t : centered_ball_radii F a t -> (0 <= t)%E.
  move=> [r [hr [_ ->]]]; rewrite lee_fin; exact: ltW hr.
split.
- move=> hi a ha e he.
  have [t [[r [hr [hF ht]]] hlt]] :=
    (nonnegative_infimum_zero_iff (hn a)).1 (hi a ha) e he.
  exists r; split=> //; apply/andP; split=> //.
  by move: hlt; rewrite ht lte_fin.
- move=> hs a ha; apply: (nonnegative_infimum_zero_iff (hn a)).2.
  move=> e he; have [r [/andP [hr hre] hF]] := hs a ha e he.
  exists r%:E; split; first by exists r.
  by rewrite lte_fin.
Qed.

(** Source for [localized_centered_ball_family]: the restricted family F' in
    Federer 2.8.15, p. 150, with an explicit strict radius cap as in the use
    of 2.8.14. Only balls contained in W and centered on A are retained. *)
Definition localized_centered_ball_family (R : realType) (X : metricType R)
    (F : set (set X)) (A W : set X) (mu : R) :=
  [set B | F B /\ B `<=` W /\ exists a r, A a /\ 0 < r < mu /\ B = metric_closed_ball a r].

(** Source for [localized_centered_balls_small_family]: the
    small-radius family hypothesis for applying 2.8.14 to F'
    in Federer 2.8.15, p. 150. Supporting restriction law. *)
Lemma localized_centered_balls_small_family (R : realType) (X : metricType R)
    (F : set (set X)) (A W : set X) (mu : R) :
  is_small_closed_ball_family mu (localized_centered_ball_family F A W mu).
Proof. move=> B [_ [_ [a [r [_ [hr he]]]]]]; by exists a, r. Qed.

(** Source for [localized_centered_balls_centered_on_target]: F' has its
    centers on A, the separability countability step of Federer 2.8.15, p.
    150 *)
Lemma localized_centered_balls_centered_on_target (R : realType) (X : metricType R)
    (F : set (set X)) (A W : set X) (mu : R) :
  positive_ball_family_centered_on A (localized_centered_ball_family F A W mu).
Proof.
move=> B [_ [_ [a [r [ha [/andP [hr _] he]]]]]]; by exists a, r.
Qed.

(** Source for [fine_centered_balls_open_localization]: every point of A
    intersect W is the center of a member of F', Federer 2.8.15, p. 150
    Choose a radius below both the positive cap and an open-ball
    neighborhood radius; the closed ball then lies in W. *)
Lemma fine_centered_balls_open_localization (R : realType) (X : metricType R)
    (F : set (set X)) (A W : set X) (mu : R) :
  has_arbitrarily_small_centered_balls F A -> open W -> 0 < mu ->
  has_small_centered_balls mu (localized_centered_ball_family F A W mu) (W `&` A).
Proof.
move=> hf hW hm a [haW haA].
have hn : nbhs a W by rewrite openE in hW; exact: hW a haW.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP a W) hn.
have hmin : 0 < Num.min e mu by rewrite lt_min he hm.
have [r [/andP [hr hre] hF]] := hf a haA (Num.min e mu) hmin.
have hmu : r < mu.
  apply: lt_le_trans hre _; by rewrite ge_min lexx orbT.
have her : r < e.
  apply: lt_le_trans hre _; by rewrite ge_min lexx.
exists r; split; first by apply/andP; split.
split=> //; split.
- move=> x hx; apply: hball; exact: le_lt_trans hx her.
- exists a, r; split=> //; split=> //; by apply/andP; split.
Qed.
