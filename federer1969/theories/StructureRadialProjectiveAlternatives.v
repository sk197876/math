(** Federer (1969), 3.3.4, p. 291:
    the original P_v, Q_v, R_v and their
    actual monotonicity. No measurable hull replaces
    the original source image. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import StructureProjectiveSpace StructureRadialImageMeasure
  StructureRadialImageLaws StructureOpenBallGrowth StructureInfiniteLimitComparison
  PositiveRadiusLimits PositiveRightOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Alternatives.
Variable R:realType.
Variable X:metricType R.
Variable m:nat.
Variable phi:set X->\bar R.
Variables (A D:set X) (a:X) (f:X->structure_projective_space R m).
Local Notation cutoff v:=(((v.+1)%:R:R)^-1).
Local Notation psi v:=(structure_radial_image_measure m phi A a D f (cutoff v)).

(** Source for [structure_radial_projective_zero]: the
    actual P_v in Federer 3.3.4, p. 291:
    the ordinary zero limit of the original
    open-ball costs for the actual psi_v. *)
Definition structure_radial_projective_zero v:set (structure_projective_space R m):=
  [set z|positive_right_extended_order_limit (structure_open_ball_growth m (psi v) z) 0%E].

(** Source for [structure_radial_projective_infinite]: the
    actual Q_v in Federer 3.3.4, p. 291:
    infinite upper limit of the same original
    costs at every positive aperture cutoff. *)
Definition structure_radial_projective_infinite v:set (structure_projective_space R m):=
  [set z|positive_radius_upper_limit (structure_open_ball_growth m (psi v) z)=+oo%E].

(** Source for [structure_radial_projective_image]: the
    original R_v=f[A intersect U(a,1/v) intersect
    domain(f)] in Federer 3.3.4, p. 291.
    Natural v here denotes the positive index v+1. *)
Definition structure_radial_projective_image v:set (structure_projective_space R m):=
  f @` [set x|A x /\ mdist a x<cutoff v /\ D x].

(** Source for [structure_radial_projective_cost_decreases]:
    actual psi_v and their unnormalized open-ball
    costs decrease with v, Federer 3.3.4,
    p. 291. Only the radius supremum domain
    changes, and extended values remain allowed. *)
Lemma structure_radial_projective_cost_decreases i j z t:
  (i<=j)%N ->0<t ->
  (structure_open_ball_growth m (psi j) z t<=
    structure_open_ball_growth m (psi i) z t)%E.
Proof.
move=>hij ht; rewrite /structure_open_ball_growth.
apply:lee_wpmul2r; first by rewrite lee_fin exprn_ge0 // invr_ge0 ltW.
apply:structure_radial_image_cutoff_mono.
by rewrite lef_pV2 ?posrE ?ltr0n // ler_nat.
Qed.

(** Source for [structure_radial_projective_infinite_decreases]:
    Q_v decreases with v in Federer 3.3.4,
    p. 291. An infinite upper limit for
    a smaller numerator forces infinity for
    every larger numerator; no finite bound
    on either numerator is assumed. *)
Lemma structure_radial_projective_infinite_decreases i j:
  (i<=j)%N ->structure_radial_projective_infinite j `<=`
    structure_radial_projective_infinite i.
Proof.
move=>hij z hInfinite.
apply:(@structure_infinite_limit_scaled_comparison R
  (structure_open_ball_growth m (psi j) z)
  (structure_open_ball_growth m (psi i) z) 1 1 1 ltr01 ltr01 ltr01)=>//.
move=>t /andP [ht _]; rewrite mul1r mul1e.
exact:structure_radial_projective_cost_decreases hij ht.
Qed.

(** Source for [structure_radial_projective_image_decreases]:
    R_v decreases with v in Federer 3.3.4,
    p. 291. The original strict source balls
    decrease while f and its actual domain
    remain exactly the same. *)
Lemma structure_radial_projective_image_decreases i j:
  (i<=j)%N ->structure_radial_projective_image j `<=`
    structure_radial_projective_image i.
Proof.
move=>hij; apply:structure_radial_original_images_decrease.
by rewrite lef_pV2 ?posrE ?ltr0n // ler_nat.
Qed.
End Alternatives.
