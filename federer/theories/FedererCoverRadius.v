(** Federer (1969), 3.1.13, p. 224:
    the radius h is one twentieth of the
    supremum of capped complement distances.
    A global zero extension is used only
    as an auxiliary representative; h is
    positive on the union of the cover. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology ring lra.
From Federer Require Import MetricClosedBalls OpenCoverClearanceUP
  OpenCoverClearanceSealed OpenCoverClearanceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_cover_radius]:
    the exact choice lambda= 1/20 in
    Federer 3.1.13, p. 224,
    multiplying the abstract clearance supremum. *)
Definition federer_cover_radius (R : realType) (X : metricType R)
    (Phi : set (set X)) (x : X) :=
  OpenCoverClearance.value Phi x/20.

(** Source for [federer_cover_radius_nonnegative]:
    nonnegativity of the auxiliary global
    radius in Federer 3.1.13, p. 224. *)
Lemma federer_cover_radius_nonnegative (R : realType) (X : metricType R)
    (Phi : set (set X)) x : 0<=federer_cover_radius Phi x.
Proof.
rewrite /federer_cover_radius; apply: divr_ge0; last by rewrite ler0n.
exact: (open_cover_clearance_nonnegative (OpenCoverClearance.laws Phi) x).
Qed.

(** Source for [federer_cover_radius_cap]:
    the cap one in the distance formula
    bounds h by 1/20, supporting the
    bounded selection in Federer 3.1.13, p. 224. *)
Lemma federer_cover_radius_cap (R : realType) (X : metricType R)
    (Phi : set (set X)) x : federer_cover_radius Phi x<=1/20.
Proof.
rewrite /federer_cover_radius.
apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
exact: (open_cover_clearance_cap (OpenCoverClearance.laws Phi) x).
Qed.

(** Source for [federer_cover_radius_positive]:
    h takes strictly positive finite values
    on the open-cover union, Federer
    3.1.13, p. 224. *)
Lemma federer_cover_radius_positive (R : realType) (X : metricType R)
    (Phi : set (set X)) x :
  (forall T, Phi T -> open T) ->
  (exists T, Phi T /\ T x) -> 0<federer_cover_radius Phi x.
Proof.
move=>ho hx; rewrite /federer_cover_radius; apply: divr_gt0; last by rewrite ltr0n.
exact: (open_cover_clearance_positive (OpenCoverClearance.laws Phi) ho hx).
Qed.

(** Source for [federer_cover_radius_lipschitz]:
    Lip(h)<=1/20, as required when applying
    3.1.12 in Federer 3.1.13, p. 224. *)
Lemma federer_cover_radius_lipschitz (R : realType) (X : metricType R)
    (Phi : set (set X)) x y :
  `|federer_cover_radius Phi x-federer_cover_radius Phi y|<=
    (1/20)*mdist x y.
Proof.
rewrite /federer_cover_radius -mulrBl normrM normfV normr_nat div1r [X in _<=X]mulrC.
apply: ler_wpM2r; first by rewrite invr_ge0 ler0n.
exact: (open_cover_clearance_lipschitz (OpenCoverClearance.laws Phi) x y).
Qed.

(** Source for [federer_cover_radius_subordinate_ball]:
    the tenfold radius ball lies in an
    original member of the cover, supporting
    the refinement assertion of Federer
    3.1.13, pp. 224–225. Supremum
    approximation supplies the containing member;
    attainment of the supremum is not assumed. *)
Theorem federer_cover_radius_subordinate_ball (R : realType) (X : metricType R)
    (Phi : set (set X)) x :
  (forall T, Phi T -> open T) ->
  (exists T, Phi T /\ T x) ->
  exists T, Phi T /\ metric_closed_ball x (10*federer_cover_radius Phi x) `<=` T.
Proof.
move=>ho hx.
have hp := open_cover_clearance_positive (OpenCoverClearance.laws Phi) ho hx.
have he : 10*federer_cover_radius Phi x=OpenCoverClearance.value Phi x/2.
  by rewrite /federer_cover_radius; field.
have hr0 : 0<=10*federer_cover_radius Phi x by rewrite he divr_ge0 ?ltW // ler0n.
have hr : 10*federer_cover_radius Phi x<OpenCoverClearance.value Phi x.
  rewrite he; lra.
exact: (open_cover_clearance_subordinate_ball (OpenCoverClearance.laws Phi) hr0 hr).
Qed.
