(** Federer (1969), 2.10.1, p. 170: replace a uniform mesh restriction by
    refinement of each open cover. The cited paper is [F12], not [F11], by
    the local erratum, page 3, book p. 170 lines 24 and 35: Federer, On
    Lebesgue area (1955) Its proof partitions the covered set into Borel
    pieces on which a sufficiently small mesh refines the given cover. These
    supporting open layers use reciprocal-radius balls to obtain such pieces
    without first choosing a countable subcover. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import MetricClosedBalls MetricOpenShrinking MetricDiameterUP MetricDiameter
  ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_open_cover_layer]: supporting local-mesh
    layer for Federer 2.10.1, p. 170, and the corrected
    reference Federer1955 Theorem 2.5, pp. 291–292. A
    point lies in a reciprocal-radius ball whose doubled
    closed ball is contained in a member of the given cover.
    These layers replace the paper's two-index Borel layers
    while serving the same uniform-refinement step. *)
Definition metric_open_cover_layer (R : realType) (X : metricType R)
    (H : set (set X)) (n : nat) : set X := [set x | exists U : set X, exists c : X,
  H U /\ metric_closed_ball c (2*(n.+1%:R)^-1) `<=` U /\ mdist c x<(n.+1%:R)^-1].

(** Source for [metric_open_cover_layer_open]: supporting
    Borel-layer assertion in the open-refinement proof cited by
    Federer 2.10.1, p. 170. Each layer is a union of
    open balls. No countability or separability of X is used. *)
Lemma metric_open_cover_layer_open (R : realType) (X : metricType R)
    (H : set (set X)) n : open (metric_open_cover_layer H n).
Proof.
rewrite openE=> x [U [c [hU [hsub hcx]]]].
apply: (proj2 (metricType_numDomainType.nbhs_mdistP x _)).
exists ((n.+1%:R)^-1-mdist c x); first by rewrite /= subr_gt0.
move=> y hy; exists U,c; split=> //; split=> //.
apply: le_lt_trans (metric_triangle c x y) _.
have hh := ler_ltD (lexx (mdist c x)) hy.
by rewrite addrCA subrr addr0 in hh.
Qed.

(** Source for [metric_open_cover_layers_cover]: supporting
    exhaustion by Borel pieces in Federer 2.10.1, p. 170,
    corrected reference Federer1955 Theorem 2.5, pp. 291–292.
    A positive closed-ball neighbourhood inside any covering
    member contains a doubled reciprocal-radius ball. *)
Lemma metric_open_cover_layers_cover (R : realType) (X : metricType R)
    (H : set (set X)) (A : set X) :
  (forall U, H U -> open U) -> A `<=` \bigcup_(U in H) U ->
  A `<=` \bigcup_n metric_open_cover_layer H n.
Proof.
move=> hopen hcover x hx; have [U hU hxU] := hcover x hx.
have [r [hr hsub]] := @metric_open_contains_closed_ball R X U x (hopen U hU) hxU.
have hr2 : 0<r/2 by rewrite divr_gt0 // ltr0n.
have [n hn] := positive_reciprocal_nat_small hr2.
have hd : (0 : R)<(n.+1%:R)^-1 by rewrite invr_gt0 ltr0n.
exists n; first exact I.
exists U,x; split=> //; split; last by rewrite mdistxx.
move=> y hy; apply: hsub.
change (mdist x y<=r).
have h2d : 2*(n.+1%:R)^-1<=r.
  rewrite mulrC; apply: ltW; by move: hn; rewrite ltr_pdivlMr ?ltr0n.
exact: le_trans hy h2d.
Qed.

(** Source for [metric_open_cover_layer_refinement]: supporting
    mesh-to-open-refinement implication in Federer 2.10.1,
    p. 170, corrected reference Federer1955 Theorem 2.5,
    p. 292. Any set meeting a layer and with diameter at
    most its reciprocal radius is contained in a covering member. *)
Lemma metric_open_cover_layer_refinement (R : realType) (X : metricType R)
    (H : set (set X)) (n : nat) (S : set X) :
  (extended_metric_diameter S<=((n.+1%:R)^-1 : R)%:E)%E ->
  (exists x, S x /\ metric_open_cover_layer H n x) ->
  exists U, H U /\ S `<=` U.
Proof.
move=> hd [x [hx [U [c [hU [hsub hcx]]]]]].
exists U; split=> // y hy; apply: hsub.
have hxy : mdist x y<=(n.+1%:R)^-1.
  have hh := le_trans (metric_diameter_upper (extended_metric_diameter_specification S) hx hy) hd.
  by move: hh; rewrite lee_fin.
have hh := le_lt_trans (metric_triangle c x y) (ltr_leD hcx hxy).
have he : (n.+1%:R)^-1+(n.+1%:R)^-1=(2*(n.+1%:R)^-1 : R) by ring.
rewrite he in hh; exact: ltW hh.
Qed.
