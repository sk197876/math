(** Supporting consequences of Federer (1969), 2.8.16, p. 151. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import CoveringRelationUP CoveringFamilyUP NonnegativeInfimumZero MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [covering_relation_fine_iff_small_diameter]: the infimum-zero
    definition in Federer 2.8.16, p. 151, expressed as arbitrarily small
    related diameters. This supporting equivalence uses nonnegativity,
    including empty fibers. *)
Lemma covering_relation_fine_iff_small_diameter (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (x : X) :
  covering_relation_fine_at C x <-> forall e : R, 0 < e ->
    exists S, C x S /\ (extended_metric_diameter S < e%:E)%E.
Proof.
have hn : forall d, covering_relation_diameters C x d -> (0 <= d)%E.
  move=> d [S [_ ->]]; exact: metric_diameter_nonnegative (extended_metric_diameter_specification S).
have h := nonnegative_infimum_zero_iff hn.
split=> hi.
- have hs := h.1 hi; move=> e he.
  have [d [[S [hS ->]] hd]] := hs e he; by exists S.
- apply: h.2=> e he.
  have [S [hS hd]] := hi e he.
  exists (extended_metric_diameter S); split=> //; by exists S.
Qed.

(** Source for [covering_relation_fine_image_cover]: the fine family
    consequence of Federer 2.8.16, p. 151, stated. Each point must be the
    base point of the selected small set. *)
Lemma covering_relation_fine_image_cover (R : realType) (X : metricType R)
    (C : X -> set X -> Prop) (Z : set X) :
  is_covering_relation C -> (forall x, Z x -> covering_relation_fine_at C x) ->
  family_covers_finely (covering_relation_image C Z) Z.
Proof.
move=> hc hf x hx e he.
have [S [hS hd]] := (covering_relation_fine_iff_small_diameter C x).1 (hf x hx) e he.
exists S; split; first by exists x.
split; first exact: hc x S hS.
move=> y hy; rewrite /metric_open_ball.
have hxy := metric_diameter_upper (extended_metric_diameter_specification S) (hc x S hS) hy.
by have := le_lt_trans hxy hd; rewrite lte_fin.
Qed.

(** Source for [covering_relation_fine_mono]: supporting
    monotonicity of the fineness definition in Federer 2.8.16,
    p. 151. Enlarging the fiber preserves arbitrarily small
    related diameters; it need not preserve the Vitali property. *)
Lemma covering_relation_fine_mono (R : realType) (X : metricType R)
    (C D : X -> set X -> Prop) (x : X) :
  (forall S, C x S -> D x S) -> covering_relation_fine_at C x ->
  covering_relation_fine_at D x.
Proof.
move=> hCD /((covering_relation_fine_iff_small_diameter C x).1) hf.
apply: (covering_relation_fine_iff_small_diameter D x).2=> e he.
have [S [hS hd]] := hf e he; exists S; split=> //; exact: hCD.
Qed.

(** Source for [vitali_fine_subrelation]: supporting consequence of the
    definition in Federer 2.8.16, p. 151 A subrelation which remains fine
    everywhere is again a Vitali relation. *)
Lemma vitali_fine_subrelation (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V W : X -> set X -> Prop) :
  is_vitali_relation phi V -> (forall x S, W x S -> V x S) ->
  (forall x, covering_relation_fine_at W x) -> is_vitali_relation phi W.
Proof.
move=> hv hWV hf; constructor=> //.
- move=> x S hS; exact: (@vitali_relation_covering R X phi V hv x S (hWV x S hS)).
- move=> S [x [_ hx]]; apply: (@vitali_relation_borel R X phi V hv S); by exists x; split=> //; exact: hWV x S hx.
- move=> C Z hCW hCfine; apply: (@vitali_relation_selection R X phi V hv C Z) hCfine.
  move=> x S hS; exact: hWV x S (hCW x S hS).
Qed.
