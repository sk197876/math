(** Supporting lower continuity in the projection
    parameter for Federer (1969), 2.10.5(2),
    p. 173. An open source has open incidence;
    a compact inner approximant of one projected
    image remains in all sufficiently nearby
    projected images by a compact product tube.
    The resulting lower continuity holds for all
    open sources, including unbounded ones. It
    supplies part of the printed bounded open
    convex continuity claim without assuming the
    forward theorem 3.2.36, p. 272. Source
    editions and supporting Radon reference:
    OpenProjectionIncidence.v and
    EuclideanLebesgueCompactInner.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanProjectionMetric ProjectedVolumeIncidence OpenProjectionIncidence
  ProjectedVolumeMeasurability EuclideanLebesgueCompactInner EuclideanLebesgueDimensions
  MeasureBasic CompactProductTube TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [open_euclidean_projected_image]:
    supporting openness of p(S), from 1.7.4,
    p. 30, for the continuity assertion of
    Federer 2.10.5(2), p. 173. It is
    the fixed-parameter section of open incidence. *)
Lemma open_euclidean_projected_image (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : euclidean_projection_space R n m) :
  open S -> open (euclidean_projection_linear p @` S :
    set (inner_metric_space (@euclidean_inner_productP R m))).
Proof.
move=> hS.
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose P := euclidean_projection_space R n m.
have hi : continuous (fun y : Y => y) by move=> y; exact: cvg_id.
have hc := @topological_pair_continuous Y Y P (fun y => y) (fun _ => p)
  hi (@cst_continuous Y P p).
rewrite -(@projection_incidence_horizontal_section R n m S p).
apply: open_comp (@projection_incidence_open R n m S hS)=> y _.
exact: hc y.
Qed.

(** Source for [projected_volume_lower_neighbourhood]:
    supporting lower continuity of f_S in Federer
    2.10.5(2), p. 173. A finite strict lower
    bound at p persists in an open neighbourhood
    of p; only openness of S is required. *)
Theorem projected_volume_lower_neighbourhood (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : euclidean_projection_space R n m) (b : R) :
  open S -> b%:E<projected_volume_function S p ->
  exists V : set (euclidean_projection_space R n m), open V /\ V p /\
    forall q, V q -> b%:E<projected_volume_function S q.
Proof.
move=> hS hb.
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose P := euclidean_projection_space R n m.
have [K [hK [hKS hvol]]] := @euclidean_open_compact_inner_volume R m
  (euclidean_projection_linear p @` S) b (@open_euclidean_projected_image R n m S p hS) hb.
pose U : set (P*Y) := [set z | projection_incidence S (z.2,z.1)].
have hswap : continuous (fun z : P*Y => (z.2,z.1)).
  exact (@topological_pair_continuous (P*Y)%type Y P (@snd P Y) (@fst P Y)
    (@second_projection_continuous P Y) (@first_projection_continuous P Y)).
have hU : open U.
  apply: open_comp (@projection_incidence_open R n m S hS)=> z _; exact: hswap z.
have hinc y : K y -> U (p,y).
  move=> hy; have [x hx hxy] := hKS y hy.
  exists x; split=> //; exact: esym hxy.
have [V [W [hV [hp [_ [hKW hsub]]]]]] :=
  @compact_product_open_tube P Y p K U hK hU hinc.
exists V; split=> //; split=> // q hq.
apply: lt_le_trans hvol _; apply: (measure_mono (euclidean_lebesgue_is_measure R m)).
rewrite -(@projection_incidence_horizontal_section R n m S q)=> y hy.
exact: hsub (q,y) (conj hq (hKW y hy)).
Qed.

(** Source for [projected_volume_open_superlevel]:
    supporting open strict superlevels for the
    projection-volume function in Federer 2.10.5(2),
    p. 173. This form also applies to infinite
    projected volumes of unbounded open sets. *)
Lemma projected_volume_open_superlevel (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) (b : R) :
  open S -> open [set p : euclidean_projection_space R n m | b%:E<projected_volume_function S p].
Proof.
move=> hS; rewrite openE=> p hp.
have [V [hV [hVp hbound]]] := @projected_volume_lower_neighbourhood R n m S p b hS hp.
have hn : nbhs p V by rewrite openE in hV; exact: hV p hVp.
apply: (@filterS _ (nbhs p) _ V _ _ hn)=> q hq; exact: hbound q hq.
Qed.
