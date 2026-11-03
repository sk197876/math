(** Federer (1969), 3.2.41, printed p. 278, compact
    approximation: replace each actual closed grid cube by
    its proper open interior, with an actual null remainder. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry
  EuclideanOpenCoordinateBoxUP EuclideanOpenCoordinateBoxMeasure EuclideanOpenBoxMeasurability
  FiniteMeasureSetDifference MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coordinate_cube_open_box_interior_exists]: supporting
    actual open grid boxes for Federer 3.2.41, p. 278. Their
    coordinate membership is specified first. The closed/open
    product-volume identities prove the omitted remainder null,
    including the empty-coordinate positive atom. *)
Lemma coordinate_cube_open_box_interior_exists (R:realType) n (a:R_n R n) (h:R)
    (Q:set (inner_metric_space (@euclidean_inner_productP R n))):
  0<h ->is_euclidean_coordinate_cube a h Q ->
  exists P,
    is_euclidean_open_coordinate_box a ([ffun i=>a i+h]:R_n R n) P /\
    P `<=` Q /\@euclidean_lebesgue_measure R n (Q `\` P)=0%E.
Proof.
move=> hh hQ.
pose b:R_n R n:=[ffun i=>a i+h].
have hProper i:a i<b i by rewrite /b ffunE ltrDl.
have [P hP]:=euclidean_open_coordinate_box_exists hProper.
have hSub:P `<=` Q.
  move=> x hx; apply:(hQ.2 x).2=> i.
  have /andP[hLow hHigh]:=(hP.2 x).1 hx i; rewrite /b ffunE in hHigh.
  apply/andP; split; exact:ltW.
have hVolumeP:@euclidean_lebesgue_measure R n P=(h^+n)%:E.
  rewrite (open_coordinate_box_volume hP).
  have hProduct:(\prod_i (b i-a i))=\prod_(i:'I_n) h.
    apply:eq_bigr=> i _; by rewrite /b ffunE addrAC subrr add0r.
  by rewrite hProduct prodr_const card_ord.
have hMeasP:=open_coordinate_box_measurable hP.
have hDifference:=@finite_measure_nested_difference R _ (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) P Q (h^+n) (h^+n) hMeasP hSub hVolumeP
  (coordinate_cube_volume hQ).
rewrite subrr in hDifference.
exists P; split; first exact hP.
by split.
Qed.
