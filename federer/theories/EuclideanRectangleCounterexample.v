(** The counterexample of Federer (1969), 2.8.20, p. 152: the relation of
    points belonging to products of compact nondegenerate intervals in R^2
    is not an L^2 Vitali relation. The book cites Caratheodory, Vorlesungen
    ueber reelle Funktionen, second edition (1927), pp. 689–692, without
    proof. The local argument uses the positive-core, harmonic-fan and
    summation constructions in Saks1934 Lemma B, pp. 258–259, and
    Cesari1939, pp. 306–307, as detailed in VitaliMassObstruction.v.
    Disjoint group unions are selected by 2.8.7 instead of repeating finite
    packing. The coordinate bijection of 2.6.5, pp. 119–120, transfers the
    measure; continuity transfers based fineness. The conclusion uses the
    book's Euclidean metric. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ScalarPlaneRectangles ScalarMetricPlane ScalarRectangleCounterexample
  EuclideanInnerProduct InnerMetric EuclideanPlaneCoordinates EuclideanPlaneLebesgue
  EuclideanLebesgue EuclideanLebesgueDimensions MeasureUP MeasurePushforward
  PushforwardMeasurableSets MeasureBijectionUP MeasureBijectionLaws
  ContinuousDiameterImages CoveringRelationUP CoveringRelationFineness VitaliMassObstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_rectangle_relation]: the exact
    point/rectangle relation in Federer 2.8.20, p. 152.
    Coordinate products are carried to the standard Euclidean
    plane by the already established two-coordinate bijection. *)
Definition euclidean_rectangle_relation (R : realType)
    (x : inner_metric_space (@euclidean_inner_productP R 2))
    (S : set (inner_metric_space (@euclidean_inner_productP R 2))) :=
  S x /\ exists T : set (scalar_metric_plane R),
    is_nondegenerate_scalar_rectangle T /\ S=(@euclidean_plane_join R) @` T.

(** Source for [federer_2_8_20]: direct formalisation of
    the complete counterexample in Federer 2.8.20, p. 152.
    A continuous coordinate bijection transfers the checked
    mass obstruction to the Euclidean metric and L^2.
    The scalar field may be any realType, an explicit
    generalisation of the book's real-number model. No assumption
    about a differentiation theorem or a rectangle selection is added. *)
Theorem federer_2_8_20 (R : realType) :
  ~ @is_vitali_relation R (inner_metric_space (@euclidean_inner_productP R 2))
      (@euclidean_lebesgue_measure R 2) (@euclidean_rectangle_relation R).
Proof.
have [nu [Z [hn [hmeas [hZ [hcost hf]]]]]] := @scalar_rectangle_mass_obstruction_exists R.
pose P := scalar_metric_plane R.
pose E := inner_metric_space (@euclidean_inner_productP R 2).
pose f := @euclidean_plane_join R.
have hfK := @euclidean_plane_joinK R.
have hfi : injective f := can_inj hfK.
have hpre (A : set P) : f @^-1` (f @` A)=A.
  apply/seteqP; split.
  - move=> x [y hy he]; have hexy : y=x := hfi y x he; by rewrite -hexy.
  - by move=> x hx; exists x.
have hpush : measure_pushforward f (@scalar_plane_lebesgue R)=@euclidean_lebesgue_measure R 2 :=
  measure_bijection_pushforward (measure_bijection_inverse (euclidean_plane_lebesgue_bijection R)).
have hLeb (A : set P) : (@euclidean_lebesgue_measure R 2) (f @` A)=scalar_plane_lebesgue A.
  by rewrite -hpush /measure_pushforward hpre.
pose psi := measure_pushforward f nu.
pose Y := f @` Z.
pose C (y : E) (T : set E) := exists (x : P) (S : set P),
  Z x /\ scalar_rectangle_relation x S /\ 2*scalar_plane_lebesgue S<=nu S /\
    y=f x /\ T=f @` S.
have hpsi : is_measure psi := measure_pushforward_is_measure f hn.
have hCY y T : C y T -> euclidean_rectangle_relation y T.
  move=> [x [S [_ [[hx hS] [_ [-> ->]]]]]]; split.
  - by exists x.
  - by exists S.
have hCfine y : Y y -> covering_relation_fine_at C y.
  move=> [x hx <-]; apply: (covering_relation_fine_iff_small_diameter C (f x)).2=> e he.
  have [d [hd hdim]] := @continuous_based_small_diameter_images R P E f x e
    (@euclidean_plane_join_continuous R) he.
  have [S [[hxS hS] [hm hsmall]]] := hf x hx d hd.
  exists (f @` S); split.
  - exists x,S; split; first exact hx.
    split; first by split.
    split; first exact hm.
    by split.
  - exact: hdim S hxS hsmall.
have hCmeas T : covering_relation_image C Y T -> measure_measurable psi T.
  move=> [y [_ hCy]].
  have [x [S [_ [hrel [_ [_ hT]]]]]] := hCy.
  rewrite hT; apply: pushforward_measurable_from_preimage; rewrite hpre; apply: hmeas.
  have [a [b [c [d [_ [_ ->]]]]]] := hrel.2; exact: scalar_closed_rectangle_measurable.
have hCmass T : covering_relation_image C Y T ->
    2*(@euclidean_lebesgue_measure R 2) T<=psi T.
  move=> [y [_ hCy]].
  have [x [S [_ [_ [hm [_ hT]]]]]] := hCy.
  by rewrite hT hLeb /psi /measure_pushforward hpre.
have hstrict : psi setT<2*(@euclidean_lebesgue_measure R 2) Y.
  rewrite /psi /measure_pushforward preimage_setT /Y hLeb hZ mule1.
  apply: le_lt_trans hcost _; by rewrite lte_fin ltr1n.
have htwo : (0<2 :> R)%R by rewrite ltr0n.
exact (@vitali_fine_mass_obstruction R E (@euclidean_lebesgue_measure R 2) psi
  (@euclidean_rectangle_relation R) C Y 2 (euclidean_lebesgue_is_measure R 2) hpsi
  htwo hCY hCfine hCmeas hCmass hstrict).
Qed.
