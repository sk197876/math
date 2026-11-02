(** Federer (1969), 2.10.47, p. 204: if a hyperplane section has positive
    measure, the lower dimensional induction hypothesis produces the
    required compact subset inside that section. Coordinate hyperplanes
    suffice for the dyadic construction. The existing opaque normal chart
    gives an isometric embedding and a nonexpanding inverse; no new
    coordinate choice is exposed. Source context:
    EuclideanHyperplaneGeometry.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology num_normedtype.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanNormalChartUP EuclideanNormalChart EuclideanHyperplaneGeometry NormalHeadChartGeometry
  EuclideanCoordinateTopology CoordinateProjection OrthonormalFamilies NormMetricScaleContinuity
  MetricRealPowerMeasure MetricRealPowerMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_positive_coordinate_section_reduction]:
    explicit lower-dimensional case of the induction sentence
    in 2.10.47, p. 204. The hypothesis about
    sections is used to select a positive section, not
    assumed for the final theorem. *)
Theorem compact_positive_coordinate_section_reduction (R : realType) n c p
    (A : set (inner_metric_space (@euclidean_inner_productP R n.+1))) (l : 'I_n.+1) (t : R) :
  (0<=c)%R -> (0<=p)%R ->
  (forall C : set (inner_metric_space (@euclidean_inner_productP R n)), compact C ->
    0<metric_real_power_measure c p C ->
    exists D, [/\ compact D, D `<=` C, 0<metric_real_power_measure c p D & metric_real_power_measure c p D< +oo]) ->
  compact A -> 0<metric_real_power_measure c p (A `&` [set x | x l=t]) ->
  exists B, [/\ compact B, B `<=` A, 0<metric_real_power_measure c p B & metric_real_power_measure c p B< +oo].
Proof.
move=> hc hp IH hA hpositive.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose Y := inner_metric_space (@euclidean_inner_productP R n.+1).
pose u := @coordinate_basis R n.+1 l.
have hu : euclidean_inner_product u u= 1%R by rewrite euclidean_inner_basis /u /coordinate_basis ffunE eqxx.
pose D := euclidean_normal_chart ord0 hu.
have hD : @is_euclidean_normal_chart R n.+1 ord0 u D := euclidean_normal_chart_specification ord0 hu.
pose f : X -> Y := @normal_hyperplane_embedding R n D t.
pose g : Y -> X := @normal_hyperplane_projection R n D.
have hfg : cancel f g := @normal_hyperplane_embeddingK R n D t u hD.
have hf x y : (mdist (f x) (f y)<=mdist x y)%R.
  by rewrite (@normal_hyperplane_embedding_isometry R n D t u hD).
have hg x y : (mdist (g x) (g y)<=mdist x y)%R := @normal_hyperplane_projection_nonexpanding R n D u hD x y.
have hfc : continuous f.
  apply: (@metric_fixed_lipschitz_continuous R X Y f 1%R ler01)=> x y; rewrite mul1r; exact: hf.
have hgc : continuous g.
  apply: (@metric_fixed_lipschitz_continuous R Y X g 1%R ler01)=> x y; rewrite mul1r; exact: hg.
pose S := A `&` [set x : Y | x l=t].
have hclosed : closed [set x : Y | x l=t].
  apply: (@preimage_closed Y R^o (fun x=>x l) [set t]); last exact: closed_eq.
  by move=> x _; exact: euclidean_coordinate_continuous.
have hS : compact S := compact_closedI hA hclosed.
have hgf x : S x -> f (g x)=x.
  move=> [_ hx]; apply: (@normal_hyperplane_projectionK R n D t u hD).
  have hh := @normal_chart_head_coordinate R n u D hD x.
  rewrite inner_coordinateE euclidean_inner_basis in hh.
  by rewrite -hh.
pose C := g @` S.
have hC : compact C := continuous_compact (continuous_subspaceT hgc) hS.
have himage : f @` C=S.
  apply/seteqP; split.
  - move=> _ [z [x hx <-] <-]; by rewrite hgf.
  - move=> x hx; exists (g x); last exact: hgf.
    by exists x.
have hmeasure T := @metric_real_power_isometric_image R X Y c p f g hc hp hfg hf hg T.
have hCp : 0<metric_real_power_measure c p C by rewrite -(hmeasure C) himage.
have [K [hK hKC hKp hKf]] := IH C hC hCp.
exists (f @` K); split.
- exact: continuous_compact (continuous_subspaceT hfc) hK.
- move=> _ [z hz <-]; have [x hx he] := hKC z hz.
  rewrite -he hgf //; exact hx.1.
- by rewrite hmeasure.
- by rewrite hmeasure.
Qed.
