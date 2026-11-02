(** Federer (1969), 2.10.36, printed p. 198: the symmetrised convex set
    contains the base projection and the two endpoints of the centred first
    chord. Apply the proved double-cone section integral to obtain height
    times projected volume divided by dimension. Compactness is used here
    only for the existing Steiner volume theorem; the final endpoint
    inequality removes it by a compact convex hull. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology ring lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps InnerMetric InnerConvex
  OrthonormalFamilies CoordinateProjection TensorUP EuclideanCoordinateTopology EuclideanCoordinateSplit EuclideanNormalChartUP
  NormalHeadChartGeometry UnitNormalGeometry NormalSectionConvex CenteredSectionChordInclusion
  SteinerSymmetrisationUP SteinerSymmetrisation SteinerCompact SteinerConvex SteinerVolume
  CoveringFamilyUP CompactSetDistanceProfile CompactMetricBounded ScalarConvexLength BipyramidHeightVolumeBound
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanLebesgueLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_chord_projection_volume_bound]: supporting
    last inequality in 2.10.36, p. 198,
    in any specified normal chart whose first axis
    is the chord direction. The original compact
    convex set need not have interior; the projected
    base may have zero volume, including dimension zero. *)
Theorem steiner_chord_projection_volume_bound (R : realType) (n : nat)
    (u : inner_metric_space (@euclidean_inner_productP R n.+1))
    (D : euclidean_normal_chart_data R n.+1)
    (S : set (inner_metric_space (@euclidean_inner_productP R n.+1)))
    (a b : inner_metric_space (@euclidean_inner_productP R n.+1)) (h : R) :
  @is_euclidean_normal_chart R n.+1 ord0 u D -> compact S -> is_inner_convex S ->
  S a -> S b -> 0<h ->
  normal_chart_backward_map D (a-b)=@coordinate_head_inclusion R n h ->
  ((h/n.+1%:R)%:E*euclidean_lebesgue_measure n
    ((fun x => coordinate_tail (normal_chart_backward_map D x)) @` S)
    <=euclidean_lebesgue_measure n.+1 S)%E.
Proof.
move=> hD hS hconv ha hb hh hchord.
pose hB := @euclidean_inner_productP R n.+1.
pose f := normal_chart_forward_map D.
pose g := normal_chart_backward_map D.
have hu : euclidean_inner_product u u= 1.
  rewrite -(normal_chart_axis_law hD) (normal_chart_orthogonal_law hD) euclidean_inner_basis.
  by rewrite /coordinate_basis ffunE eqxx.
have hne : S !=set0 by exists a.
pose SC : compact_metric_set (inner_metric_space hB) :=
  exist _ S (mem_set (conj hS hne)).
have hbound : metric_set_bounded S := compact_metric_diameter_finite SC.
pose T : set (inner_metric_space hB) := steiner_symmetrisation hB hu hbound.
have hT := steiner_symmetrisation_specification hB hu hbound.
have hTc : compact T := steiner_preserves_compactness hT hS.
have hTv : is_inner_convex T := steiner_preserves_convexity hT hbound hconv.
pose C : set (inner_metric_space hB) := g @` T.
pose K : set (inner_metric_space (@euclidean_inner_productP R n)) :=
  (fun x => coordinate_tail (g x)) @` S.
have hCc : compact C.
  apply: continuous_compact hTc.
  apply: continuous_subspaceT; exact: euclidean_linear_continuous.
have hCv : is_inner_convex C := linear_image_inner_convex hTv.
have hKc : compact K.
  apply: (continuous_compact _ hS); apply: continuous_subspaceT.
  move=> x; apply: (@continuous_comp (Topological.clone (inner_metric_space hB) _)
    (Topological.clone (inner_metric_space hB) _)
    (Topological.clone (inner_metric_space (@euclidean_inner_productP R n)) _)
    g (@coordinate_tail R n) x).
  - exact: euclidean_linear_continuous.
  - exact: coordinate_tail_continuous.
have hKf : (euclidean_lebesgue_measure n K< +oo)%E := euclidean_compact_finite hKc.
have hmem (x : inner_metric_space (@euclidean_inner_productP R n)) (t : R) :
    T (f (euclidean_join (x,t))) -> C (euclidean_join (x,t)).
  move=> hx; exists (f (euclidean_join (x,t)))=> //.
  by rewrite /f /g (normal_chart_forward_inverse_law hD).
have hfoot x : f (euclidean_join (coordinate_tail (g x),0))=normal_foot hB u x.
  by rewrite -(normal_chart_head_foot hD x) /f /g (normal_chart_backward_inverse_law hD).
have hbase x : K x -> C (euclidean_join (x,0)).
  move=> [y hy <-]; apply: hmem; rewrite hfoot.
  have hs := steiner_normal_sections_law hT (normal_coordinate_foot hB hu y).
  have hys : normal_scalar_section u S (normal_foot hB u y) (inner_coordinate hB u y).
    by rewrite /normal_scalar_section /= normal_decomposition.
  have hz : (2 : R)*`|(0 : R)|<=`|inner_coordinate hB u y-inner_coordinate hB u y|.
    by rewrite subrr !normr0 mulr0.
  have hi := centered_section_contains_chord_interval hs
    (normal_scalar_section_convex hconv) hys hys hz.
  by move: hi; rewrite /normal_scalar_section /= scale0r addr0.
have htail : coordinate_tail (g a)=coordinate_tail (g b).
  have he := congr1 (@coordinate_tail R n) hchord.
  rewrite !linearB in he.
  have hz : coordinate_tail (@coordinate_head_inclusion R n h)=0.
    apply/ffunP=> i; by rewrite /coordinate_tail /coordinate_head_inclusion !ffunE lift_eqF.
  rewrite hz in he; apply/eqP; by rewrite -subr_eq0 he eqxx.
have hfeet : normal_foot hB u b=normal_foot hB u a.
  apply: (can_inj (normal_chart_backward_inverse_law hD)).
  exact (eq_trans (normal_chart_head_foot hD b)
    (eq_trans (congr1 (fun z => euclidean_join (z,0)) (esym htail))
      (esym (normal_chart_head_foot hD a)))).
have hheight : inner_coordinate hB u a-inner_coordinate hB u b=h.
  have he := congr1 (@coordinate_head R n) hchord.
  rewrite !linearB coordinate_headK in he.
  rewrite (normal_chart_head_coordinate hD a) (normal_chart_head_coordinate hD b).
  exact he.
have hapex (t : R) : 2*`|t|<=h -> C (euclidean_join (coordinate_tail (g a),t)).
  move=> ht; apply: hmem; rewrite (normal_chart_head_line hD) hfoot.
  have hs := steiner_normal_sections_law hT (normal_coordinate_foot hB hu a).
  have has : normal_scalar_section u S (normal_foot hB u a) (inner_coordinate hB u a).
    by rewrite /normal_scalar_section /= normal_decomposition.
  have hbs : normal_scalar_section u S (normal_foot hB u a) (inner_coordinate hB u b).
    by rewrite /normal_scalar_section /= -hfeet normal_decomposition.
  apply: (@centered_section_contains_chord_interval R _ _ _ _ t hs
    (normal_scalar_section_convex hconv) has hbs).
  by rewrite hheight (ger0_norm (ltW hh)).
have hr : 0<h/2 by rewrite divr_gt0 // ltr0n.
have htwice : 2*(h/2)=h by field.
have hpos : 2*`|h/2|<=h.
  by rewrite (ger0_norm (ltW hr)) htwice.
have hneg : 2*`|-(h/2)|<=h by rewrite normrN.
have hv := @bipyramid_height_volume_lower_bound R n K C (coordinate_tail (g a))
  (h/2) hr hCc hCv hKf hbase (hapex _ hpos) (hapex _ hneg).
have hscale : 2*(h/2)*n.+1%:R^-1=h/n.+1%:R by rewrite htwice.
rewrite hscale in hv.
have hCvol : euclidean_lebesgue_measure n.+1 C=euclidean_lebesgue_measure n.+1 T.
  have he : C=(f : inner_metric_space hB -> inner_metric_space hB) @^-1` T.
    apply/seteqP; split=> x /=.
    - move=> [y hy <-]; by rewrite /f /g (normal_chart_backward_inverse_law hD).
    - move=> hx; exists (f x)=> //; by rewrite /f /g (normal_chart_forward_inverse_law hD).
  rewrite he; exact (@euclidean_orthogonal_pushforward R n.+1 f
    (normal_chart_orthogonal_law hD) T).
rewrite hCvol -(steiner_preserves_euclidean_volume hT hS) in hv; exact hv.
Qed.
