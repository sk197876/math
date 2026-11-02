(** Federer (1969), 3.2.38, pp. 274--275: subdivide each
    bad parent cube and sum its actual small-cube tube bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes EuclideanBallVolume EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry
  EqualCoordinateCubeGridUP EqualCoordinateCubeGridLaws EqualCoordinateCubeGridMeasure CoordinateCubeSubdivision
  LipschitzUP LipschitzCubeTubeNormalization FiniteMinkowskiTubeCover MinkowskiContents
  MeasureUP MeasureBasic FiniteNullOverlapAdditivity TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_parent_cube_normalized_tube_bound]: supporting
    the H-family sum in Federer 3.2.38, p. 275. A side-vr
    parent has an exact finite subdivision into side-r cubes. Each
    actual child has the proved ball tube estimate; its coordinate
    faces are null, so exact additivity sums their mass to the
    original parent mass. This packages one inner finite sum without
    adding a covering, disjointness or volume premise. *)
Lemma lipschitz_parent_cube_normalized_tube_bound (R:realType) m n (hmn:(m<=n)%N)
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (a:R_n R m) (r L:R) v (Q:set (inner_metric_space (@euclidean_inner_productP R m))):
  (0<v)%N ->0<r ->is_metric_lipschitz_bound setT f L ->
  is_euclidean_coordinate_cube a (v%:R*r) Q ->
  (minkowski_tube_quotient m (f @` Q) r<=
    (euclidean_unit_ball_volume R n*(1+L* m%:R)^+n/euclidean_unit_ball_volume R (n-m))%R%:E*
      @euclidean_lebesgue_measure R m Q)%E.
Proof.
move=>hv hr hLip hQ.
have [P [hP hUnion]]:=coordinate_cube_subdivision_exists hv (ltW hr) hQ.
pose I:=coordinate_cube_grid_indices m v.
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose eta:R:=euclidean_unit_ball_volume R n*(1+L* m%:R)^+n/euclidean_unit_ball_volume R (n-m).
have hCube s:=equal_coordinate_grid_cell_cube hP s.
have hMeas s:measure_measurable mu (P s).
  apply:euclidean_borel_measurable.
  exact:closed_borel_set (compact_closed (@metric_hausdorff R
    (inner_metric_space (@euclidean_inner_productP R m))) (coordinate_cube_compact (hCube s))).
have hMass:mu Q=(\sum_(s:I) mu (P s))%E.
  rewrite hUnion.
  exact:(@finite_coordinate_cubes_measure_sum R m I
    (fun s=>[ffun i=>a i+(s i)%:R*r]) r P mu hm hCube hMeas
    (fun s t=>@equal_coordinate_grid_null_overlaps R m v a r P hP s t)).
have hCover:Q `<=` \bigcup_s P s by rewrite -hUnion.
have hTubeCover:=@finite_minkowski_image_tube_cover R
  (inner_metric_space (@euclidean_inner_productP R m)) n m I f Q P r hr hCover.
have hChild s:(minkowski_tube_quotient m (f @` P s) r<=eta%:E*mu (P s))%E.
  have hBound:=@lipschitz_coordinate_cube_normalized_tube_bound R m n
    ([ffun i=>a i+(s i)%:R*r]) r L (P s) f hmn (hCube s) hr hLip.1 hLip.
  rewrite /mu (coordinate_cube_volume (hCube s)) -EFinM.
  exact hBound.
apply:le_trans hTubeCover _.
have hSum:(\sum_(s:I) minkowski_tube_quotient m (f @` P s) r<=
    \sum_(s:I) eta%:E*mu (P s))%E.
  apply:lee_sum=>s _; exact:hChild s.
apply:le_trans hSum _.
change ((\sum_(s:I) eta%:E*mu (P s))<=eta%:E*mu Q)%E.
rewrite hMass ge0_sume_distrr; first exact:lexx.
move=>s _; exact:measure_nonnegative hm _.
Qed.
