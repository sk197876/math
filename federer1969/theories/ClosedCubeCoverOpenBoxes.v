(** Federer (1969), 3.2.41, printed p. 278, compact
    approximation: a finite null-overlap closed cube cover
    gives a genuine disjoint open-box family of at least the
    original outer volume, lying in a prescribed small tube. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanCoordinateCubeUP FiniteCubeFamilyNearSet
  EuclideanOpenCoordinateBoxUP EuclideanOpenCoordinateBoxMeasure CoordinateCubeOpenBoxInterior
  OpenBoxNullIntersection FiniteDisjointOpenBoxFamilyUP MetricOpenThickening
  MeasureUP MeasureBasic MeasureSplit MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_cube_cover_open_boxes]: supporting genuine
    disjoint finite-box approximation in Federer 3.2.41, p. 278.
    Actual cube boundaries are null, and proper-box positivity
    turns null intersections of interiors into true disjointness.
    The original K is covered up to those null remainders; its
    points on grid faces are not silently discarded. *)
Theorem closed_cube_cover_open_boxes (R:realType) n (I:finType)
    (a:I->R_n R n) (h r:R)
    (Q:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (K:set (inner_metric_space (@euclidean_inner_productP R n))):
  0<h ->(forall i,is_euclidean_coordinate_cube (a i) h (Q i)) ->
  (forall i,(Q i `&` K) !=set0) ->K `<=` \bigcup_i Q i ->
  (forall i j,i!=j ->@euclidean_lebesgue_measure R n (Q i `&` Q j)=0%E) ->
  n%:R*h<r ->K !=set0 ->
  exists (b:I->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n))),
    is_finite_disjoint_open_box_family a b G /\(\bigcup_i G i) !=set0 /\
    (@euclidean_lebesgue_measure R n K<=@euclidean_lebesgue_measure R n (\bigcup_i G i))%E /\
    (\bigcup_i G i) `<=` metric_open_thickening K r.
Proof.
move=> hh hQ hMeet hCover hOverlap hMesh hKNe.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose b(i:I):R_n R n:=[ffun j=>a i j+h].
have hExists i:exists P:set E,
    is_euclidean_open_coordinate_box (a i) (b i) P /\
    P `<=` Q i /\mu (Q i `\` P)=0%E.
  exact:(@coordinate_cube_open_box_interior_exists R n (a i) h (Q i) hh (hQ i)).
have [G hProps]:=choice hExists.
have hm:=euclidean_lebesgue_is_measure R n.
have hNull i j:i!=j ->mu (G i `&` G j)=0%E.
  move=> hNe; apply:(@measure_null_subset R E mu hm _ (Q i `&` Q j) _ (hOverlap i j hNe)).
  move=> x [hi hj]; split; [exact:(hProps i).2.1 x hi|exact:(hProps j).2.1 x hj].
have hFamily:is_finite_disjoint_open_box_family a b G.
  constructor; first by move=> i; exact:(hProps i).1.
  move=> i j hNe.
  exact:(@open_boxes_null_intersection_disjoint R n (a i) (b i) (a j) (b j)
    (G i) (G j) (hProps i).1 (hProps j).1 (hNull i j hNe)).
have hGNe:(\bigcup_i G i) !=set0.
  have [x hx]:=hKNe; have [i _ hi]:=hCover x hx.
  have [z hz]:=open_coordinate_box_nonempty (hProps i).1.
  exists z; by exists i.
pose N:set E:=\bigcup_i (Q i `\` G i).
have hN:mu N=0%E.
  exact:(@measure_null_countable_union R E I mu hm setT (fun i=>Q i `\` G i)
    (finite_set_countable (@finite_finset I setT)) (fun i _=>(hProps i).2.2)).
have hSource:K `<=` (\bigcup_i G i) `|` N.
  move=> x hx; have [i _ hi]:=hCover x hx.
  case:(pselect (G i x))=> hxi.
  - left; by exists i.
  - right; exists i=>//; by split.
have hMass:=@measure_binary_cover R E mu hm K (\bigcup_i G i) N hSource.
rewrite hN adde0 in hMass.
have hNear:=@coordinate_cube_family_near_set R n I a h r Q K hQ hMeet hMesh.
exists b,G; split; first exact hFamily.
split; first exact hGNe.
split; first exact hMass.
move=> x [i _ hi]; apply:hNear; exists i=>//; exact:(hProps i).2.1 x hi.
Qed.
