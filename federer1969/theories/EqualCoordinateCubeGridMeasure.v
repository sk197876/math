(** Federer (1969), 3.2.38, pp. 274--275: exact finite sums over
    closed grid cubes. Shared coordinate faces have actual zero mass. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry
  EqualCoordinateCubeGridUP EqualCoordinateCubeGridLaws EuclideanCoordinateHyperplaneNull
  TopologicalBorel MeasureUP MeasureBasic MeasureAlmostBasic
  FiniteNullOverlapAdditivity FiniteCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_coordinate_grid_null_overlaps]: the null-face
    justification for the finite cube-volume sums in Federer 3.2.38,
    p. 275. It follows from actual grid coordinates, not an assumed
    disjointness or measurability property of the covered source. *)
Lemma equal_coordinate_grid_null_overlaps (R:realType) n k (a:R_n R n) (h:R) Q:
  is_equal_coordinate_cube_grid k a h Q ->forall s t,s!=t ->
    @euclidean_lebesgue_measure R n (Q s `&` Q t)=0%E.
Proof.
move=>hQ s t hst.
have [i [b hSubset]]:=equal_coordinate_grid_distinct_overlap hQ hst.
exact:(@measure_null_subset R _ _ (euclidean_lebesgue_is_measure R n)
  _ _ hSubset (euclidean_coordinate_hyperplane_null i b)).
Qed.

(** Source for [finite_coordinate_cubes_measure_sum]: supporting
    finite summation of closed source cells in Federer 3.2.38,
    p. 275. The finite subfamily may be empty and the measure may
    be the Jacobian density. Actual null-overlap laws suffice. *)
Lemma finite_coordinate_cubes_measure_sum (R:realType) n (I:finType)
    (a:I->R_n R n) (h:R)
    (Q:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (mu:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R):
  is_measure mu ->(forall i,is_euclidean_coordinate_cube (a i) h (Q i)) ->
  (forall i,measure_measurable mu (Q i)) ->
  (forall i j,i!=j ->mu (Q i `&` Q j)=0%E) ->
  mu (\bigcup_i Q i)=(\sum_i mu (Q i))%E.
Proof.
move=>hm hQ hMeas hOverlap.
have hAdd:=@measure_finite_family_null_overlap_additivity R
  (inner_metric_space (@euclidean_inner_productP R n)) I mu hm Q setT
  (@finite_finset I setT) (fun i _=>hMeas i) (fun i j _ _=>hOverlap i j).
rewrite (@finite_type_nonnegative_sum R I (fun i=>mu (Q i))
  (fun i=>@measure_nonnegative R _ mu hm (Q i))) in hAdd.
exact hAdd.
Qed.
