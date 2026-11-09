(** Federer (1969), 3.3.14, p. 298: complete original
    condition (I) outside one actual projection-null exceptional set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace EuclideanProjectionMetric
  FiniteCoordinates InnerSpaceCountableBase OrthogonalProjectionProbability IntegralGeometricMeasure
  CountableOpenTestsUP CountableOpenTestsExistence StructureOpenProjectionBounds
  StructureOpenBoundNullPreservation StructureProjectionConditions
  MeasureUP MeasureAlmostUP MeasureAlmostBasic TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_integral_geometric_null_preservation]:
    the full original (I) conclusion within the proof of Federer
    3.3.14, p. 298. An actual local countable Euclidean base supplies
    a local family of open tests through independent exhaustion laws.
    Actual common null exceptions and monotone projected-image
    continuity give all opens; the actual finite Borel restriction
    and open-infimum law give EVERY original null subset. No source
    or image replacement, supplied uniform null-preservation theorem
    or extra projection hypothesis is assumed. *)
Lemma structure_integral_geometric_null_preservation (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):
  borel_set E ->@integral_geometric_measure R n m hmn +oo E< +oo ->
  measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
    [set p|structure_projection_preserves_null_subsets
      (@integral_geometric_measure R n m hmn +oo) E p].
Proof.
move=>hE hFinite.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose I:=@integral_geometric_measure R n m hmn +oo.
have hI:is_measure I:=@integral_geometric_measure_is_measure R n m hmn +oo (leey 1).
have hRegular:=@integral_geometric_measure_borel_regular R n m hmn +oo (leey 1).
have [U hU]:=inner_space_countable_open_base (@euclidean_inner_productP R n) (@coordinate_basisP R n).
have [F hF]:=countable_open_test_family_exists hU.
have hOpen:=@structure_all_open_projection_bounds R n m hmn E
  [the choiceType of (seq nat:Type)] F hE hF.
have hTheta:=theta_star_is_measure R hmn.
apply:(measure_almost_everywhere_mono hTheta _ hOpen)=>p hp.
exact:(@structure_open_bound_null_preservation R n m I E p hI hRegular hE hFinite hp).
Qed.
