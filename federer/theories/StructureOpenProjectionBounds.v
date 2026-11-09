(** Federer (1969), 3.3.14, p. 298: one original projection
    satisfying countably many tests controls every original open set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanProjectionMetric EuclideanLebesgueDimensions OrthogonalProjectionProbability
  ProjectionMultiplicityIntegral IntegralGeometricMeasure CountableOpenTestsUP
  StructureIntegralGeometricProjectionBounds TopologicalBorel BorelFamilyBasic
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureContinuityBelow
  ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_all_open_projection_bounds]: supporting
    the uniform open-source bound in Federer 3.3.14, p. 298.
    Actual countable open tests replace the printed small partition
    cells. Their common null exception gives all finite-test bounds;
    actual contained increasing exhaustion, original Suslin image
    measurability and 2.1.3(4) continuity give EVERY original open set.
    No open bound or null-subset-preservation result is supplied. *)
Lemma structure_all_open_projection_bounds (R:realType) n m (hmn:(m<=n)%N)
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (J:choiceType) (F:J->set (inner_metric_space (@euclidean_inner_productP R n))):
  borel_set E ->is_countable_open_test_family F ->
  measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
    [set p|forall O,open O ->euclidean_lebesgue_measure m
      (euclidean_projection_linear p @` (E `&` O))<=
      @integral_geometric_measure R n m hmn +oo (E `&` O)].
Proof.
move=>hE hF.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose I:=@integral_geometric_measure R n m hmn +oo.
have hI:is_measure I:=@integral_geometric_measure_is_measure R n m hmn +oo (leey 1).
have hTest j:borel_set (E `&` F j).
  exact:(@borel_family_binary_intersection [the topologicalType of X] setT _
    (borel_sets_family [the topologicalType of X]) E (F j) hE
    (open_borel_set (open_test_open hF j))).
have hAlmost:=@structure_countable_projection_bounds R n m hmn J setT
  (fun j=>E `&` F j) (open_test_countable hF) (fun j _=>hTest j).
have hTheta:=theta_star_is_measure R hmn.
apply:(measure_almost_everywhere_mono hTheta _ hAlmost)=>p hp O hO.
have [a [hIncreasing [hContained hUnion]]]:=open_test_exhaustion hF hO.
pose S k:=euclidean_projection_linear p @` (E `&` F (a k)).
pose L:=@euclidean_lebesgue_measure R m.
have hL:=euclidean_lebesgue_is_measure R m.
have hS k:measure_measurable L (S k):=@euclidean_projection_borel_image_measurable R n m p _ (hTest (a k)).
have hMono j k:(j<=k)%N ->S j `<=` S k.
  move=>hjk y [x [hx hFx] <-]; exists x; last by [].
  split; first exact:hx; exact:hIncreasing j k hjk x hFx.
have hImage:euclidean_projection_linear p @` (E `&` O)=\bigcup_k S k.
  apply/seteqP; split=>y.
  - move=>[x [hx hOx] <-]; rewrite hUnion in hOx; have [k _ hFx]:=hOx.
    exists k; first exact:Logic.I.
    exists x; last by [].
    by split.
  - move=>[k _ [x [hx hFx] <-]]; exists x; last by [].
    split; first exact:hx; exact:hContained k x hFx.
have hLimit:=@measure_continuity_below R [the choiceType of Y] L hL S hS hMono.
have hBound k:L (S k)<=I (E `&` O).
  apply:le_trans (hp (a k) Logic.I) _.
  apply:(@measure_mono R _ I hI)=>x [hx hFx]; split; first exact:hx.
  exact:hContained k x hFx.
rewrite hImage.
apply:(extended_real_supremum_least (extended_increasing_limit_supremum hLimit)).
by move=>v [k ->]; exact:hBound.
Qed.
