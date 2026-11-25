(** Federer (1969), 3.3.4, pp. 288–292: actual regressions for
    the positive zero-dimensional atom, a noncentral line atom and
    an everywhere infinitely weighted planar counting measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces EuclideanInnerProduct InnerMetric
  FiniteCoordinates GrassmannHomogeneousSpace EuclideanGrassmannProbability
  EuclideanOneCoordinate StructureTrichotomy StructurePlaneGrowth StructureZeroPlaneAlternative
  StructureConeUP PointMassMeasure PointMassRegularity WeightedCountingMeasure
  NonnegativeSum NonnegativeSumSupport BorelClosedProjection TopologicalBorel MeasureAlmostUP.
(** Supplementary original proof assertions are also checked recursively. *)
From Federer Require Import EuclideanInjectionExtensionGroup EuclideanInjectionExtensionImage InjectionExtensionRange StructureApertureRatioLimit
  StructureDirectionMapBalls StructureProjectiveRotationMeasure StructureSourcePuncture.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_trichotomy_positive_zero_atom]: concrete
    zero-ambient regression for Federer 3.3.4, p. 288. The actual
    whole R^0 source has unit point mass, while the complete original
    theorem still applies with both dimensions zero. *)
Example structure_trichotomy_positive_zero_atom (R:realType):
  let E:=inner_metric_space (@euclidean_inner_productP R 0) in
  point_mass R (0:E) setT= 1%E /\
  @measure_almost_everywhere R
    [the choiceType of grassmann_space (@euclidean_inner_productP R 0)
      (@euclidean_inner_productP R 0) (@coordinate_basisP R 0) (@coordinate_basisP R 0)]
    (@euclidean_grassmann_probability R 0 0 (leq_subr 0 0))
    [set V|structure_plane_trichotomy 0 (point_mass R (0:E)) setT (0:E) V].
Proof.
cbn zeta; split; first exact:(@point_mass_in R
  (inner_metric_space (@euclidean_inner_productP R 0)) 0 setT I).
apply:(@structure_trichotomy R 0 0 (leqnn 0)).
- split; first exact:point_mass_is_measure.
  move=>C _; exact:point_mass_every_set_measurable.
- apply:metric_borel_suslin; exact:open_borel_set openT.
Qed.

(** Source for [structure_trichotomy_noncentral_line_atom]: concrete
    n=m endpoint for Federer 3.3.4(1), p. 288. The actual unit atom
    is at line coordinate one rather than at the centre zero; the
    original zero-plane cone has ordinary zero growth nevertheless. *)
Example structure_trichotomy_noncentral_line_atom (R:realType) (V:G (R_n R 1) 0):
  let E:=inner_metric_space (@euclidean_inner_productP R 1) in
  let x:E:=euclidean_one_embed (1:R) in
  point_mass R x [set x]= 1%E /\
  structure_plane_zero_growth 1 (point_mass R x) setT (0:E) V.
Proof.
cbn zeta; split; first exact:(@point_mass_in R
  (inner_metric_space (@euclidean_inner_productP R 1)) (euclidean_one_embed (1:R))
  [set euclidean_one_embed (1:R)] (erefl _)).
exact:structure_zero_plane_zero_growth (@point_mass_is_measure R
  (inner_metric_space (@euclidean_inner_productP R 1)) (euclidean_one_embed (1:R))).
Qed.

(** Source for [structure_trichotomy_infinite_planar_atoms]: concrete
    positive-codimension regression for Federer 3.3.4, pp. 288–292.
    Every actual planar point has infinite atomic mass, so no finite
    neighbourhood or local-finiteness premise could hold. The complete
    original theorem still gives its actual Grassmann almost-everywhere
    trichotomy for the whole original planar source. *)
Example structure_trichotomy_infinite_planar_atoms (R:realType):
  let E:=inner_metric_space (@euclidean_inner_productP R 2) in
  let phi:=@weighted_counting_measure R E (fun _=>+oo%E) in
  phi [set (0:E)]=+oo%E /\
  @measure_almost_everywhere R
    [the choiceType of grassmann_space (@euclidean_inner_productP R 1)
      (@euclidean_inner_productP R 2) (@coordinate_basisP R 1) (@coordinate_basisP R 2)]
    (@euclidean_grassmann_probability R 2 1 (leq_subr 1 2))
    [set V|structure_plane_trichotomy 1 phi setT (0:E) V].
Proof.
cbn zeta; split.
- rewrite weighted_counting_measure_sum.
  apply:nonnegative_sum_singleton; exact:leey.
- apply:(@structure_trichotomy R 2 1 (leqnSn 1)).
  + have hWeight (x:inner_metric_space (@euclidean_inner_productP R 2)):(0<=(+oo: \bar R))%E:=leey 0%E.
    split; first exact:(@weighted_counting_measure_is_measure R
      (inner_metric_space (@euclidean_inner_productP R 2)) (fun _=>+oo%E) hWeight).
    move=>C _; exact:(@weighted_counting_measure_measurable R
      (inner_metric_space (@euclidean_inner_productP R 2)) (fun _=>+oo%E) C hWeight).
  + apply:metric_borel_suslin; exact:open_borel_set openT.
Qed.
