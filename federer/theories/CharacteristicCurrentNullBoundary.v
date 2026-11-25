(** Federer (1969), 4.1.23, pp. 379–380:
    a proper coordinate box and its
    compact closure give the same actual
    constant-coefficient current. The original
    densities differ only on the preceding
    null boundary, and every actual compact
    test integral is almost invariant. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentSpaces CurrentCharacteristicDensity
  CurrentDensityAlmostAgreement SmoothCompactSet TopologicalBorel
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  EuclideanOpenCoordinateBoxUP EuclideanOpenBoxMeasurability
  ClosedCoordinateBoxConvex ClosedCoordinateBoxGeometry
  MeasureUP MeasureAlmostUP MeasureAlmostBasic
  CharacteristicFunctionUP CharacteristicFunctionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [characteristic_current_nested_null_difference]:
    a null omitted boundary leaves the
    original Lebesgue coefficient current unchanged,
    supporting Federer 4.1.23, pp. 379–380.
    The sets may have infinite measure;
    only their original measurable density
    actions and the actual null remainder are used. *)
Theorem characteristic_current_nested_null_difference (R : realType)
    (h2 : (1+1:R)!=0) n m (A B : set (R_n R n))
    (hA : measure_measurable (@euclidean_lebesgue_measure R n) A)
    (hB : measure_measurable (@euclidean_lebesgue_measure R n) B)
    (z : exterior_power (R_n R n) m) :
  A `<=` B -> @euclidean_lebesgue_measure R n (B `\` A)=0%E ->
  @current_characteristic_density R h2 n m (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
    (@euclidean_distribution_measure_compact_finite R n) A hA z=
  @current_characteristic_density R h2 n m (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
    (@euclidean_distribution_measure_compact_finite R n) B hB z.
Proof.
move=> hAB hNull.
apply: (current_density_almost_agreement (euclidean_lebesgue_is_measure R n)
  (@current_characteristic_density_action R h2 n m (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
    (@euclidean_distribution_measure_compact_finite R n) A hA z)
  (@current_characteristic_density_action R h2 n m (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
    (@euclidean_distribution_measure_compact_finite R n) B hB z)).
have hConull : measure_almost_everywhere (@euclidean_lebesgue_measure R n) (~`(B `\` A)).
  by rewrite /measure_almost_everywhere setCK.
apply: (@measure_almost_everywhere_mono R (R_n R n) (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) _ _ _ hConull)=> x hx.
change (@CharacteristicFunction.value R (R_n R n) A x*:z=
  @CharacteristicFunction.value R (R_n R n) B x*:z).
case: (pselect (A x))=> hAx.
- by rewrite (characteristic_on_set (@CharacteristicFunction.laws R (R_n R n) A) hAx)
    (characteristic_on_set (@CharacteristicFunction.laws R (R_n R n) B) (@hAB x hAx)).
- have hBx : ~B x by move=> h; exact: hx (conj h hAx).
  by rewrite (characteristic_off_set (@CharacteristicFunction.laws R (R_n R n) A) hAx)
    (characteristic_off_set (@CharacteristicFunction.laws R (R_n R n) B) hBx).
Qed.

Section BoxCurrentClosure.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variables a b : R_n R n.
Variable G : set (R_n R n).
Hypothesis hG : @is_euclidean_open_coordinate_box R n a b G.
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation C := (@closed_coordinate_box R n a b).
Local Notation hGM := (@open_coordinate_box_measurable R n a b G hG).
Local Notation hCM := (@euclidean_distribution_measure_borel R n C
  (closed_borel_set (compact_closed (@metric_hausdorff R (real_norm_metric_space hNX))
    (@closed_coordinate_box_norm_compact R n a b)))).

(** Source for [proper_coordinate_box_current_closure]:
    the actual m-current of the
    selected proper box is unchanged
    when its compact closure is used,
    Federer 4.1.23, pp. 379–380.
    All coefficient degrees and dimension
    zero retain the same literal current. *)
Theorem proper_coordinate_box_current_closure
    (z : exterior_power (R_n R n) m) :
  @current_characteristic_density R h2 n m (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
    (@euclidean_distribution_measure_compact_finite R n) G hGM z=
  @current_characteristic_density R h2 n m (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
    (@euclidean_distribution_measure_compact_finite R n) C hCM z.
Proof.
apply: characteristic_current_nested_null_difference.
- move=> x hx i; have /andP [hLow hHigh] := (hG.2 x).1 hx i.
  apply/andP; split; exact: ltW.
- exact: (@proper_coordinate_box_null_boundary R n a b G hG).
Qed.
End BoxCurrentClosure.
