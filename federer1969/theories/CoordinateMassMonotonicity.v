(** Federer (1969), 3.2.27, pp. 262–263: the
    coordinate mass lower bound remains valid on arbitrary
    finite rectifiable sources whenever the displayed
    coordinate integrals exist. Supporting monotonicity
    follows from actual fibre inclusion and 2.4.4(5). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric ExteriorIndices
  CoordinateProjection RectifiableCoordinateMassUP EuclideanLebesgueDimensions
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci ExtendedRealOrderTopology
  MappingMultiplicity CountingMeasure MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralComparison NonnegativeExtendedNormOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coordinate_masses_nonnegative]: nonnegativity
    of each a_lambda in 3.2.27, p. 262, by
    actual counting and 2.4.4(2), p. 82. No
    measurability of the original source is assumed. *)
Lemma coordinate_masses_nonnegative (R:realType) m n (W:set (R_n R n))
    (a:Lambda n m->R):
  is_rectifiable_coordinate_masses W a ->forall lambda,(0<=a lambda)%R.
Proof.
move=>hA lambda.
have h:=@nonnegative_total_integral_value_ge0 R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
  (@euclidean_lebesgue_measure R m) (@euclidean_lebesgue_is_measure R m) _ _
  (fun y=>@mapping_multiplicity_nonnegative R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
    (R_n R m) (@coordinate_projection R n m lambda) W y) (hA lambda).
by rewrite lee_fin in h.
Qed.

(** Source for [coordinate_masses_subset_mono]: supporting
    measure-hull comparison for the lower inequality in
    3.2.27, pp. 262–263. Inclusion of each actual
    fibre implies inclusion of its counting mass, and
    monotonicity of the actual integrals gives the
    coordinatewise bound. *)
Lemma coordinate_masses_subset_mono (R:realType) m n (W M:set (R_n R n))
    (a b:Lambda n m->R):
  W `<=` M ->is_rectifiable_coordinate_masses W a ->is_rectifiable_coordinate_masses M b ->
  forall lambda,(a lambda<=b lambda)%R.
Proof.
move=>hWM hA hB lambda.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose F:=@coordinate_projection R n m lambda.
pose beta:=@euclidean_lebesgue_measure R m.
have hBeta:=@euclidean_lebesgue_is_measure R m.
have hPoint y:@mapping_multiplicity R (Choice.clone X _) Y F W y<=
    @mapping_multiplicity R (Choice.clone X _) Y F M y.
  apply:(measure_mono (@counting_measure_is_measure R (Choice.clone X _)))=>x [hx hF].
  split; first exact:hWM x hx; exact hF.
have h:=@measure_integral_monotone R (Choice.clone Y _) beta hBeta _ _ _ _
  (hA lambda) (hB lambda).
have hAE:measure_almost_everywhere beta (partial_extended_le_locus
    (partial_function_total (fun y=>(@mapping_multiplicity R (Choice.clone X _) Y F W y:extended_real_line R)))
    (partial_function_total (fun y=>(@mapping_multiplicity R (Choice.clone X _) Y F M y:extended_real_line R)))).
  apply:(measure_almost_everywhere_mono hBeta _ (measure_almost_everywhere_true hBeta))=>y _.
  exists (@mapping_multiplicity R (Choice.clone X _) Y F W y),
    (@mapping_multiplicity R (Choice.clone X _) Y F M y); by split; last split; last exact:hPoint y.
have hBound:=h hAE; by rewrite lee_fin in hBound.
Qed.

(** Source for [coordinate_integral_subset_upper]: supporting
    finiteness of each actual integral in the defining
    display of 3.2.27, p. 262. The original
    integral value may initially be extended real;
    fibre inclusion bounds it by a finite containing
    source's actual coordinate mass. *)
Lemma coordinate_integral_subset_upper (R:realType) m n
    (W M:set (R_n R n)) (lambda:Lambda n m) (z: \bar R) (b:Lambda n m->R):
  W `<=` M ->
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y=>(@mapping_multiplicity R
      [the choiceType of inner_metric_space (@euclidean_inner_productP R n)]
      (R_n R m) (@coordinate_projection R n m lambda) W y:extended_real_line R))) z ->
  is_rectifiable_coordinate_masses M b ->z<=(b lambda)%:E.
Proof.
move=>hWM hZ hB.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
pose F:=@coordinate_projection R n m lambda.
pose beta:=@euclidean_lebesgue_measure R m.
have hBeta:=@euclidean_lebesgue_is_measure R m.
apply:(@measure_integral_monotone R (Choice.clone Y _) beta hBeta _ _ _ _ hZ (hB lambda)).
apply:(measure_almost_everywhere_mono hBeta _ (measure_almost_everywhere_true hBeta))=>y _.
exists (@mapping_multiplicity R (Choice.clone X _) Y F W y),
  (@mapping_multiplicity R (Choice.clone X _) Y F M y); split; first reflexivity; split; first reflexivity.
apply:(measure_mono (@counting_measure_is_measure R (Choice.clone X _)))=>x [hx hF].
split; first exact:hWM x hx; exact hF.
Qed.
