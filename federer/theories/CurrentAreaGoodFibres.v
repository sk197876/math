(** Federer (1969), 4.1.25, p. 383: the discarded
    nondifferentiable and singular source points have a
    Hausdorff-null image. Reuse the complete original
    3.2.3 reduction, pp. 243–244, which already discards
    those images on arbitrary measurable sources. This
    gives the full fibre domain, without a finite-source
    mass premise or a second critical-image proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  ExteriorGrading EuclideanLinearJacobian LipschitzUP
  InjectiveDifferentialPieceUP AreaBorelReductionUP MeasurableAreaBorelReduction
  EuclideanLebesgueDimensions HausdorffMeasure MeasureUP MeasureBasic MeasureSplit
  MeasureAlmostUP MeasureAlmostBasic PartialFunctionUP
  CurrentAreaNormalisedImageSealed CurrentAreaNormalisedImageLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section GoodAreaFibres.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Variable f : X -> Y.
Variable xi : R_n R m -> exterior_power (R_n R m) m.
Hypothesis hLip : is_metric_lipschitz setT f.
Local Notation u := (@CurrentAreaNormalisedImage.value R m n f xi).
Local Notation H := (@hausdorff_measure R Y m).

(** Source for [current_area_undefined_summand_image_null]:
    the exceptional-image step in Federer 4.1.25,
    p. 383, from the complete 3.2.3 reduction. The
    normalized summand retains its exact partial domain;
    no default differential is used. *)
Theorem current_area_undefined_summand_image_null :
  H (f @` (~` partial_function_domain u)) = 0.
Proof.
have [G [_ [_ [hInjective [_ hImage]]]]] :=
  @measurable_injective_area_subset R m n f setT hLip
    (measure_measurable_whole (@euclidean_lebesgue_is_measure R m)).
have hGDomain : G `<=` partial_function_domain u.
  move=> x hx; have [D [hD hInjectiveD]] := hInjective x hx.
  apply: (@current_area_normalised_image_domain R m n f xi x).2.
  exists D; split; first exact: hD.
  have hPositive := (@euclidean_linear_jacobian_top_positive R m n D).2 hInjectiveD.
  by rewrite lt_def in hPositive; exact: (andP hPositive).1.
apply: (@measure_null_subset R Y H (@hausdorff_measure_is_measure R Y m)
  _ _ _ hImage).
move=> y [x hOutside <-]; exists x; split; first exact: Logic.I.
move=> hx; exact: hOutside (hGDomain x hx).
Qed.

(** Source for [current_area_good_fibres]: for Hausdorff
    almost every target point, every member of its
    original fibre has a valid normalized differential
    summand, supporting the full fibre formula of
    Federer 4.1.25, p. 383. Empty fibres and all
    source and target dimensions are retained. *)
Theorem current_area_good_fibres :
  measure_almost_everywhere H
    [set y | forall x, f x = y -> partial_function_domain u x].
Proof.
pose Bad := f @` (~` partial_function_domain u).
have hAway : measure_almost_everywhere H (~` Bad).
  rewrite /measure_almost_everywhere setCK.
  exact: current_area_undefined_summand_image_null.
apply: (@measure_almost_everywhere_mono R Y H
  (@hausdorff_measure_is_measure R Y m) _ _ _ hAway).
move=> y hAwayY x hx; apply: contrapT => hOutside.
by apply: hAwayY; exists x.
Qed.
End GoodAreaFibres.
