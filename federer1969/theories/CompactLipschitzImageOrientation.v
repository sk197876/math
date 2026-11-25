(** Federer (1969), 4.1.25, p. 383: the original
    compact support has a finite rectifiable image, so
    the preceding measurable-orientation theorem applies
    to that very image. Reuse 3.2.14 and 3.2.25,
    pp. 251–252 and 261, and the existing compact-image
    mass bound; no new frame or tangent construction is used. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  LipschitzUP LipschitzBasic EuclideanLipschitzRectifiableImage
  RectifiableSetUP RectifiableOrientation CompactLipschitzImageMass
  ExteriorGrading PartialFunctionUP MeasureUP MeasureBasic MeasureAlmostUP HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactImage.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Variable f : X -> Y.
Variable K : set X.
Hypothesis hLip : is_metric_lipschitz setT f.
Hypothesis hK : compact K.
Local Notation W := (f @` K).
Local Notation H := (@hausdorff_measure R Y m).

(** Source for [compact_lipschitz_image_measure_rectifiable]:
    the original image f(spt xi) in Federer 4.1.25,
    p. 383, satisfies the finite Hausdorff rectifiability
    hypotheses of 3.2.25. No target measurability or
    nonempty source hypothesis is added. *)
Theorem compact_lipschitz_image_measure_rectifiable :
  is_measure_m_rectifiable H m W.
Proof.
have hOnK : is_metric_lipschitz K f.
  have [L [hL hBound]] := hLip.
  exists L; split; first exact: hL.
  exact: (@metric_lipschitz_bound_restrict R X Y setT K f L
    (fun _ _ => Logic.I) hBound).
have hCount := @euclidean_lipschitz_image_countably_rectifiable R m Y K f hOnK.
have hMeasure := @hausdorff_measure_is_measure R Y m.
split; last exact: (@compact_lipschitz_image_finite_hausdorff_mass R m n f K hLip hK).
split; first exact: hMeasure.
exists W; split; first exact: hCount.
by rewrite /measure_almost_included setDv (measure_empty hMeasure).
Qed.

(** Source for [compact_lipschitz_image_orientation]: a
    measurable simple unit direction with the actual
    image-set approximate tangent, supporting the common
    fibre direction in Federer 4.1.25, p. 383. The
    earlier 3.2.25 partial-domain statement and its exact
    almost-everywhere qualifications are retained. *)
Theorem compact_lipschitz_image_orientation :
  exists T : partial_function (R_n R n) (exterior_power (R_n R n) m),
    is_rectifiable_measurable_orientation W T /\
    partial_function_domain T `<=` W.
Proof.
exact: (@federer_3_2_25 R m n W compact_lipschitz_image_measure_rectifiable).
Qed.
End CompactImage.
