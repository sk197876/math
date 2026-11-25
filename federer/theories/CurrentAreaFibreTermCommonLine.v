(** Federer (1969), 4.1.25, p. 383, last
    paragraph: for Hausdorff almost every point of
    the literal compact support image, every normalized
    fibre term belongs to the line of one simple
    unit tangent vector. Reuse 3.2.2, 3.2.17,
    2.10.19(4) and 3.2.25, as Federer does. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import ModuleQuotient SubspaceCarrier Hom RealNormUP NormDifferentialUP InnerNorm InnerMetric
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanLinearMaps
  ExteriorGrading ExteriorNorm AssociatedSubspace SimpleProportionality
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction
  MeasureApproximateTangentUP HausdorffMeasure LipschitzUP
  RectifiableOrientationUP PartialFunctionUP
  CompactLipschitzImageOrientation CurrentAreaRegularFibreTangents
  CurrentAreaNormalisedImageUP CurrentAreaNormalisedImageSealed
  CurrentAreaNormalisedImageAssociated.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FibreTermCommonLine.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Variable f : X -> Y.
Variable xi : R_n R m -> exterior_power (R_n R m) m.
Variable K : set X.
Hypothesis hLip : is_metric_lipschitz setT f.
Hypothesis hK : compact K.
Hypothesis hOff : forall x, ~K x -> xi x = 0.
Local Notation W := (f @` K).
Local Notation H := (@hausdorff_measure R Y m).
Local Notation Plane := (fun y => measure_approximate_tangent_cone
  (inner_norm_real_norm (@euclidean_inner_productP R n))
  (measure_restrict H W) m y).
Local Notation u := (@CurrentAreaNormalisedImage.value R m n f xi).

(** Source for [current_area_fibre_term_common_line]:
    the common fibre direction used to conclude
    Federer 4.1.25, p. 383. K may be the
    exact original support; no larger replacement or
    omission of source points from a fibre is needed.
    A defined zero term also belongs to the line. *)
Theorem current_area_fibre_term_common_line :
  measure_almost_everywhere_on H W [set y |
    exists tau : exterior_power (R_n R n) m,
      simple tau /\ tau != 0 /\
      Plane y = [set z | FedererSimple.T tau z] /\
      forall x v, f x = y -> partial_function_graph u x v ->
        exists c : R, v = c *: tau].
Proof.
have hH := @hausdorff_measure_is_measure R Y m.
have [T [hOrientation _]] :=
  @compact_lipschitz_image_orientation R m n f K hLip hK.
have hOrientationAt :=
  (measure_almost_everywhere_on_implication H W _).1
    (rectifiable_orientation_tangent hOrientation).
have hRegular := @current_area_regular_fibre_tangents R m n f K hLip hK.
apply: (measure_almost_everywhere_on_implication H W _).2.
apply: (measure_almost_everywhere_mono hH _
  (measure_almost_everywhere_and hH hOrientationAt hRegular)).
move=> y [hAt hRange] hWY.
have [tau [hTauValue [hPlane _]]] := hAt hWY.
have [hSimple hUnit] := rectifiable_orientation_unit_simple hOrientation hTauValue.
have hTau : tau != 0.
  by rewrite -(exterior_norm_eq0 (euclidean_two_nonzero R)
    (@euclidean_inner_productP R n)) hUnit oner_eq0.
exists tau; split; first exact: hSimple.
split; first exact: hTau.
split; first exact: hPlane.
move=> x v hXY hValue.
have [->|hV] := eqVneq v 0.
- exists 0; by rewrite scale0r.
have hInK : K x.
  apply: contrapT => hOutside.
  have [D [_ [_ hFormula]]] :=
    (@CurrentAreaNormalisedImage.laws R m n f xi x v).1 hValue.
  have hZero : v = 0.
    by rewrite -hFormula /current_area_normalised_image_coefficient
      (@hOff x hOutside) linear0 scaler0.
  by move: hV; rewrite hZero eqxx.
have [D [hD [hInjective hAssociated]]] :=
  current_area_normalised_image_associated hValue hV.
have hSame : forall z, FedererSimple.T v z <-> FedererSimple.T tau z.
  have hSets : [set z | FedererSimple.T v z] = [set z | FedererSimple.T tau z].
    by rewrite hAssociated -(hRange x hInK hXY D hD hInjective) hPlane.
  move=> z; have hz := congr1 (fun S : set _ => S z) hSets.
  change (FedererSimple.T v z = FedererSimple.T tau z) in hz.
  rewrite hz; exact: iff_refl.
have [c [_ hCoefficient]] := (proj1 (@simple_associated_equal R h2
  (R_n R n) m v tau hV hTau hSimple)) hSame.
by exists c.
Qed.
End FibreTermCommonLine.
