(** Federer (1969), 4.1.25, p. 383: assemble
    the original full-fibre geometry on the literal
    compact support image. The last paragraph supplies
    one common tangent plane; the already proved
    numerical-sum laws supply its direction and the
    signed normalized terms. Keep the degree-zero
    simplicity qualification separate from the all-degree
    associated-plane and signed identities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import ModuleQuotient SubspaceCarrier RealNormUP InnerNorm InnerMetric HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorNorm
  AssociatedSubspace SimpleElementary MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureRestriction MeasureApproximateTangentUP HausdorffMeasure LipschitzUP
  PartialFunctionUP CurrentAreaNormalisedImageSealed CurrentAreaNormalisedImageMass
  CurrentAreaFibreSumUP CurrentAreaFibreTermCommonLine CurrentAreaFibreCommonLine
  CurrentSimpleVectorEuclideanNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FibreGeometry.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation V := (exterior_power (R_n R n) m).
Local Notation N := (@exterior_norm R h2 (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) m).
Local Notation NX := (@exterior_norm R h2 (R_n R m) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R m) m).
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

(** Source for [current_area_fibre_geometry_on_image]:
    the simplicity, actual approximate tangent and
    last signed formula of Federer 4.1.25,
    p. 383. Simplicity is asserted in positive
    degrees; both other assertions retain all degrees
    and every original source point of the fibre. *)
Theorem current_area_fibre_geometry_on_image :
  measure_almost_everywhere_on H W [set y | forall eta : V,
    is_current_area_fibre_sum f u y eta ->
    (((0 < m)%N -> simple eta) /\
      (eta != 0 ->
        Plane y = [set z | FedererSimple.T eta z] /\
        forall x v, f x = y -> partial_function_graph u x v ->
          exists s : R, (s = 1 \/ s = -1) /\
            v = (s*NX (xi x)) *: ((N eta)^-1 *: eta)))].
Proof.
have hH := @hausdorff_measure_is_measure R Y m.
have hLine := (measure_almost_everywhere_on_implication H W _).1
  (@current_area_fibre_term_common_line R h2 m n f xi K hLip hK hOff).
apply: (measure_almost_everywhere_on_implication H W _).2.
apply: (measure_almost_everywhere_mono hH _ hLine).
move=> y hAt hWY eta hSum.
have [tau [hSimple [hTau [hPlane hTerms]]]] := hAt hWY.
have hEtaSimple : (0 < m)%N -> simple eta.
  move=> hPositive.
  exact: (@current_area_fibre_sum_positive_simple R h2 X n m f u
    y eta tau hTau hSum hTerms hPositive hSimple).
split; first exact: hEtaSimple.
move=> hEta.
have [c hEtaValue] := @current_area_fibre_sum_common_line R h2 X n m f u
  y eta tau hTau hSum hTerms.
have hC : c != 0.
  apply/eqP => hZero; by move: hEta; rewrite hEtaValue hZero scale0r eqxx.
split.
- rewrite hPlane hEtaValue.
  apply/seteqP; split=> z.
  + exact: (@associated_scale_nonzero R (R_n R n) m tau c hC z).2.
  + exact: (@associated_scale_nonzero R (R_n R n) m tau c hC z).1.
- move=> x v hXY hValue.
  have [s [hSign hSigned]] := @current_area_fibre_sum_signed_terms R h2 X n m
    f u y eta tau hTau hSum hTerms hEta x v hXY hValue.
  have hEtaNorm := @current_simple_vector_euclidean_norm R h2 n m eta hEtaSimple.
  have hTermNorm := @current_area_normalised_image_mass R h2 m n f xi x v hValue.
  have hSourceNorm := @current_top_vector_euclidean_norm R h2 m (xi x).
  exists s; split; first exact: hSign.
  move: hSigned; by rewrite hTermNorm hSourceNorm hEtaNorm.
Qed.
End FibreGeometry.
