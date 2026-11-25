(** Federer (1969), 4.1.25, p. 383: the
    original full-fibre density has the stated
    geometry on the image of the literal support
    of the original compact summable source field.
    No arbitrary larger carrier or representative
    replaces that support. All-degree zero and
    signed statements are separated from positive-degree
    literal simplicity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import ModuleQuotient SubspaceCarrier RealNormUP NormDifferentialUP NormOpenDomainLaws
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness ExteriorGrading ExteriorNorm AssociatedSubspace
  SimpleElementary LipschitzUP HausdorffMeasure MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralGraphEquivalence
  MeasureRestriction MeasureApproximateTangentUP ExtendedRealOrderTopology
  PartialFunctionUP CompactSummableMultivectors CompactSummableMultivectorAmbient
  CurrentAreaNormalisedImageSealed CurrentAreaFibreSumUP CurrentAreaFibreDensitySealed
  CurrentAreaFibreDensityDomain CurrentAreaFibreOutsideSupport CurrentAreaFibreGeometry
  EuclideanLebesgueDimensions PartialFunctionBasic CurrentCoefficientNorms
  SummableRealFunctionUP
  FiniteExteriorPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section LipschitzAreaGeometry.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variables m n : nat.
Local Notation X := (R_n R m).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation V := (exterior_power (R_n R n) m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Variable xi : @compact_summable_multivector_space R h2 m m Full hFull.
Local Notation raw := (@compact_summable_multivector_ambient_value R h2 m m Full hFull xi).
Local Notation K := (@compact_summable_multivector_ambient_support R h2 m m Full hFull xi).
Variable f : X -> R_n R n.
Hypothesis hLip : @is_metric_lipschitz R
  (inner_metric_space (@euclidean_inner_productP R m)) Y setT f.
Local Notation W := (f @` K).
Local Notation H := (@hausdorff_measure R Y m).
Local Notation u := (@CurrentAreaNormalisedImage.value R m n f raw).
Local Notation eta := (@CurrentAreaFibreDensity.value R h2 X n m f u).
Local Notation N := (@exterior_norm R h2 (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) m).
Local Notation NS := (@exterior_norm R h2 (R_n R m) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R m) m).
Local Notation Plane := (fun y => measure_approximate_tangent_cone
  (inner_norm_real_norm (@euclidean_inner_productP R n))
  (measure_restrict H W) m y).

(** Source for [current_lipschitz_area_geometry]:
    the full-fibre, simplicity, associated-tangent
    and signed conclusions of Federer 4.1.25,
    p. 383, with the exact original support.
    Positive degree is explicit only for literal
    simplicity; both the actual tangent statement
    for a nonzero total and the original signed
    formula retain degree zero. *)
Theorem current_lipschitz_area_geometry :
  measure_almost_everywhere H [set y | exists v : V,
    partial_function_graph eta y v /\
    ((0 < m)%N -> simple v) /\
    (~W y -> v = 0) /\
    (v != 0 ->
      Plane y = [set z | FedererSimple.T v z] /\
      forall x a, f x = y -> partial_function_graph u x a ->
        exists s : R, (s = 1 \/ s = -1) /\
          a = (s*NS (raw x)) *: ((N v)^-1 *: v))].
Proof.
have hH := @hausdorff_measure_is_measure R Y m.
have [hK [_ hOff]] :=
  @compact_summable_multivector_ambient_support_laws R h2 m m Full hFull xi.
have hGeometry := (measure_almost_everywhere_on_implication H W _).1
  (@current_area_fibre_geometry_on_image R h2 m n f raw K hLip hK hOff).
have hIntegral : exists b : R, is_measure_integral
    (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun x =>
      ((@current_vector_mass R h2 m m (raw x))%:E : extended_real_line R))) b%:E.
  exists (@compact_summable_multivector_size R h2 m m Full hFull xi).
  apply: (measure_integral_graph_equivalent _
    (@compact_summable_multivector_ambient_integral R h2 m m Full hFull xi)) => x z.
  exact: real_total_integrand_graph.
have hDomain := @current_area_fibre_density_conull_domain R h2 m n f raw hLip hIntegral.
apply: (measure_almost_everywhere_mono hH _
  (measure_almost_everywhere_and hH hDomain hGeometry)).
move=> y [[v hValue] hAt].
have hSum := (@CurrentAreaFibreDensity.laws R h2 X n m f u y v).1 hValue.
have hZero : ~W y -> v = 0.
  move=> hOutside.
  exact: (@current_area_fibre_outside_support R h2 m n f raw K y v hOff hOutside hSum).
exists v; split; first exact: hValue.
have [hWY | hOutside] := pselect (W y).
- have [hSimple hGeometryAt] := hAt hWY v hSum.
  split; first exact: hSimple.
  by split.
- have hVZero := hZero hOutside.
  split.
  + move=> hPositive.
    have hSimple := @simple_scale R (R_n R n) m
      (e_lambda (fun _ : 'I_m => (0 : R_n R n)) (ord_tuple m)) 0%R hPositive
      (@product_simple R (R_n R n) m (fun _ : 'I_m => 0%R)).
    rewrite hVZero; move: hSimple; by rewrite scale0r.
  + split; first exact: hZero.
    by rewrite hVZero eqxx.
Qed.
End LipschitzAreaGeometry.
