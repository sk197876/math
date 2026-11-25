(** Federer (1969), 3.4.8(8), pp. 329–330:
    the original coordinate quotient is integral
    over its original prefix, its fraction
    extension is finite, and its original
    remaining coordinates generate that field.
    Apply the existing finite-module and field
    results to the checked original quotient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthonormalFamilies FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  OrthogonalGroupTopology AnalyticGermUP AnalyticGermRing AnalyticGermNoetherian
  AnalyticPrefixGermMap AnalyticCoordinateGermsSealed AnalyticRotatedGermIdeal AnalyticReductionActual
  AnalyticReductionFiniteQuotient AnalyticReductionCoordinateGeneration
  CommutativeIdealUP CommutativeQuotientUP CommutativeSubringUP
  RingScalarRestriction RingSubmoduleUP IntegralRingElementUP NoetherianFiniteAlgebraIntegrality
  FractionFieldUP CoefficientFractionFieldUP FiniteFractionFieldModule
  FractionFieldCoordinateGenerators GeneratedRingTailEnumeration OrdinalCoordinateTail
  AnalyticScalarsSealed CommutativePolynomialSealed FiniteFieldPrimitiveDirectionsNull
  EuclideanLebesgueDimensions InnerMetric HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalFields.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Hypothesis hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Variable I:set G.
Hypothesis hI:is_commutative_ideal I.
Hypothesis hProper:~I 1.
Variable g:@orthogonal_group R X B hB n e he.
Variable C:comNzRingType.
Variable pi:{rmorphism G->C}.
Hypothesis hPi:is_commutative_ideal_quotient (@analytic_rotated_germ_ideal R X B hB n e he I g) pi.
Variable m:nat.
Hypothesis hMN:(m<=n)%N.
Hypothesis hAllB:forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g.
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R (R_n R m)
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) 0)].
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega m hMN).
Local Notation scalar:=(GRing.RMorphism.clone A C (pi \o E) _).
Local Notation gamma:=(fun i:'I_n=>@AnalyticCoordinateGerms.value R X NX hNX n e he omega i).
Local Notation suffix:=(fun i:'I_(n-m)=>pi (gamma (ordinal_coordinate_tail_index hMN i))).

(** Source for [analytic_reduction_quotient_integral]:
    the original quotient is integral over
    p(Q_m), 3.4.8(8), p. 329. The
    already proved finite module and Noetherian
    analytic coefficient ring discharge the existing
    finite-algebra integrality theorem. *)
Theorem analytic_reduction_quotient_integral:forall c:C,is_integral_ring_element scalar c.
Proof.
have hFinite:=@analytic_reduction_finite_original_quotient R X B hB n e he hON omega hDual
  I g C pi m hMN hI hProper hPi hAllB.
have hNoetherian:=@finite_analytic_germ_ring_noetherian R (R_n R m)
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) m (@coordinate_basis R m) 0
  (@coordinate_basisP R m).
exact:(@noetherian_finite_algebra_integral A C scalar hNoetherian hFinite).
Qed.

Variable L:fieldType.
Variable inclusion:{rmorphism C->L}.
Hypothesis hFraction:is_commutative_fraction_field inclusion.
Variable M:fieldType.
Variable eta:{rmorphism A->M}.
Variable phi:{rmorphism M->L}.
Hypothesis hCoefficient:is_coefficient_fraction_field
  (GRing.RMorphism.clone A L (inclusion \o scalar) _) eta phi.

(** Source for [analytic_reduction_fraction_field_finite]:
    the original L is finite over M,
    the original coefficient-image field in
    3.4.8(8), pp. 329–330. Its defining
    scalar triangle and the actual finite
    quotient prove this field-module conclusion. *)
Theorem analytic_reduction_fraction_field_finite:
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType M of ring_restricted_space phi L^o]).
Proof.
have hFinite:=@analytic_reduction_finite_original_quotient R X B hB n e he hON omega hDual
  I g C pi m hMN hI hProper hPi hAllB.
apply:(@finite_algebra_fraction_field_module A C M L scalar inclusion eta phi hFraction _ hFinite).
exact:coefficient_fraction_scalar_triangle hCoefficient.
Qed.

(** Source for [analytic_reduction_fraction_coordinate_generators]:
    the original remaining coordinate classes
    and M generate the original L as
    a ring, 3.4.8(8), pp. 329–330.
    The proved ordinal-tail enumeration preserves
    exactly those original coordinates. *)
Theorem analytic_reduction_fraction_coordinate_generators:
  is_generated_commutative_subring
    (fun y:L=>(exists i:'I_(n-m),y = inclusion (suffix i)) \/exists a:M,y = phi a) setT.
Proof.
have hOriginal:=@analytic_reduction_original_coordinate_generators R X B hB n e he hON omega hDual
  I g C pi m hMN hI hProper hPi hAllB.
have hIndexed:=@generated_ring_tail_enumeration C n (fun j=>pi (gamma j)) m hMN
  (fun y:C=>exists a:A,y = scalar a) hOriginal.
apply:(@fraction_field_original_coordinate_generators A C M L scalar inclusion eta phi
  (n-m)%N suffix hFraction _ analytic_reduction_fraction_field_finite hIndexed).
exact:coefficient_fraction_scalar_triangle hCoefficient.
Qed.

(** Source for [analytic_reduction_primitive_suffix_nullity]:
    almost every original real suffix direction
    generates the original L over M,
    3.4.8(8), p. 330. Apply the checked
    primitive-direction theorem to the actual
    quotient and original coordinate classes.
    The determinant-polynomial argument expands the
    printed appeal to separable field extensions. *)
Theorem analytic_reduction_primitive_suffix_nullity:
  let realScalar:=GRing.RMorphism.clone R M (eta \o
    (@AnalyticScalars.map R (R_n R m) (inner_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R m)) 0)) _ in
  let bad:=fun v:R_n R (n-m)=>~is_generated_commutative_subring
    (fun y:L=>y = \sum_i phi (realScalar (v i))*inclusion (suffix i) \/
      exists a:M,y = phi a) setT in
  @euclidean_lebesgue_measure R (n-m) bad = 0%:E /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n-m))) (n-m-1)
    [set v|bad v /\inner_norm (@euclidean_inner_productP R (n-m)) v = 1] = 0%:E.
Proof.
move=>realScalar bad.
exact:(@finite_field_primitive_real_directions_null R M L realScalar phi (n-m)%N
  (fun i=>inclusion (suffix i)) (CommutativePolynomial.space M) (CommutativePolynomial.embed M)
  (CommutativePolynomial.variable M) (@CommutativePolynomial.coefficient M) (CommutativePolynomial.laws M)
  analytic_reduction_fraction_field_finite analytic_reduction_fraction_coordinate_generators).
Qed.
End OriginalFields.
