(** Federer (1969), 4.1.18, p. 375: the first
    summand of q is linear on the actual compactly
    supported L1 field space. Reuse the old literal
    integral action and uniqueness, without constructing
    a different distribution topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing CurrentDomain CurrentSpaces
  CurrentEvaluation CurrentCoefficientNorms CurrentIntegrationCriterion
  MultivectorDualSealed DistributionIntegrationRepresentationUP
  EuclideanOpenDomainMeasure CompactSummableMultivectors
  CompactSummableMultivectorDensity CompactSummableFieldLaws
  MeasureUP MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP SummableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Linear.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT:=(current_domain R n U).
Local Notation W:=(@compact_summable_multivector_space R h2 n m U hU).
Local Notation value:=(@compact_summable_multivector_value R h2 n m U hU).
Local Notation image:=(@compact_summable_multivector_current R h2 n m U hU).
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation DT:=(@current_test_space R h2 n U hU m).
Local Notation ev:=(@current_test_value R h2 n U hU m).
Local Notation action:=(@current_value R h2 n U hU m).
Local Notation mu:=(@euclidean_open_domain_measure R n U).
Local Notation hm:=(proj1 (@euclidean_open_domain_measure_laws R n U hU)).

(** Source for [compact_summable_multivector_current_action]:
    the literal first integral in q(xi,eta) applied
    to an original test, Federer 4.1.18, p. 375. *)
Theorem compact_summable_multivector_current_action (xi:W) (psi:DT):
  is_measure_integral mu
    (real_total_integrand (fun x=>pairing (value xi x) (ev psi (set_val x))))
    (action (image xi) psi)%:E.
Proof.
have h:=distribution_representation_action
  (@compact_summable_multivector_current_representation R h2 n m U hU xi) psi.
have hPoint:(fun x:UT=>@MultivectorDual.evaluation R X m
    (value xi x) (ev psi (set_val x)))=
    (fun x:UT=>pairing (value xi x) (ev psi (set_val x))).
  apply:funext=>x;exact:MultivectorDual.laws.
by rewrite hPoint in h.
Qed.

(** Source for [compact_summable_multivector_current_linear]:
    linearity of xi mapped to Lebesgue^n wedge xi,
    supporting the linear q of Federer 4.1.18, p. 375. *)
Theorem compact_summable_multivector_current_linear:linear image.
Proof.
move=>c xi eta;apply:(@current_values_extensional R h2 n m U hU)=>psi.
pose a:=fun x:UT=>pairing (value xi x) (ev psi (set_val x)).
pose b:=fun x:UT=>pairing (value eta x) (ev psi (set_val x)).
have hA:=@real_total_integral_scale R UT mu hm a
  (action (image xi) psi) c (compact_summable_multivector_current_action xi psi).
have hSum:=@real_total_integral_add R UT mu hm (fun x=>c*a x) b
  (c*action (image xi) psi) (action (image eta) psi) hA
  (compact_summable_multivector_current_action eta psi).
have hPoint:(fun x:UT=>pairing (value (c*:xi+eta) x) (ev psi (set_val x)))=
    (fun x:UT=>c*a x+b x).
  apply:funext=>x.
  rewrite /compact_summable_multivector_value
    compact_summable_field_value_add compact_summable_field_value_scale /=.
  by rewrite /pairing linearD linearZ.
have hActual:=compact_summable_multivector_current_action (c*:xi+eta) psi.
rewrite hPoint in hActual.
have hValues:=congr1 (@fine R) (measure_integral_unique hActual hSum).
rewrite linearD hom_addE linearZ hom_scaleE.
exact:hValues.
Qed.

(** Source for [compact_summable_multivector_current_hom]:
    the actual first linear map entering q, Federer
    4.1.18, p. 375. Its values are the already
    sealed original density currents. *)
Definition compact_summable_multivector_current_hom:Hom W C:=
  @HomMap R W C image
    (introT (asboolP _) compact_summable_multivector_current_linear).
End Linear.
