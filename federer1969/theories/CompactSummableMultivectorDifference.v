(** Federer (1969), 4.1.18, p. 375: differences
    of the actual Omega fields retain their pointwise
    values, literal L1 errors and density-current mass.
    These are the earlier linearity and norm-integral
    laws on the original opaque carriers. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces CurrentMassSealed
  CurrentCoefficientNorms
  CompactSummableFieldLaws CompactSummableFieldIntegral CompactSummableMultivectors
  CompactSummableMultivectorDensity CompactSummableMultivectorLinear CompactSummableMultivectorAmbient
  CompactContinuousVectorZeroExtension EuclideanOpenDomainMeasure MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CompactSummableMultivectorDifference.
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
Local Notation raw:=(@compact_summable_multivector_ambient_value R h2 n m U hU).
Local Notation size:=(@compact_summable_multivector_size R h2 n m U hU).
Local Notation A:=(@compact_summable_multivector_current R h2 n m U hU).
Local Notation H:=(@compact_summable_multivector_current_hom R h2 n m U hU).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Local Notation mu:=(@euclidean_open_domain_measure R n U).
Local Notation hm:=(@euclidean_open_domain_measure_laws R n U hU).1.

(** Source for [compact_summable_multivector_value_difference]:
    subtraction in the actual Omega space is pointwise
    subtraction, supporting the L1 convolution limit of
    Federer 4.1.18, p. 375. *)
Theorem compact_summable_multivector_value_difference (xi eta:W):
  value (xi-eta)=(fun x:UT=>value xi x-value eta x).
Proof.
have hField:xi-eta=(-1)*:eta+xi by rewrite scaleN1r addrC.
rewrite hField /compact_summable_multivector_value
  compact_summable_field_value_add compact_summable_field_value_scale.
apply:funext=>x;by rewrite scaleN1r addrC.
Qed.

(** Source for [compact_summable_multivector_ambient_difference]:
    the original zero extensions preserve differences,
    supporting ordinary field convolution in 4.1.18,
    p. 375, without selecting exterior values. *)
Theorem compact_summable_multivector_ambient_difference (xi eta:W):
  raw (xi-eta)=(fun x:X=>raw xi x-raw eta x).
Proof.
apply:funext=>x;rewrite /compact_summable_multivector_ambient_value
  /compact_vector_open_extension.
case:pselect=>hx;last by rewrite subrr.
by rewrite compact_summable_multivector_value_difference.
Qed.

(** Source for [compact_summable_multivector_difference_integral]:
    the literal integral of mass(xi-eta) is its
    actual Omega L1 size, supporting the convergence
    assertion in Federer 4.1.18, p. 375. *)
Theorem compact_summable_multivector_difference_integral (xi eta:W):
  is_measure_integral mu (real_total_integrand (fun x:UT=>VN (value xi x-value eta x)))
    (size (xi-eta))%:E.
Proof.
have h:=@compact_summable_field_size_integral R UT (exterior_power X m) VN hVN mu hm (xi-eta).
change (is_measure_integral mu
  (real_total_integrand (fun x:UT=>VN (value (xi-eta) x)))
  (size (xi-eta))%:E) in h.
by rewrite compact_summable_multivector_value_difference in h.
Qed.

(** Source for [compact_summable_multivector_difference_symmetric]:
    either orientation of the original L1 error has
    the same value, supporting 4.1.18, p. 375. *)
Theorem compact_summable_multivector_difference_symmetric (xi eta:W):
  size (xi-eta)=size (eta-xi).
Proof.
exact:(@real_seminorm_subtract R W size
  (@compact_summable_multivector_size_laws R h2 n m U hU) xi eta).
Qed.

(** Source for [compact_summable_multivector_current_difference_mass]:
    the original L1 field error equals the mass
    of its actual density-current error, supporting
    Federer 4.1.18, p. 375. No mass claim
    is made here for a boundary or q itself. *)
Theorem compact_summable_multivector_current_difference_mass (xi eta:W):
  @CurrentMass.value R h2 n m U hU (A xi-A eta)=(size (xi-eta))%:E.
Proof.
have hMap:A (xi-eta)=A xi-A eta.
  change (H (xi-eta)=H xi-H eta);exact:linearB.
rewrite -hMap;exact:compact_summable_multivector_current_mass.
Qed.
End CompactSummableMultivectorDifference.
