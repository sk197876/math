(** Federer (1969), 4.1.23, p. 379:
    view the literal full-space Omega coefficient
    as an actual ambient compact L1 field
    before the finite-cell decomposition. Preserve
    every point value and the exact mass
    integral through the existing sealed representative laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentDomain CurrentCoefficientNorms CurrentVectorCompleteness
  CompactSummableFieldSealed CompactSummableFieldLaws CompactSummableFieldRepresentation
  CompactSummableMultivectors CompactSummableMultivectorAmbient
  EuclideanLebesgueDimensions MeasureUP PartialFunctionUP PartialFunctionBasic
  TotalVectorNormIntegrability SummableRealFunctionUP.
From Federer Require Import TotalVectorIntegralDomination.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AmbientFieldRepresentative.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) => norm_full_domain_interior NX x).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation hVN := (@current_vector_mass_real_norm R h2 n m).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation hLeb := (euclidean_lebesgue_is_measure R n).
Local Notation WF := (@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation WA := (@CompactSummableField.space R XT V VN hVN Leb hLeb).
Local Notation raw := (@compact_summable_multivector_ambient_value R h2 n m Full hFull).
Local Notation sizeF := (@compact_summable_multivector_size R h2 n m Full hFull).

(** Source for [compact_summable_ambient_field_representative]:
    the original full-space coefficient
    of Federer 4.1.23, p. 379,
    has an actual ambient compact
    L1 representative with exactly its
    point values and size. No
    almost-equality quotient or ambient default
    point replaces the original coefficient. *)
Theorem compact_summable_ambient_field_representative (xi : WF) :
  exists f : WA,
    @compact_summable_field_value R XT V VN hVN Leb hLeb f=raw xi /\
    @compact_summable_field_size R XT V VN hVN Leb hLeb f=sizeF xi.
Proof.
have hLone := @compact_summable_multivector_ambient_lone R h2 n m Full hFull xi.
have [K [hK [_ hOff]]] := @compact_summable_multivector_ambient_carrier R h2 n m Full hFull xi.
have hGraphOff x y : partial_function_graph (partial_function_total
    (fun x : XT => (raw xi x:real_norm_metric_space hVN))) x y -> ~K x -> y=0.
  move=> hValue hx; change (raw xi x=y) in hValue.
  rewrite -hValue; exact: (@hOff x hx).
have [f [hExtend [_ [_ [_ hSize]]]]] :=
  @compact_summable_partial_field_representative R XT V VN hVN Leb hLeb
    (partial_function_total (fun x : XT => (raw xi x:real_norm_metric_space hVN)))
    hLone.2.1 hLone.2.2.1 K hK hGraphOff.
have hRaw : @compact_summable_field_value R XT V VN hVN Leb hLeb f=raw xi.
  apply: funext=> x; exact: (@hExtend x (raw xi x) (erefl (raw xi x))).
have hNorm := @total_vector_lone_norm_value R XT V VN hVN Leb hLeb (raw xi) (sizeF xi)
  (@compact_summable_multivector_ambient_measurable R h2 n m Full hFull xi)
  (@compact_summable_multivector_ambient_integral R h2 n m Full hFull xi).
rewrite hNorm in hSize.
exists f; split; first exact: hRaw.
exact: esym (EFin_inj hSize).
Qed.
End AmbientFieldRepresentative.
