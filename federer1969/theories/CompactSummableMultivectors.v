(** Federer (1969), 4.1.18, p. 375: the original
    Omega_m(U) with its actual multivector mass and
    Lebesgue measure on U. The generic field carrier is
    opaque and retains genuine compact representatives. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentDomain CurrentCoefficientNorms SmoothCompactSet
  MeasureUP EuclideanOpenDomainMeasure CompactSummableFieldSealed
  CompactSummableFieldLaws CompactSummableFieldIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Multivectors.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT:=(current_domain R n U).
Local Notation V:=(exterior_power X m).
Local Notation VN:=(@current_vector_mass R h2 n m).
Local Notation hVN:=(@current_vector_mass_real_norm R h2 n m).
Local Notation mu:=(@euclidean_open_domain_measure R n U).
Local Notation hMu:=(proj1 (@euclidean_open_domain_measure_laws R n U hU)).

(** Source for [compact_summable_multivector_space]:
    Omega_m(U), Federer 4.1.18, p. 375. Its
    original mass norm and measure are unchanged, including
    degree zero and empty U. *)
Definition compact_summable_multivector_space:lmodType R:=
  @CompactSummableField.space R UT V VN hVN mu hMu.

(** Source for [compact_summable_multivector_value]:
    actual U-values of the field in Omega_m(U),
    Federer 4.1.18, p. 375. *)
Definition compact_summable_multivector_value
    (xi:compact_summable_multivector_space):UT->V:=
  @compact_summable_field_value R UT V VN hVN mu hMu xi.

(** Source for [compact_summable_multivector_size]:
    integral_U mass(xi), each summand in J,
    Federer 4.1.18, p. 375. *)
Definition compact_summable_multivector_size
    (xi:compact_summable_multivector_space):R:=
  @compact_summable_field_size R UT V VN hVN mu hMu xi.

(** Source for [compact_summable_multivector_size_laws]:
    the original integral size is a seminorm on actual
    compact representatives in Omega_m(U), Federer
    4.1.18, p. 375, by the earlier L1 laws. *)
Theorem compact_summable_multivector_size_laws:
  is_real_seminorm compact_summable_multivector_size.
Proof.
exact:(@compact_summable_field_size_seminorm R UT V VN hVN mu hMu).
Qed.
End Multivectors.
