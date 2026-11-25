(** Federer (1969), 4.1.7, p. 358: compact
    scalar integrals for the dominated-density argument.
    This adapter reuses compact summability from
    2.5.13, p. 106, and the opaque integral
    functional and Daniell laws of 2.5.1, p. 92. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP RadonMeasureUP RadonBorelRegularity BorelRegularMeasureUP
  FunctionLatticeUP FunctionLatticeLaws CompactSupportFunctionUP CompactSupportFunctionLattice
  CompactSupportSummability SummableRealFunctionUP RealIntegralFunctionalUP RealIntegralFunctional
  RealIntegralFunctionalSealed MonotoneDaniellIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section RadonCompactScalarIntegral.
Variable R:realType.
Variable X:topologicalType.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hr:is_radon_measure mu.
Local Notation Kplus := (positive_function_lattice (@compactly_supported_continuous_functions R X)).

(** Source for [radon_compact_summability]: every
    compact continuous scalar test is summable,
    supporting Federer 4.1.7, p. 358, by
    2.5.13, p. 106. Signed tests retain
    their ordinary finite integrals. *)
Lemma radon_compact_summability:
  @compactly_supported_continuous_functions R X `<=` summable_real_functions mu.
Proof.
move=>f hf.
exact:(@compactly_supported_summable R X mu hm
  (fun B hB=>borel_regular_borel_measurable hm (radon_borel_regular hm hr) hB)
  (fun C hC=>radon_compact_finite hr hC) f hf).
Qed.

(** Source for [radon_compact_integral]: the opaque
    integral on all of K(U), through 2.5.1,
    p. 92, supporting Federer 4.1.7, p. 358. *)
Definition radon_compact_integral:(X->R)->R:=
  @RealIntegralFunctional.value R X mu (@compactly_supported_continuous_functions R X)
    radon_compact_summability.

(** Source for [radon_compact_integral_laws]: the exact
    finite integral of every original signed compact
    continuous test, supporting Federer 4.1.7,
    p. 358, by 2.5.1, p. 92. *)
Lemma radon_compact_integral_laws:
  is_real_integral_functional mu (@compactly_supported_continuous_functions R X) radon_compact_integral.
Proof. exact:RealIntegralFunctional.laws. Qed.

(** Source for [radon_positive_compact_summability]: every
    original compact positive scalar test is summable,
    supporting Federer 4.1.7, p. 358, by
    2.5.13, p. 106, and compact finiteness
    from 2.2.5, pp. 62–63. *)
Lemma radon_positive_compact_summability:Kplus `<=` summable_real_functions mu.
Proof.
move=>f hf.
exact:radon_compact_summability hf.1.
Qed.

(** Source for [radon_positive_compact_integral]: the
    opaque finite compact scalar integral from
    2.5.1, p. 92, supporting Federer 4.1.7,
    p. 358. Values outside K(U)+ are immaterial. *)
Definition radon_positive_compact_integral:(X->R)->R:=
  @RealIntegralFunctional.value R X mu Kplus radon_positive_compact_summability.

(** Source for [radon_positive_compact_integral_laws]: the
    actual integral specification on every original
    K(U)+ test, supporting Federer 4.1.7, p. 358. *)
Lemma radon_positive_compact_integral_laws:
  is_real_integral_functional mu Kplus radon_positive_compact_integral.
Proof. exact:RealIntegralFunctional.laws. Qed.

(** Source for [radon_positive_compact_integral_daniell]:
    the original monotone Daniell laws needed to
    apply 2.5.9, p. 100, in Federer 4.1.7,
    p. 358. These are consequences of the
    existing real integral laws, not new premises. *)
Lemma radon_positive_compact_integral_daniell:
  is_monotone_daniell_integral Kplus radon_positive_compact_integral.
Proof.
exact:(@real_integral_functional_is_monotone_daniell R X mu hm Kplus _
  (positive_function_lattice_laws (@compactly_supported_continuous_functions_lattice R X))
  radon_positive_compact_integral_laws).
Qed.
End RadonCompactScalarIntegral.
