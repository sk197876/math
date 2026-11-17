(** Supporting Federer (1969), 3.4.8(5), p. 328:
    public scalar-linear interfaces for the original finite Taylor
    maps. Exact interpolation, ideal-power kernel and remainder are
    consequences of the independent opaque value laws. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  RingScalarRestriction AnalyticScalarsSealed AnalyticGermRing AnalyticVanishingIdealSealed
  CommutativeIdealPowersSealed FiniteJetDegreeIndices AnalyticPolynomialGermSealed
  AnalyticFiniteCoefficientsSealed AnalyticFiniteCoefficientsLinear AnalyticFiniteCoefficientsKernel
  AnalyticTaylorSectionSealed AnalyticTaylorSectionLinear AnalyticTaylorSectionInterpolation
  AnalyticTaylorSectionRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Maps.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation V:=[the lmodType R of ring_restricted_space (@AnalyticScalars.map R X NX hNX 0) G^o].
Local Notation J:=(@AnalyticPolynomialGerms.map R X B hB n e he 0).
Local Notation hJ:=(@AnalyticPolynomialGerms.laws R X B hB n e he 0).
Variable l:nat.
Local Notation W:=[the lmodType R of {ffun finite_jet_degree_indices n l->R^o}].
Local Notation T:=(@AnalyticFiniteTaylorSections.map R X NX hNX n e he l J).
Local Notation hT:=(@AnalyticFiniteTaylorSections.laws R X NX hNX n e he l J).

(** Source for [finite_analytic_taylor_coefficients]: the original
    normalized finite derivative coefficients, supporting Federer
    3.4.8(5), p. 328, with their proved scalar-linear hierarchy. *)
Definition finite_analytic_taylor_coefficients:{linear V->W}:=
  @analytic_finite_coefficient_hom R X NX hNX n e l 0.

(** Source for [finite_analytic_taylor_section]: the original finite
    Taylor polynomial germ, supporting Federer 3.4.8(5), p. 328.
    Its implementation remains opaque; original scalar linearity
    has been proved from its independently specified values. *)
Definition finite_analytic_taylor_section:{linear W->V}:=
  HB.pack T (GRing.isLinear.Build R W V *:%R T
    (@analytic_finite_taylor_section_linear R X NX hNX n e he l J T hJ hT)).

(** Source for [finite_analytic_taylor_interpolation]: original
    finite Taylor interpolation supporting Federer 3.4.8(5), p. 328,
    including degree zero and the zero-dimensional coefficient ring. *)
Lemma finite_analytic_taylor_interpolation:
  cancel finite_analytic_taylor_section finite_analytic_taylor_coefficients.
Proof.
exact:(@analytic_finite_taylor_section_interpolation R X B hB n e he l J hJ T hT
  (@AnalyticFiniteCoefficients.map R X NX hNX n e l 0)
  (@AnalyticFiniteCoefficients.laws R X NX hNX n e l 0)).
Qed.

(** Source for [finite_analytic_taylor_kernel]: original ideal-power
    kernel supporting Federer 3.4.8(5), p. 328. The coefficients vanish
    exactly on the lth power of the original centre-vanishing ideal. *)
Lemma finite_analytic_taylor_kernel z:finite_analytic_taylor_coefficients z = 0 <->
  @CommutativeIdealPowers.value G (@AnalyticVanishingIdeal.value R X NX hNX 0) l z.
Proof.
exact:(@finite_analytic_coefficient_power_kernel R X NX hNX n e he l 0
  (@AnalyticFiniteCoefficients.map R X NX hNX n e l 0)
  (@AnalyticFiniteCoefficients.laws R X NX hNX n e l 0) z).
Qed.

(** Source for [finite_analytic_taylor_remainder]: original finite
    Taylor remainder supporting Federer 3.4.8(5), p. 328. No higher
    derivative is assumed to vanish beyond the chosen truncation. *)
Lemma finite_analytic_taylor_remainder z:
  @CommutativeIdealPowers.value G (@AnalyticVanishingIdeal.value R X NX hNX 0) l
    (z-finite_analytic_taylor_section (finite_analytic_taylor_coefficients z)).
Proof.
exact:(@analytic_finite_taylor_remainder_power R X B hB n e he l J T
  (@AnalyticFiniteCoefficients.map R X NX hNX n e l 0) hJ hT
  (@AnalyticFiniteCoefficients.laws R X NX hNX n e l 0) z).
Qed.
End Maps.
