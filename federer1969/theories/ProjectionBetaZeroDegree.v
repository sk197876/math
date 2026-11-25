(** Federer (1969), 3.2.35, p. 271:
    the zeroth intrinsic-volume normalization agrees
    with the existing empty-product projection gauge. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm OrthogonalProjectionConstants
  ProjectionBeta ProjectionConstantNorms ExteriorDiameterUP ExteriorNorm ExteriorNormNaturality
  WirtingerZeroDegree RealPower ExtendedPositivePower ProbabilityConstantIntegral MeasureIntegralUP
  MeasureIntegralGraphEquivalence SummableRealFunctionUP PartialFunctionUP CompactGroupHaarNormalisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [projection_constant_zero_degree_one]:
    supporting beta_t(n,0)=1 for the convention
    zeta^0(S)=1 in Federer 3.2.35,
    p. 271. The literal simple degree-zero
    vector and its actual exterior image both
    have norm one. Probability integration proves
    the defining constant laws before uniqueness
    identifies the existing opaque beta. *)
Lemma projection_constant_zero_degree_one (R:realType) (h2:(1+1:R)!=0) n (t:R):
  0<t ->is_projection_constant h2 t n 0 1.
Proof.
move=>ht; split; first exact:ltr01.
move=>mulS invS eS hS phi hPhi xi hSimple.
have [nu [hNu hRep hm hTotal]]:=normalised_invariant_measure_integral hPhi.
have hNorm:exterior_norm h2 (@euclidean_inner_productP R n) xi= 1.
  exact:two_form_zeroth_simple_norm hSimple.
have hProjection p:projection_norm h2 xi p= 1.
  apply:two_form_zeroth_simple_norm.
  exact:exterior_power_map_simple hSimple.
have hConst:=@probability_constant_integral R _ phi hm 1 hPhi.2.
exists (1:R)%:E.
- apply:(measure_integral_graph_equivalent _ hConst)=>p z.
  rewrite real_total_integrand_graph hProjection real_power_one_base.
  reflexivity.
- by rewrite hNorm mul1r /extended_positive_power real_power_one_base.
Qed.

(** Source for [projection_beta_zero_degree]: the
    actual beta at degree zero is one,
    supporting the literal zeta^0 convention in
    Federer 3.2.35, p. 271. Every finite
    exponent at least one is retained. *)
Theorem projection_beta_zero_degree (R:realType) n (h0n:(0<=n)%N) (t:R):
  1<=t ->@projection_beta R n 0 h0n t%:E= 1.
Proof.
move=>ht; have ht0:0<t:=lt_le_trans ltr01 ht.
have htE:(1<=t%:E)%E by rewrite lee_fin.
exact:(projection_constant_unique h0n ht0
  (@projection_beta_specification R n 0 h0n t%:E htE)
  (projection_constant_zero_degree_one (real_exterior_two_nonzero R) n ht0)).
Qed.
