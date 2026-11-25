(** Federer 2.10.27, p. 191: the full real-degree profile
    integral, including both zero endpoints. Positive degree/radius
    use the proved real moment; degree zero reuses the original
    natural profile, and radius zero follows from exact values. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBallVolume
  EuclideanLebesgueDimensions EuclideanBallSectionProfileUP EuclideanBallSectionProfile
  EulerGamma EulerGammaHalfParameters RealHausdorffBallCoefficient RealHausdorffNormalisation RealPower
  RealPowerNaturalHausdorff RealEuclideanBallSectionProfileUP
  RealEuclideanBallSectionProfileNatural RealBallSectionProfilePositiveIntegral
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureConullZeroIntegral
  PartialFunctionUP PartialFunctionBasic SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [real_ball_coefficient_equal_degree]: supporting
    independent-parameter transport for the actual alpha values
    from Federer 2.10.2, p. 171, in the first display of
    2.10.27, p. 191. Equal real degrees give equal coefficients,
    irrespective of their nonnegativity proofs. *)
Lemma real_ball_coefficient_equal_degree (R:realType) (p q:R)
    (hp:0<=p) (hq:0<=q):p=q ->
  real_hausdorff_ball_coefficient hp=real_hausdorff_ball_coefficient hq.
Proof.
move=> h;subst q;rewrite /real_hausdorff_ball_coefficient.
by rewrite (euler_gamma_proof_irrelevant (real_dimension_gamma_parameter hp)
  (real_dimension_gamma_parameter hq)).
Qed.

(** Source for [real_ball_section_profile_integral]: the exact
    first display of Federer 2.10.27, p. 191, for every
    nonnegative real section degree, natural base dimension,
    original centre and nonnegative radius. The pointwise laws
    alone suffice; no measurability or integrability premise is added. *)
Theorem real_ball_section_profile_integral (R:realType) m (k:R) (hk:0<=k)
    (u:inner_metric_space (@euclidean_inner_productP R m)) (r:R) q:
  0<=r ->is_real_euclidean_ball_section_profile hk u r q ->
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (partial_function_total (fun y=>(q y:extended_real_line R)))
    (real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R m))*real_power r (k+m%:R))%:E.
Proof.
move=> hr hq.
case:(eqVneq k 0)=> [he|hkNe].
- subst k.
  pose p:=@euclidean_ball_section_profile R m 0 u r hr.
  have hp:=@euclidean_ball_section_profile_specification R m 0 u r hr.
  have hReal:=@real_ball_section_profile_natural_laws R m 0 hk u r p hp.
  have he:q=p:=real_ball_section_profile_unique hq hReal.
  rewrite he.
  have hAlpha:real_hausdorff_ball_coefficient (addr_ge0 hk (ler0n R m))=
      euclidean_unit_ball_volume R m.
    rewrite (@real_ball_coefficient_equal_degree R (0+m%:R) m%:R
      (addr_ge0 hk (ler0n R m)) (ler0n R m) (add0r _)).
    exact:real_hausdorff_ball_coefficient_natural.
  rewrite hAlpha add0r (@real_power_natural_exponent R r m hr).
  have hi:=@euclidean_ball_section_profile_integral R m 0 u r hr.
  by rewrite add0n in hi.
have hkPos:0<k by rewrite lt_neqAle eq_sym hkNe hk.
case:(ltP 0 r)=> hrPos.
- exact:(@real_ball_section_profile_positive_integral R m k hk u r q hkPos hrPos hq).
- have he:r=0 by apply/eqP;rewrite eq_le hrPos hr.
  subst r.
  have hDegree:0<k+m%:R by have hm:=ler0n R m;lra.
  rewrite real_power_zero_base ?(lt0r_neq0 hDegree) // mulr0.
  have hZero y:q y=0%E.
    case:(leP (mdist u y) 0)=> hy.
    + have hd:mdist u y=0 by apply/eqP;rewrite eq_le hy mdist_ge0.
      by rewrite (real_ball_section_profile_inside hq hy) hd expr0n subrr sqrtr0
        real_power_zero_base // mulr0.
    + exact (@real_ball_section_profile_outside R m k hk u 0 q hq y hy).
  apply:(@measure_almost_zero_integral R
    (inner_metric_space (@euclidean_inner_productP R m))
    (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m) _).
  apply:(@measure_almost_everywhere_mono R _ _ (euclidean_lebesgue_is_measure R m)
    setT _ _ (measure_almost_everywhere_true (euclidean_lebesgue_is_measure R m)))=>y _.
  exact (hZero y).
Qed.
