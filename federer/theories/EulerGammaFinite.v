(** Federer (1969), 3.2.13, p. 250: existence
    of a finite defining Gamma integral for every
    positive parameter. The proof uses actual scalar
    Lebesgue measure, dyadic covers and summable majorants. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality
  constructive_ereal topology lra ring.
From Federer Require Import EulerGammaUP EulerGammaBounds EulerGammaMeasurable GammaDyadicBounds
  GammaDyadicCosts GammaDyadicMass GammaDyadicIntervals CountableIntegralMajorant RealPower
  RealExponentialSealed LebesgueScalarMeasure MeasureUP MeasurableFunctionUP MeasurableGraphEquivalence
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension MeasureIntegralUP MeasureIntegralGraphEquivalence
  NonnegativeSum MeasureSubsetIntegral SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gamma_positive_completion_subset_graph]:
    exact graph of the positive-ray Gamma integrand,
    Federer 3.2.13, p. 250. No value
    outside the integration domain contributes to the integral. *)
Lemma gamma_positive_completion_subset_graph (R:realType) (s:R) x z:
  partial_function_graph (partial_function_total
    (fun x:R=>((gamma_positive_completion s x)%:E:extended_real_line R))) x z <->
  partial_function_graph (partial_function_zero_extension (0:extended_real_line R)
    [set x:R|(0<x)%R] (real_total_integrand (euler_gamma_integrand s))) x z.
Proof.
rewrite partial_function_zero_extension_graph real_total_integrand_graph.
change (((gamma_positive_completion s x)%:E=z)<->
  ((0<x)%R /\(euler_gamma_integrand s x)%:E=z) \/ (~(0<x)%R /\z= 0)).
rewrite /gamma_positive_completion; case:ifP=>hx; split.
- by move=>hz; left; split.
- by move=>[[hx' hz]|[hx' hz]]=>//; exfalso; exact:hx' hx.
- by move=>hz; right; split=>//; symmetry.
- move=>[[hx' hz]|[hx' hz]].
  + by discriminate hx'.
  + by symmetry.
Qed.

(** Source for [euler_gamma_finite_integral]: actual
    finite defining integral of Gamma(s), s>0,
    Federer 3.2.13, p. 250. The proof
    covers the singular origin and the unbounded tail;
    integrability is a conclusion rather than a premise. *)
Theorem euler_gamma_finite_integral (R:realType) (s:R):
  (0<s)%R ->exists a:R,(0<=a)%R /\
    is_measure_subset_integral (@lebesgue_scalar_measure R) [set x:R|(0<x)%R]
      (real_total_integrand (euler_gamma_integrand s)) a%:E.
Proof.
move=>hs.
pose p:=(Num.min s 1)%R.
have hp:(0<p)%R by rewrite /p lt_min hs ltr01.
have hp1:(p<= 1)%R by rewrite /p ge_min lexx orbT.
have hps:(p<=s)%R by rewrite /p ge_min lexx.
pose q:=real_power (1/2:R) p.
pose C:=real_power (2:R) (1-p).
pose k:=Num.truncn s.
pose D:=(((k.+2)%:R:R)^+k.+2)%R.
have hHalf:(0<(1/2:R))%R by apply:divr_gt0; lra.
have hHalf1:((1/2:R)<1)%R by lra.
have hq:(0<=q)%R:=real_power_nonnegative _ _.
have hq1:(q<1)%R.
  have hh:=real_power_strict_monotone (ltW hHalf) hHalf1 hp.
  by rewrite real_power_one_base in hh.
have hC:(0<=C)%R:=real_power_nonnegative _ _.
have hD:(0<=D)%R by apply:exprn_ge0; exact:ler0n.
have hk:(s<=k.+1%:R)%R.
  have /andP[_ hh]:=truncn_itv (ltW hs); exact:ltW hh.
pose B (j:bool*nat):set R:=if j.1 then gamma_origin_interval j.2 else gamma_tail_interval j.2.
pose c (j:bool*nat):R:=
  (if j.1 then C*q^+j.2/(1/2)^+j.2 else D*((2^+j.2)^-1)^+2)%R.
pose u (x:R):extended_real_line R:=(gamma_positive_completion s x)%:E.
have hu:is_measure_measurable_function (@lebesgue_scalar_measure R) (partial_function_total u).
  apply:measurable_function_graph_equivalent _ (gamma_positive_completion_measurable s)=>x z.
  by rewrite real_total_integrand_graph.
have hu0 x:0<=u x.
  rewrite /u /gamma_positive_completion; case:ifP=>hx; rewrite lee_fin.
  - exact:ltW (euler_gamma_integrand_positive s hx).
  - exact:lexx.
have hB j:measure_measurable (@lebesgue_scalar_measure R) (B j).
  exact:gamma_dyadic_interval_measurable.
have hc j:(0<=c j)%R.
  case:j=>[b n]; case:b; rewrite /c /=.
  - apply:divr_ge0.
    + exact:mulr_ge0 hC (exprn_ge0 n hq).
    + exact (exprn_ge0 n (ltW hHalf)).
  - exact (mulr_ge0 hD (sqr_ge0 (((2:R)^+n)^-1))).
have hBound j x:B j x ->u x<=(c j)%:E.
  case:j=>[b n]; case:b=>hx.
  - have hr:(0<(1/2:R)^+n)%R:=exprn_gt0 n hHalf.
    have hTwo:(0<(2:R))%R by lra.
    have hx0:(0<x)%R:=lt_le_trans (divr_gt0 hr hTwo) hx.1.
    rewrite /u /gamma_positive_completion hx0 lee_fin.
    exact:gamma_dyadic_origin_upper hp hp1 hps hx.
  - have hTwo:(0<(2:R))%R by lra.
    have hx0:(0<x)%R:=lt_le_trans (exprn_gt0 n hTwo) hx.1.
    rewrite /u /gamma_positive_completion hx0 lee_fin.
    exact:gamma_dyadic_tail_upper hk hx.
have hCover x:0<u x ->exists j,B j x.
  rewrite /u /gamma_positive_completion; case:ifP=>hx; last by rewrite ltxx.
  move=>_; case:(leP x 1%R)=>hx1.
  - have [n hn]:=gamma_origin_intervals_cover hx hx1; exists (true,n); exact hn.
  - have [n hn]:=gamma_tail_intervals_cover (ltW hx1); exists (false,n); exact hn.
have hCost:nonnegative_sum setT (fun j=>(c j)%:E*lebesgue_scalar_measure (B j))< +oo.
  exact:gamma_dyadic_total_cost_finite hC hD hq hq1.
have [a [ha hI]]:=@countable_integral_majorant_finite R R [the countType of ((bool*nat)%type:Type)]
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) u B c hu hu0 hB hc hBound hCover hCost.
exists a; split=>//.
apply:measure_integral_graph_equivalent _ hI=>x z.
exact:gamma_positive_completion_subset_graph.
Qed.
