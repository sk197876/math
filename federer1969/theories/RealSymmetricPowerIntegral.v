(** Federer 2.10.27, p. 191: the actual one-dimensional
    power integral on a symmetric interval. Reuse the proved positive
    radial integral, scalar reflection, finite integral addition and
    null equality at the origin. No endpoint integrability is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground RealPower RealPowerRadialIntegral
  ScalarReflectionMeasure InjectivePushforwardIntegral MeasurePushforward
  LebesgueScalarMeasure MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality
  MeasureConullZeroIntegral PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  SummableRealFunctionUP SummableRealArithmetic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [real_scalar_reflection_integral]: supporting
    reflection connection for the real section profile in Federer
    2.10.27, p. 191. Reuse 2.4.18 and the already proved scalar
    measure reflection; actual signed integral values are unchanged. *)
Lemma real_scalar_reflection_integral (R:realType) (f:R->R) (a: \bar R):
  is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand f) a ->
  is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (fun x=>f (-x))) a.
Proof.
move=> hi;pose mu:=@lebesgue_scalar_measure R.
pose u (x:R):R:=-x.
have hCancel:cancel u u by move=>x;rewrite /u opprK.
have hPush:measure_pushforward u mu=mu.
  apply:funext=>A;exact:scalar_reflection_preserves_length.
have hTransport:=(@injective_pushforward_integral_iff R R R mu
  (lebesgue_scalar_is_measure R) u (real_total_integrand f) (can_inj hCancel) a).2.
rewrite hPush in hTransport.
apply:(measure_integral_graph_equivalent _ (hTransport hi))=>x z.
change (partial_function_graph (real_total_integrand f) (-x) z <->
  partial_function_graph (real_total_integrand (fun x=>f (-x))) x z).
by rewrite !real_total_integrand_graph.
Qed.

(** Source for [real_symmetric_power_integral]: supporting
    inner vertical integral for the profile identity of Federer
    2.10.27, p. 191. For every p>0 and r>=0, the function
    |t|^(p-1) on [-r,r], zero outside, has actual integral
    2r^p/p. The assigned value at zero does not become an
    integrability premise, and radius zero is included. *)
Theorem real_symmetric_power_integral (R:realType) (p r:R) (g:R->R):
  0<p ->0<=r ->
  (forall x,`|x|<=r ->g x=real_power `|x| (p-1)) ->
  (forall x,r<`|x| ->g x=0) ->
  is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand g)
    (2* p^-1*real_power r p)%:E.
Proof.
move=> hp hr hOn hOff.
pose mu:=@lebesgue_scalar_measure R.
pose hm:=lebesgue_scalar_is_measure R.
have hAway:measure_almost_everywhere mu (~` [set (0:R)]).
  rewrite /measure_almost_everywhere setCK;exact:lebesgue_scalar_singleton.
case:(ltP 0 r)=> hpos.
- pose f:=@positive_radius_power R p r.
  have hi:=@positive_radius_power_integral R p r hp hpos.
  have hn:=real_scalar_reflection_integral hi.
  have hSum:=@real_total_integral_add R R mu hm f (fun x=>f (-x))
    (p^-1*real_power r p) (p^-1*real_power r p) hi hn.
  have hValue:p^-1*real_power r p+p^-1*real_power r p= 2* p^-1*real_power r p by ring.
  rewrite hValue in hSum.
  apply:(measure_integral_almost_equal hm hSum).
  apply:(@measure_almost_everywhere_mono R R mu hm _ _ _ hAway)=>x hx.
  have hxNe:x!=0 by apply/eqP;exact:hx.
  have hEq:g x=f x+f (-x).
    case:(ltP 0 x)=> hxPos.
    + have hNeg:~~(0< -x<=r).
        apply/negP=>/andP [h _];lra.
      have hFn:f (-x)=0 by rewrite /f /positive_radius_power (negbTE hNeg).
      have hAbs:`|x|=x:=ger0_norm (ltW hxPos).
      case:(leP x r)=>hxr.
      * have hGood:0<x<=r by rewrite hxPos hxr.
        have hF:f x=real_power x (p-1) by rewrite /f /positive_radius_power hGood.
        rewrite hF hFn addr0.
        have hAbsBound:`|x|<=r by rewrite hAbs.
        have h:=hOn x hAbsBound;by rewrite hAbs in h.
      * have hBad:~~(0<x<=r) by rewrite hxPos leNgt hxr.
        have hF:f x=0 by rewrite /f /positive_radius_power (negbTE hBad).
        rewrite hF hFn addr0;apply:hOff;by rewrite hAbs.
    + have hxNeg:x<0 by rewrite lt_neqAle hxNe hxPos.
      have hNegPos:0< -x by lra.
      have hAbs:`|x|= -x:=ler0_norm (ltW hxNeg).
      have hBad:~~(0<x<=r) by rewrite ltNge hxPos.
      have hF:f x=0 by rewrite /f /positive_radius_power (negbTE hBad).
      case:(leP (-x) r)=>hxr.
      * have hGood:0< -x<=r by rewrite hNegPos hxr.
        have hFn:f (-x)=real_power (-x) (p-1) by rewrite /f /positive_radius_power hGood.
        rewrite hF hFn add0r.
        have hAbsBound:`|x|<=r by rewrite hAbs.
        have h:=hOn x hAbsBound;by rewrite hAbs in h.
      * have hNo:~~(0< -x<=r) by rewrite hNegPos leNgt hxr.
        have hFn:f (-x)=0 by rewrite /f /positive_radius_power (negbTE hNo).
        rewrite hF hFn addr0;apply:hOff;by rewrite hAbs.
  exists (g x)%:E;split;apply/real_total_integrand_graph=> //;by rewrite hEq.
- have he:r=0 by apply/eqP;rewrite eq_le hpos hr.
  subst r;rewrite real_power_zero_base ?(lt0r_neq0 hp) // mulr0.
  apply:(@measure_almost_zero_integral R R mu hm (real_total_integrand g)).
  apply:(@measure_almost_everywhere_mono R R mu hm _ _ _ hAway)=>x hx.
  apply/real_total_integrand_graph;rewrite hOff //.
  by rewrite normr_gt0;apply/eqP;exact:hx.
Qed.
