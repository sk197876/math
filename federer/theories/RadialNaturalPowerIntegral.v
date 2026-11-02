(** Federer (1969), 3.2.35, p. 272:
    the actual scalar polynomial integrals in
    the last line of Steiner's induction. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal
  topology normedtype realfun.
From Federer Require Import UnitPowerIntegral UniformPrimitiveUP UniformPrimitiveAlgebra UniformPrimitiveIntegral
  StieltjesIntegral LebesgueScalarMeasure LebesgueRiemannContinuous LebesgueOpenSegmentIntegral
  MeasureSubsetIntegral SummableRealFunctionUP RealOpenIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radial_natural_power_integral]:
    the exact integral of t^k over 0<t<r
    in Federer 3.2.35, p. 272. The
    existing finite-increment primitive of t^(k+1)
    and its Lebesgue identification prove
    r^(k+1)/(k+1); null endpoints are removed.
    Degree zero remains included. *)
Theorem radial_natural_power_integral (R:realType) k (r:R):
  0<r ->is_measure_subset_integral (@lebesgue_scalar_measure R) (real_open_interval 0 r)
    (real_total_integrand (fun t:R=>t^+k)) (r^+k.+1/k.+1%:R)%:E.
Proof.
move=>hr.
have hCont:continuous (fun t:R=>t^+k) by move=>t; exact:exprn_continuous.
have hI:=@lebesgue_riemann_continuous_segment R _ 0 r hCont hr.
have hBase:=@natural_power_uniform_primitive R k 0 r.
have hScale:=uniform_primitive_scale ((k.+1%:R:R)^-1) hBase.
have hPrimitive:is_uniform_primitive_on (fun t:R=>t^+k)
    (fun t:R=>(k.+1%:R)^-1*t^+k.+1) 0 r.
  apply:(uniform_primitive_ext _ hScale)=>t _; split=>//.
  by rewrite mulrA mulVf ?mul1r // pnatr_eq0.
have hValue:=uniform_primitive_riemann_integral hCont (ltW hr) hPrimitive.
rewrite expr0n /= mulr0 subr0 mulrC in hValue.
rewrite -hValue in hI.
have hOpen:=lebesgue_closed_open_segment_integral hI.
have hInterval:(real_open_interval 0 r)=`]0,r[.
  apply/seteqP; split=>t.
  - move=>[ht0 htr]; rewrite /= in_itv /=; by apply/andP.
  - rewrite /= in_itv /=; move/andP=>[ht0 htr]; by split.
by rewrite hInterval.
Qed.
