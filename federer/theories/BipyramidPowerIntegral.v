(** Scalar power integral supporting Federer (1969), 2.10.36, p. 198, the
    last volume comparison for the two-apex hull. Its normalised
    negative-height profile is (1+t)^n on [-1,0], with integral 1/(n+1), the
    reflection of the calculation used in 2.7.16, p. 136. All calculus is
    derived from the project's finite-increment primitive and scalar
    Lebesgue integral laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal
  topology normedtype realfun ring.
From Federer Require Import UniformPrimitiveUP UniformPrimitiveAlgebra UniformPrimitiveIntegral UniformPrimitiveReflection
  PowerSegmentIntegral StieltjesIntegral LebesgueScalarMeasure LebesgueRiemannContinuous
  MeasureSubsetIntegral SummableRealFunctionUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [reflected_complement_power_primitive]: supporting
    reflected half-profile primitive for the
    last inequality of 2.10.36, p. 198.
    It is a consequence of the
    already proved complement-power primitive. *)
Lemma reflected_complement_power_primitive (R : realType) (n : nat) :
  is_uniform_primitive_on (fun t : R=>(1+t)^+n)
    (fun t : R=>n.+1%:R^-1*(1+t)^+n.+1) (-1) 0.
Proof.
have hp := @uniform_primitive_reflection R
  (fun t : R=> -(n.+1%:R)*(1-t)^+n) (fun t : R=>(1-t)^+n.+1) 0 1
  (@complement_power_primitive R n 0 1).
rewrite oppr0 in hp.
have hs := uniform_primitive_scale (-(n.+1%:R)^-1) hp.
apply: (uniform_primitive_ext _ hs)=> t _; split.
- by rewrite opprK mulrA mulNr mulrN opprK mulVf ?mul1r // pnatr_eq0.
- by rewrite opprK mulrNN.
Qed.

(** Source for [reflected_complement_power_continuous]: supporting
    continuity of the negative-height profile
    in 2.10.36, p. 198. This
    is elementary continuity of a polynomial. *)
Lemma reflected_complement_power_continuous (R : realType) (n : nat) :
  continuous (fun t : R=>(1+t)^+n).
Proof.
move=> t; apply: (@continuous_comp R R R (fun s=>1+s) (fun s=>s^+n)).
- apply: (@continuousD R R^o R^o (fun _=>1) (fun s=>s) t).
  + exact: cst_continuous.
  + exact: cvg_id.
- exact: exprn_continuous.
Qed.

(** Source for [reflected_complement_power_segment_integral]: supporting
    normalised negative-height integral 1/(n+1)
    for the two-apex volume computation in
    2.10.36, p. 198. This is
    infrastructure for the printed comparison,
    not a separately numbered book assertion. *)
Theorem reflected_complement_power_segment_integral (R : realType) (n : nat) :
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[-1,0]
    (real_total_integrand (fun t : R=>(1+t)^+n)) (n.+1%:R^-1)%:E.
Proof.
have hc := @reflected_complement_power_continuous R n.
have hneg : (-1 : R)<0 by rewrite oppr_lt0 ltr01.
have hi := @lebesgue_riemann_continuous_segment R (fun t : R=>(1+t)^+n) (-1) 0 hc hneg.
have hp := @uniform_primitive_riemann_integral R _ _ (-1) 0 hc (ltW hneg)
  (@reflected_complement_power_primitive R n).
have hv : stieltjes_integral (fun t : R=>t) (fun t : R=>(1+t)^+n) (-1) 0=n.+1%:R^-1.
  by rewrite -hp addr0 subrr expr0n /= expr1n mulr1 mulr0 subr0.
by rewrite hv in hi.
Qed.
