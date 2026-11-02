(** Supporting integral for Federer (1969), 2.7.16, p. 136: "using 2.6.2,
    2.9.20 one inductively computes L^n(S) = int_0^1 L^{n-1}{...} dL^1 t =
    int_0^1 (1-t)^{n-1}/(n-1)! dL^1 t = 1/n!". The reference 2.9.20 is used
    for the elementary evaluation int_0^1 (1-t)^m dL^1 t = 1/(m+1). Section
    2.9 is not yet formalised; the evaluation is proved here from the
    uniform primitive criterion of the Riemann integral and its agreement
    with the integral with respect to L^1 on segments (2.5.17, p. 111), as
    for the elementary integrals of 2.6.3(2), p. 118. The primitive
    -(1-t)^{m+1} is obtained from the product rule by induction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype realfun.
From mathcomp Require Import lra ring.
From Federer Require Import RealMetricBackground UniformPrimitiveUP UniformPrimitiveAlgebra
  UniformPrimitiveProduct UniformPrimitiveIntegral StieltjesIntegral LebesgueScalarMeasure
  LebesgueRiemannContinuous MeasureSubsetIntegral SummableRealFunctionUP SummableRealArithmetic
  MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PowerIntegral.
Variable R : realType.

(** Source for [complement_power_continuous]: t |-> (1 - t)^m is
    continuous on R, supporting Federer 2.7.16, p. 136. *)
Lemma complement_power_continuous (m : nat) : continuous (fun t : R => (1 - t) ^+ m).
Proof.
move=> t; apply: (@continuous_comp R R R (fun s => 1 - s) (fun s => s ^+ m)).
- apply: (@continuousB R R^o R^o (fun _ => 1) (fun s => s) t); first exact: cst_continuous.
  exact: cvg_id.
- exact: exprn_continuous.
Qed.

(** Source for [complement_identity_primitive]: t |-> 1 - t is a
    primitive of the constant -1 on every segment, supporting Federer
    2.7.16, p. 136. *)
Lemma complement_identity_primitive (a b : R) :
  is_uniform_primitive_on (fun _ => -1) (fun t : R => 1 - t) a b.
Proof.
move=> e he; exists 1; split=> // s u t has hsu hut htb _.
have he0 : (1 - t) - (1 - s) - (-1) * (t - s) = 0 by lra.
by rewrite he0 normr0 mulr_ge0 ?subr_ge0 ?(le_trans hsu hut) // ltW.
Qed.

(** Source for [complement_power_primitive]: t |-> (1 - t)^(m+1) is a
    primitive of -(m+1)(1 - t)^m on every segment, by the product rule
    and induction; supporting the computation of Federer 2.7.16,
    p. 136. *)
Lemma complement_power_primitive (m : nat) (a b : R) :
  is_uniform_primitive_on (fun t => - (m.+1%:R) * (1 - t) ^+ m) (fun t : R => (1 - t) ^+ m.+1) a b.
Proof.
elim: m=> [|m ih].
- apply: (uniform_primitive_ext _ (complement_identity_primitive a b))=> t _.
  by rewrite expr0 expr1 mulr1.
- have hc1 : continuous (fun _ : R => -1 : R) by move=> t; exact: cst_continuous.
  have hc2 : continuous (fun t : R => 1 - t).
    move=> t; apply: (@continuousB R R^o R^o (fun _ => 1) (fun s => s) t); first exact: cst_continuous.
    exact: cvg_id.
  have hc3 : continuous (fun t : R => - (m.+1%:R) * (1 - t) ^+ m).
    move=> t; apply: (@continuousM R R (fun _ => - (m.+1%:R)) (fun s => (1 - s) ^+ m) t).
    + exact: cst_continuous.
    + exact: complement_power_continuous.
  have h := uniform_primitive_product hc1 hc2 hc3 (@complement_power_continuous m.+1)
    (complement_identity_primitive a b) ih.
  apply: (uniform_primitive_ext _ h)=> t _; split.
  + rewrite !exprS; set p := (1 - t) ^+ m.
    rewrite -[m.+2%:R]natr1 -[m.+1%:R]natr1; ring.
  + by rewrite [RHS]exprS.
Qed.

(** Source for [complement_power_segment_integral]: Federer 2.7.16,
    p. 136, the evaluation int_0^1 (1 - t)^m dL^1 t = 1/(m+1) used with
    2.9.20 in the computation of L^n(S). Supporting theorem. *)
Theorem complement_power_segment_integral (m : nat) :
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[0, 1]
    (real_total_integrand (fun t : R => (1 - t) ^+ m)) (m.+1%:R^-1)%:E.
Proof.
have hi := @lebesgue_riemann_continuous_segment R _ 0 1 (@complement_power_continuous m) ltr01.
suff hv : stieltjes_integral (fun x => x) (fun t : R => (1 - t) ^+ m) 0 1 = m.+1%:R^-1.
  by rewrite hv in hi.
have hp := complement_power_primitive m 0 1.
have hs := uniform_primitive_scale (- (m.+1%:R)^-1) hp.
have hp' : is_uniform_primitive_on (fun t : R => (1 - t) ^+ m)
    (fun t => - (m.+1%:R)^-1 * (1 - t) ^+ m.+1) 0 1.
  apply: (uniform_primitive_ext _ hs)=> t _; split=> //.
  by rewrite mulrA mulNr mulrN opprK mulVf ?mul1r // pnatr_eq0.
have he := uniform_primitive_riemann_integral (@complement_power_continuous m) ler01 hp'.
by rewrite -he subrr subr0 expr0n /= expr1n mulr0 mulr1 sub0r opprK.
Qed.

End PowerIntegral.
