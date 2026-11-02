(** Federer (1969), 3.2.13, p. 250: actual
    Lebesgue costs of the dyadic intervals used to
    prove the finite defining Gamma integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground GammaDyadicIntervals LebesgueScalarMeasure
  MeasureUP BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Close Scope ereal_scope.

(** Source for [gamma_origin_interval_segment]: the
    near-zero covering intervals for Gamma in Federer
    3.2.13, p. 250, expressed as actual segments. *)
Lemma gamma_origin_interval_segment (R:realType) n:
  @gamma_origin_interval R n=`[(1/2)^+n/2,(1/2)^+n].
Proof.
apply/seteqP; split=>x; rewrite /gamma_origin_interval /= in_itv /=.
- by move=>[h1 h2]; apply/andP; split.
- by move=>/andP[h1 h2]; split.
Qed.

(** Source for [gamma_tail_interval_segment]: the tail
    covering intervals for Gamma in Federer 3.2.13,
    p. 250, expressed as actual segments. *)
Lemma gamma_tail_interval_segment (R:realType) n:
  @gamma_tail_interval R n=`[2^+n,2^+n.+1].
Proof.
apply/seteqP; split=>x; rewrite /gamma_tail_interval /= in_itv /=.
- by move=>[h1 h2]; apply/andP; split.
- by move=>/andP[h1 h2]; split.
Qed.

(** Source for [gamma_origin_interval_mass]: exact
    Lebesgue cost of a near-zero dyadic interval,
    supporting Gamma finiteness in Federer 3.2.13, p. 250. *)
Lemma gamma_origin_interval_mass (R:realType) n:
  lebesgue_scalar_measure (@gamma_origin_interval R n)=((1/2)^+n/2)%R%:E.
Proof.
have hHalf:(0<(1/2:R))%R by apply:divr_gt0; lra.
have hr:(0<(1/2:R)^+n)%R:=exprn_gt0 n hHalf.
have hOrder:((1/2:R)^+n/2<=(1/2)^+n)%R by lra.
rewrite gamma_origin_interval_segment lebesgue_scalar_segment //.
congr (_%:E); lra.
Qed.

(** Source for [gamma_tail_interval_mass]: exact
    Lebesgue cost of a tail dyadic interval, supporting
    Gamma finiteness in Federer 3.2.13, p. 250. *)
Lemma gamma_tail_interval_mass (R:realType) n:
  lebesgue_scalar_measure (@gamma_tail_interval R n)=(2^+n)%R%:E.
Proof.
have hTwo:(0<(2:R))%R by lra.
have hr:(0<(2:R)^+n)%R:=exprn_gt0 n hTwo.
have hStep:((2:R)^+n.+1= 2*2^+n)%R by rewrite exprS.
have hOrder:((2:R)^+n<= 2^+n.+1)%R by rewrite hStep; lra.
rewrite gamma_tail_interval_segment lebesgue_scalar_segment // hStep.
congr (_%:E); lra.
Qed.

(** Source for [gamma_dyadic_interval_measurable]:
    measurability of both interval covers used for
    Gamma, Federer 3.2.13, p. 250, by
    the existing Borel regularity of scalar Lebesgue measure. *)
Lemma gamma_dyadic_interval_measurable (R:realType) b n:
  measure_measurable (@lebesgue_scalar_measure R)
    (if b then gamma_origin_interval n else gamma_tail_interval n).
Proof.
apply:(@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)).
case:b; rewrite ?gamma_origin_interval_segment ?gamma_tail_interval_segment;
apply:closed_borel_set; exact:segment_closed_real.
Qed.
