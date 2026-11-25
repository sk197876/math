(** Federer (1969), 4.1.2, pp. 347-348:
    finite sums commute with the actual vector integral.
    This is the finite form of the interchange used
    for coordinate reconstruction and small Borel partitions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic MeasureUP
  MeasureVectorIntegralUP MeasureVectorIntegralZero TotalVectorIntegralArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [total_vector_integral_sequence_sum]: the finite
    sum interchange underlying the approximations in Federer
    4.1.2, p. 348, from linearity in 2.4.12. *)
Theorem total_vector_integral_sequence_sum (R:realType) (X:choiceType)
    (Y:lmodType R) (N:Y->R) (hN:is_real_norm N)
    (mu:set X->\bar R) (hm:is_measure mu) (I:Type) (s:seq I) (f:I->X->Y) (y:I->Y):
  (forall i,is_measure_vector_integral mu
    (partial_function_total (fun x=>(f i x:real_norm_metric_space hN))) (y i)) ->
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(\sum_(i<-s) f i x:real_norm_metric_space hN))) (\sum_(i<-s) y i).
Proof.
move=>hf; elim:s=>[|i s ih].
- have hZero:(fun x:X=>(\sum_(i<-[::]) f i x:real_norm_metric_space hN))=
      (fun _ : X=>(0:real_norm_metric_space hN)).
    apply:funext=>x; by rewrite big_nil.
  rewrite hZero big_nil; exact:(@measure_vector_integral_zero R X Y N hN mu hm).
- have hCons:(fun x:X=>(\sum_(j<-i::s) f j x:real_norm_metric_space hN))=
      (fun x=>(f i x+\sum_(j<-s) f j x:real_norm_metric_space hN)).
    apply:funext=>x; by rewrite big_cons.
  rewrite hCons big_cons.
  exact:(@total_vector_integral_add R X Y N hN mu hm (f i) (fun x=>\sum_(j<-s) f j x)
    (y i) (\sum_(j<-s) y j) (hf i) ih).
Qed.

(** Source for [total_vector_integral_finite_sum]: the finite
    coordinate sums for the full derivative identity in
    Federer 4.1.2, p. 347, retain
    the actual normed target and integral domain. *)
Theorem total_vector_integral_finite_sum (R:realType) (X:choiceType)
    (Y:lmodType R) (N:Y->R) (hN:is_real_norm N)
    (mu:set X->\bar R) (hm:is_measure mu) (I:finType) (f:I->X->Y) (y:I->Y):
  (forall i,is_measure_vector_integral mu
    (partial_function_total (fun x=>(f i x:real_norm_metric_space hN))) (y i)) ->
  is_measure_vector_integral mu
    (partial_function_total (fun x=>(\sum_i f i x:real_norm_metric_space hN))) (\sum_i y i).
Proof.
move=>hf.
have hSum:=@total_vector_integral_sequence_sum R X Y N hN mu hm I (enum I) f y hf.
have hFun:(fun x:X=>(\sum_(i<-enum I) f i x:real_norm_metric_space hN))=
    (fun x=>(\sum_i f i x:real_norm_metric_space hN)).
  apply:funext=>x; by rewrite big_enum.
by rewrite hFun big_enum in hSum.
Qed.
