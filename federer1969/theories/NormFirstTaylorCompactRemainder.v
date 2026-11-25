(** Federer (1969), 4.1.1, p. 346: compact-
    uniform first Taylor remainders, using exactly
    the compact estimate already proved in
    3.1.11, p. 221. The ordinary differential
    is identified by uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormDifferentialDirectional
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearOne ContinuousMultilinearZero
  NormHigherDifferentialUP NormHigherDifferentialFirst NormRegularity
  NormTaylorRemainderBound NormTaylorCompactRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_first_taylor_compact_remainder]:
    uniformly over each compact K, the first
    Taylor error is at most epsilon times the
    increment norm, supporting the test quotient
    of Federer 4.1.1, p. 346. *)
Theorem norm_first_taylor_compact_remainder (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U K:X->Prop) (f:X->Y):
  norm_class hNX hNY U f 1%N ->
  compact [set x:real_norm_metric_space hNX|K x] ->(K `<=` U) ->
  forall e:R,0<e ->exists d:R,0<d /\ forall a h,
    K a ->NX h<d ->forall L:Hom X Y,
      has_norm_differential NX NY U f a L ->
      NY (f (a+h)-f a-L h)<=e*NX h.
Proof.
move=>hClass hK hKU e he.
pose Z j:=@ContinuousMultilinear.space R j X Y NX NY hNX hNY.
pose ez j:=@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY.
pose ZN j:=@ContinuousMultilinear.norm R j X Y NX NY hNX hNY.
pose hZ j:=@ContinuousMultilinear.laws R j X Y NX NY hNX hNY.
have [D [hD hRem]]:=@norm_class_higher_taylor_compact_uniform R X Y NX NY hNX hNY Z ez ZN hZ U f 0%N hClass.
have [d [hd hb]]:=hRem K hK hKU e he.
exists d; split=>// a h ha hh L hL.
have hFirst:=(@norm_higher_differential_first R X Y NX NY hNX hNY Z ez ZN hZ U f a (D 1%N a)).1
  (hD 1%N (leqnn _) a (hKU a ha)).
have hSame:=norm_differential_unique hNX hNY hFirst hL.
have hValue:norm_taylor_value ez D a h 1%N=f a+L h.
  rewrite /norm_taylor_value big_ord_recr big_ord1 /= ?invr1 ?scale1r.
  have hEmpty:[ffun _: 'I_0=>h]=[ffun _: 'I_0=>(0:X)].
    exact:zero_arity_arguments_unique.
  rewrite hEmpty (hD 0%N (leq0n _) a (hKU a ha)).2.
  congr (_+_).
  change ((continuous_multilinear_one_operator (hZ 1%N) (D 1%N a)) h=L h).
  by rewrite hSame.
have hBound:NY (f (a+h)-norm_taylor_value ez D a h 1%N)<=e*NX h.
  have hRaw:= (hb a h ha hh).2.
  by rewrite /= ?mulr1 ?expr1 in hRaw.
rewrite hValue opprD addrA in hBound; exact hBound.
Qed.
