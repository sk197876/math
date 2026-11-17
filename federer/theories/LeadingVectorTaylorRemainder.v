(** Federer (1969), 3.4.12, p. 339, extending 3.4.11, p. 338:
    the first nonzero homogeneous Taylor term has
    the printed little-o remainder in all source
    directions. Apply the existing compact-uniform Taylor
    theorem of 3.1.11, p. 221, to the
    singleton centre and the actual lower zero jets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormClassOneUP NormRegularity
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  NormTaylorRemainderBound NormTaylorCompactRemainder NormTaylorHomogeneousCoefficient
  NormTaylorLineValues HomogeneousPolynomialFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Remainder.
Variable R:realType.
Variables X Y:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Variable NY:Y->R.
Variable hNY:is_real_norm NY.
Local Notation N:=NY.
Local Notation hN:=hNY.
Local Notation Z:=(fun i=>@ContinuousMultilinear.space R i X Y NX N hNX hN).
Local Notation ev:=(fun i=>@ContinuousMultilinear.evaluation R i X Y NX N hNX hN).
Local Notation ZN:=(fun i=>@ContinuousMultilinear.norm R i X Y NX N hNX hN).
Local Notation hZ:=(fun i=>@ContinuousMultilinear.laws R i X Y NX N hNX hN).

(** Source for [leading_vector_actual_taylor_remainder]: the first
    displayed remainder in 3.4.11, p. 338,
    with the exact factorial-normalized polynomial and the
    actual lower differential fields. No nonzero increment
    or completeness hypothesis is added. *)
Theorem leading_vector_actual_taylor_remainder (A:set X) (f:X->Y)
    (D:forall i,X->Z i) k:
  let P:=fun v=>((k.+1)`!)%:R^-1*:@ev k.+1 [ffun _=>v] (D k.+1 0) in
  A 0 ->
  (forall i,(i<=k.+1)%N ->forall x,A x ->
    has_norm_higher_differential NX ev ZN A f i x (D i x)) ->
  norm_class_zero NX (@ZN k.+1) A (D k.+1) ->
  (forall i,(i<k.+1)%N ->D i 0=0) ->
  @is_homogeneous_polynomial R X Y k.+1 P /\
  norm_class_zero NX N setT P /\
  (forall (t:R) v,P (t*:v)=t^+k.+1*:P v) /\
  forall e:R,0<e ->exists r:R,0<r /\forall x,NX x<r ->
    A x /\NY (f x-P x)<=e*(NX x)^+k.+1.
Proof.
move=>P ha hD hContinuous hLower.
have hTop:=hD k.+1 (leqnn _) 0 ha.
have [hPolynomial hSmooth]:=@norm_taylor_homogeneous_coefficient R X Y NX N hNX hN
  A f k.+1 0 (D k.+1 0) hTop.
split;first exact:hPolynomial.
split;first exact:(norm_class_continuous (hSmooth 0%N)).
split.
- move=>t v;rewrite /P (continuous_multilinear_diagonal_scale (hZ k.+1)) !scalerA.
  by rewrite [(_*t^+k.+1)]mulrC.
- move=>e he.
  have hK:@compact (real_norm_metric_space hNX) [set 0] by exact:compact_set1.
  have hKA:[set 0] `<=` A by move=>x ->;exact:ha.
  have [r [hr hBound]]:=@norm_taylor_remainder_compact_uniform_fields R X Y NX N
    hNX hN Z ev ZN hZ A [set 0] f D k hD hContinuous hK hKA e he.
  exists r;split;first exact:hr.
  move=>x hx;have [hA hRaw]:=hBound 0 x erefl hx.
  rewrite add0r in hA hRaw.
  have hTaylor:norm_taylor_value ev D 0 x k.+1= P x.
    rewrite /norm_taylor_value big_ord_recr.
    have hZero:(\sum_(i<k.+1) (i`!)%:R^-1*:@ev i [ffun _=>x] (D i 0))=0.
      apply:big1=>i _;rewrite (hLower i (ltn_ord i)) linear0 scaler0;done.
    rewrite hZero.
    change (0+((k.+1)`!)%:R^-1*:@ev k.+1 [ffun _=>x] (D k.+1 0)= P x).
    by rewrite add0r.
  rewrite hTaylor in hRaw.
  split;first exact:hA.
  have hFactor:(1:R)<=((k.+1)`!)%:R by rewrite ler1n fact_gt0.
  have hNonnegative:=real_seminorm_nonnegative hNY.1 (f x-P x).
  have hSmall:=ler_wpM2l hNonnegative hFactor;rewrite mulr1 in hSmall.
  exact:le_trans hSmall hRaw.
Qed.
End Remainder.
