(** Federer (1969), 4.1.7, p. 359:
    actual smooth precomposition is bounded
    on each original compact derivative seminorm.
    The input seminorm uses precisely the
    compact image of the source index.
    Reuse the finite composition estimate of
    3.1.11, p. 222. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearZero
  SmoothCompactSet SmoothCompactImage SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothDerivativeSeminormUP SmoothPrecompositionUP SmoothPrecompositionPositiveBound
  SmoothPrecompositionInnerBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothPrecompositionSeminormBound.
Variable R:realType.
Variables X Y T:lmodType R.
Variables (NX:X->R) (NY:Y->R) (NT:T->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNT:is_real_norm NT).
Variables (A:X->Prop) (B:Y->Prop).
Variables E F:lmodType R.
Variables (ev:E->Y->T) (fv:F->X->T).
Hypothesis hE:is_smooth_function_space hNY hNT B ev.
Local Notation W := (fun j=>@ContinuousMultilinear.space R j Y T NY NT hNY hNT).
Local Notation ew := (fun j=>@ContinuousMultilinear.evaluation R j Y T NY NT hNY hNT).
Local Notation WN := (fun j=>@ContinuousMultilinear.norm R j Y T NY NT hNY hNT).
Local Notation hW := (fun j=>@ContinuousMultilinear.laws R j Y T NY NT hNY hNT).
Local Notation V := (fun j=>@ContinuousMultilinear.space R j X T NX NT hNX hNT).
Local Notation et := (fun j=>@ContinuousMultilinear.evaluation R j X T NX NT hNX hNT).
Local Notation VN := (fun j=>@ContinuousMultilinear.norm R j X T NX NT hNX hNT).
Local Notation hV := (fun j=>@ContinuousMultilinear.laws R j X T NX NT hNX hNT).
Variable D:forall j,Y->Hom E (W j).
Variable G:forall j,X->Hom F (V j).
Hypothesis hD:@is_smooth_function_derivatives R Y T NY NT hNY hNT B E ev D.
Hypothesis hG:@is_smooth_function_derivatives R X T NX NT hNX hNT A F fv G.
Variable f:X->Y.
Hypothesis hImage:forall x,A x->B (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY A f.
Variable P:Hom E F.
Hypothesis hP:is_smooth_precomposition A ev fv f P.
Local Notation image := (@smooth_compact_image R X Y NX NY hNX hNY A B f hImage
  (@norm_class_continuous R X Y NX NY hNX hNY A f 0%N (hf 0%N))).

(** Source for [smooth_precomposition_seminorm_bound]:
    the original compact derivative seminorm
    of a precomposition is bounded by
    a finite multiple of the same-order
    seminorm on f(K), supporting Federer
    4.1.7, p. 359. Neither compact
    image nor inner derivative bounds are
    additional hypotheses in this conclusion. *)
Theorem smooth_precomposition_seminorm_bound (K:smooth_compact_set hNX A) i
    (p:E->R) (q:F->R):
  @is_smooth_derivative_seminorm R Y T NY NT hNY hNT B E D (image K) i p->
  @is_smooth_derivative_seminorm R X T NX NT hNX hNT A F G K i q->
  exists L:R,0<=L /\forall h,q (P h)<=L * p h.
Proof.
move=>hp hq.
have [df [hdf [C [hC hInner]]]]:=smooth_precomposition_inner_compact_bound hf K i.
have hStep (j:'I_i.+1):exists L:R,0<=L /\forall x,smooth_compact_carrier K x->
    forall h,@VN j (@G j x (P h))<=L * p h.
  case:j=>j hj;case:j hj=>[|j] hj.
  - exists 1;split;first exact:ler01.
    move=>x hx h;rewrite mul1r.
    have hxA:=smooth_compact_in_domain K x hx.
    have hOut:=smooth_derivative_exact hG 0%N (P h) hxA.
    have hIn:=smooth_derivative_exact hD 0%N h (hImage x hxA).
    rewrite (@continuous_multilinear_zero_norm R X T (V 0%N) NX NT hNT
      (@et 0%N) (@VN 0%N) (hV 0%N) (@G 0%N x (P h))) hOut.2 (@hP h x hxA).
    rewrite -hIn.2 -(@continuous_multilinear_zero_norm R Y T (W 0%N) NY NT hNT
      (@ew 0%N) (@WN 0%N) (hW 0%N) (@D 0%N (f x) h)).
    apply:(smooth_derivative_seminorm_bound hp h (leq0n i)).
    by exists x.
  - have hPositive:(1<=j.+1)%N by [].
    have [L [hL hBound]]:=@smooth_precomposition_positive_bound R X Y T NX NY NT
      hNX hNY hNT A B E F ev fv hE D G hD hG f hImage hf P hP j.+1 C hPositive hC.
    exists L;split=>// x hx h.
    have hOrder:(j.+1<=i)%N by move:hj;rewrite ltnS.
    have hInnerHere ell (hell:(1<=ell<=j.+1)%N):
        @ContinuousMultilinear.norm R ell X Y NX NY hNX hNY (df ell x)<=C.
      exact:hInner ell (leq_trans (andP hell).2 hOrder) x hx.
    have hOuter ell (hell:(1<=ell<=j.+1)%N):@WN ell (@D ell (f x) h)<=p h.
      apply:(smooth_derivative_seminorm_bound hp h (leq_trans (andP hell).2 hOrder)).
      by exists x.
    exact:(hBound df hdf x (smooth_compact_in_domain K x hx) hInnerHere h (p h)
      (smooth_derivative_seminorm_nonnegative hp h) hOuter).
have [l hl]:=choice hStep.
pose L:=\sum_(j:'I_i.+1) l j.
have hL:0<=L by apply:sumr_ge0=>j _;exact:(hl j).1.
exists L;split=>// h.
apply:(@smooth_derivative_seminorm_least R X T NX NT hNX hNT A F G K i q hq
  (P h) (L * p h) (mulr_ge0 hL (smooth_derivative_seminorm_nonnegative hp h)))=>j hj x hx.
have hj':(j<i.+1)%N by rewrite ltnS.
pose index:'I_i.+1:=Ordinal hj'.
apply:le_trans ((hl index).2 x hx h) _.
apply:ler_wpM2r;first exact:smooth_derivative_seminorm_nonnegative hp h.
rewrite /L (bigD1 index) //= lerDl.
apply:sumr_ge0=>k _;exact:(hl k).1.
Qed.
End SmoothPrecompositionSeminormBound.
