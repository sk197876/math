(** Federer (1969), 3.1.24, p. 238: the
    Taylor integral gives a geometric remainder from diagonal bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP NormHigherDifferentialUP NormClassOneUP
  NormTaylorIntegral NormTaylorRemainderBound NormedStieltjesBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_taylor_diagonal_remainder_bound]: the
    Taylor step in Federer 3.1.24, p. 238,
    implication (2) to (3). A uniform bound M for
    the normalized top diagonal coefficient on the segment gives
    remainder at most 2M after retaining that degree. This
    oscillation estimate suffices for uniform convergence; the printed
    next-degree estimate has a sharper constant. *)
Theorem norm_taylor_diagonal_remainder_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y) (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A:X->Prop) (f:X->Y) (D:forall i,X->Z i) a v k M :
  (forall i,(i<=k.+1)%N -> forall x,A x ->
    has_norm_higher_differential NX ev ZN A f i x (D i x)) ->
  norm_class_zero NX (@ZN k.+1) A (D k.+1) ->
  (forall t:R,0<=t<=1 -> A (a+t*:v)) ->
  (forall t:R,0<=t<=1 ->
    NY (((k.+1)`!)%:R^-1 *: @ev k.+1 [ffun j=>v] (D k.+1 (a+t*:v)))<=M) ->
  NY (f (a+v)-norm_taylor_value ev D a v k.+1)<=2*M.
Proof.
move=>hD hc hseg hb.
have hi:=norm_taylor_integral_fields hNX hNY hZ hD hc hseg.
have h0:0<=(0:R)<=1 by rewrite lexx ler01.
have ha:=hb 0 h0; rewrite scale0r addr0 in ha.
have hbound t (ht:0<=t<=1):
    NY (((k.+1)`!)%:R^-1 *:
      (@ev k.+1 [ffun j=>v] (D k.+1 a)-@ev k.+1 [ffun j=>v] (D k.+1 (a+t*:v))))<=2*M.
  rewrite scalerBr; apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
  rewrite (real_seminorm_negate hNY.1).
  have heq0:M+M= 2*M by rewrite mulr_natl mulr2n.
  rewrite -heq0; exact (lerD ha (hb t ht)).
have hh:=normed_stieltjes_integral_decreasing_bound hNY hi hbound
  (@unit_complement_power_decreasing R k.+1).
rewrite subr0 expr1n subrr expr0n subr0 mulr1 in hh.
exact hh.
Qed.
