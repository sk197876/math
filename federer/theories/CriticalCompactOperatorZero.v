(** Federer (1969), 3.4.2(7), p. 313: continuity controls a
    derivative uniformly near a compact set where its tests vanish. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormClassOneUP
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearOne
  CompactNearbyUniformContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_compact_operator_zero_control]: the
    uniform derivative estimate in the class-one case of 3.4.2(7),
    p. 313, also used in (9). A continuous field of operators that
    vanishes on Z over compact C has uniformly small values on
    unit vectors of Z near C. Use the public one-linear norm and
    compact-base continuity; no finite target basis is needed. *)
Theorem critical_compact_operator_zero_control (R:realType)
    (X Y W:lmodType R) (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX)
    (hNY:is_real_norm NY) (ev:{ffun 'I_1->X}->Hom W Y) (WN:W->R)
    (hW:is_continuous_multilinear_space NX NY ev WN)
    (Z U C:set X) (G:X->W):
  @compact (real_norm_metric_space hNX) C ->C `<=` U ->
  norm_class_zero NX WN U G ->
  (forall c z,C c ->Z z ->continuous_multilinear_one_operator hW (G c) z=0) ->
  forall epsilon:R,0<epsilon ->exists d,0<d /\forall x c,C c ->U x ->
    NX (x-c)<d ->forall z,Z z ->NX z<=1 ->
    NY (continuous_multilinear_one_operator hW (G x) z)<epsilon.
Proof.
move=>hC hCU hG hZero epsilon hEpsilon.
pose hWN:=continuous_multilinear_norm_is_norm hNY hW.
have [d [hd hNear]]:=@norm_class_zero_compact_uniform_nearby R X W NX WN hNX
  hWN U C G hC hCU hG epsilon hEpsilon.
exists d;split;first exact:hd.
move=>x c hc hx hSmall z hz hUnit.
have hDifference:=hNear c x hc hx hSmall.
have hBound:=multilinear_operator_bound
  (continuous_multilinear_norm_laws hW (G x-G c)) [ffun i:'I_1=>z].
rewrite big_ord1 ffunE in hBound.
change (is_true (NY (ev [ffun i:'I_1=>z] (G x-G c))<=WN (G x-G c)*NX z)) in hBound.
rewrite (Bilinear.linB (hom_linear (ev [ffun i:'I_1=>z]))) in hBound.
have hAtZero:ev [ffun i:'I_1=>z] (G c)=0:=hZero c z hc hz.
rewrite hAtZero subr0 in hBound.
have hNonnegative:0<=WN (G x-G c):=
  multilinear_operator_nonnegative (continuous_multilinear_norm_laws hW (G x-G c)).
have hProduct:=ler_wpM2l hNonnegative hUnit.
rewrite mulr1 in hProduct.
exact:(le_lt_trans (le_trans hBound hProduct) hDifference).
Qed.
