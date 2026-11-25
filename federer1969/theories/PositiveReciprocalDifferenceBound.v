(** Federer (1969), 3.2.35, p. 271:
    supporting scalar reciprocal estimate for the
    corrected radial map x -> g(x)^(-1)x. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_reciprocal_upper_from_lower]:
    supporting reciprocal control for the boundary
    parametrization in Federer 3.2.35, p. 271,
    with erratum p. 5, book p. 271 line 24.
    A positive lower bound 1/M<=u gives
    0<u and u^(-1)<=M, using actual
    positive scalar division without a zero default. *)
Lemma positive_reciprocal_upper_from_lower (R:realType) (u M:R):
  0<M ->1/M<=u ->0<u /\u^-1<=M.
Proof.
move=>hM hLower.
have hInverse:0<M^-1 by rewrite invr_gt0.
have hPositive:0<u.
  apply:(lt_le_trans hInverse _); by rewrite mul1r in hLower.
split; first exact hPositive.
rewrite -(mul1r (u^-1)) ler_pdivrMr //.
by move:hLower; rewrite ler_pdivrMr // mulrC.
Qed.

(** Source for [positive_reciprocal_difference_bound]:
    supporting Lipschitz control of reciprocal g
    in the radial boundary argument of Federer
    3.2.35, p. 271. Positive u,v and
    upper bounds M on their actual inverses give
    |u^(-1)-v^(-1)|<=M^2 |u-v|.
    The estimate is proved from the exact inverse
    difference identity, not assumed as regularity. *)
Lemma positive_reciprocal_difference_bound (R:realType) (u v M:R):
  0<u ->0<v ->u^-1<=M ->v^-1<=M ->
  `|u^-1-v^-1|<=M^+2*`|u-v|.
Proof.
move=>hu hv hU hV.
have hu0:u!=0 by rewrite gt_eqF.
have hv0:v!=0 by rewrite gt_eqF.
have hUI:0<u^-1 by rewrite invr_gt0.
have hVI:0<v^-1 by rewrite invr_gt0.
have hM:0<=M:=ltW (lt_le_trans hUI hU).
have hLeft:(u^-1*v^-1)*v=u^-1 by rewrite -mulrA (mulVf hv0) mulr1.
have hRight:(u^-1*v^-1)*u=v^-1 by rewrite mulrAC (mulVf hu0) mul1r.
have hDifference:u^-1-v^-1=(u^-1*v^-1)*(v-u).
  by rewrite mulrBr hLeft hRight.
rewrite hDifference normrM (ger0_norm (mulr_ge0 (ltW hUI) (ltW hVI))) distrC.
have hProduct:u^-1*v^-1<=M^+2.
  rewrite expr2.
  apply:(le_trans (ler_wpM2r (ltW hVI) hU) _).
  exact:(ler_wpM2l hM hV).
exact:(ler_wpM2r (normr_ge0 (u-v)) hProduct).
Qed.
