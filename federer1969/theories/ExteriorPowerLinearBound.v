(** Federer (1969), 1.7.6, pp. 33–34: the
    exterior operator norm is bounded by the corresponding
    power of a linear norm bound. Supporting the arbitrary
    source comparison in 3.2.47(3), p. 283; the
    bound need not be the exact first operator norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm LinearBasis OperatorNormUP OperatorNorm
  OperatorNormLaws ExteriorMaps ExteriorOperatorNorm InnerExteriorPositivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_power_linear_bound]: the upper
    estimate of 1.7.6, pp. 33–34, used on
    every actual group tangent in 3.2.47, p. 283.
    Dimension zero and zero bounds are retained. *)
Theorem exterior_power_linear_bound (R:realType) (h2:(1+1:R)!=0)
    (V W:lmodType R) BV BW (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW)
    n (b:'I_n->V) (hb:is_basis b) (F:{linear V->W}) c q:
  0<=c ->(forall x,inner_norm hW (F x)<=c*inner_norm hV x) ->
  exterior_operator_norm h2 hV hW hb F q<=c^+q.
Proof.
move=>hc hBound.
pose l:=linear_operator_norm hV hW hb F.
have hL:is_operator_norm hV hW F l:=linear_operator_normP hV hW hb F.
have hL0:0<=l:=operator_norm_nonnegative hL.
have hLC:l<=c.
  have [x [hx hValue]]:=operator_norm_attained hL.
  rewrite -hValue; apply:le_trans (hBound x) _.
  have h:=ler_wpM2l hc hx; by rewrite mulr1 in h.
have hPow:l^+q<=c^+q.
  elim:q=>[|q ih]; first by rewrite !expr0.
  rewrite !exprS.
  exact (le_trans (ler_wpM2l hL0 ih) (ler_wpM2r (exprn_ge0 q hc) hLC)).
exact (le_trans (exterior_operator_norm_bound h2 hV hW hb F q) hPow).
Qed.

(** Source for [exterior_norm_linear_bound]: the same
    bound for any value satisfying the independent exterior
    norm laws, 1.7.6, pp. 33–34, supporting
    actual approximate Jacobians in 3.2.47, p. 283. *)
Corollary exterior_norm_linear_bound (R:realType) (h2:(1+1:R)!=0)
    (V W:lmodType R) BV BW (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW)
    n (b:'I_n->V) (hb:is_basis b) (F:{linear V->W}) c q j:
  0<=c ->(forall x,inner_norm hW (F x)<=c*inner_norm hV x) ->
  is_operator_norm (exterior_inner_productP h2 hV q) (exterior_inner_productP h2 hW q)
    (exterior_power_map F q) j ->j<=c^+q.
Proof.
move=>hc hBound hJ.
have hValue:j=exterior_operator_norm h2 hV hW hb F q.
  exact (operator_norm_unique hJ (exterior_operator_normP h2 hV hW hb F q)).
rewrite hValue; exact (@exterior_power_linear_bound R h2 V W BV BW hV hW n b hb F c q hc hBound).
Qed.
