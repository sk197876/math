(** Federer (1969), 3.3.4, pp. 290–292: the
    actual map T after unit normalization, its ball
    inequalities and its two-point direction fibres. Use
    the sealed symmetric Hilbert power and the already
    proved exact metric and fibre laws of 3.2.28(4). *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals ring lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm
  InnerUnitNormalization SymmetricGrading InnerSymmetric InnerSymmetricPositivity
  SymmetricSquareGeometry Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Directions.
Variable R:realType.
Variable V:lmodType R.
Variable B:V->V->R.
Hypothesis hB:is_inner_product B.
Local Notation N:=(inner_norm hB).
Local Notation T:=(@inner_projective_square R V).
Local Notation S:=(@symmetric_inner_productP R V B hB 2).
Local Notation NS:=(inner_norm S).

(** Source for [structure_projective_direction_distance]:
    the first two equivalent inequalities near the end
    of Federer 3.3.4, p. 291. Clearing the actual
    positive norm in the exact projective-square distance
    gives the original unnormalized inner-product expression. *)
Lemma structure_projective_direction_distance x v:
  0<N x ->N v= 1 ->
  NS (T (inner_unit_normalization hB x)-T v)^+2*(N x)^+2=
    (N x)^+2-(B x v)^+2.
Proof.
move=>hx hv.
have hUnit:=inner_unit_normalization_norm hx.
rewrite (inner_projective_square_unit_distance hUnit hv)
  /inner_unit_normalization (bilZl (inner_bilinear hB)) exprMn.
have hInv:(N x)^-1*(N x)= 1 by rewrite mulVf ?gt_eqF.
have hSq:((N x)^-1)^+2*(N x)^+2= 1 by rewrite -exprMn hInv expr1n.
by rewrite mulrBl mul1r mulrAC hSq mul1r.
Qed.

(** Source for [structure_projective_direction_ball]: the
    actual inverse-image ball equivalence in Federer
    3.3.4, p. 291. The nonzero projected vector
    is normalized by its actual norm, and every
    positive target radius is retained. *)
Theorem structure_projective_direction_ball x v (t:R):
  0<N x ->N v= 1 ->0<t ->
  (NS (T (inner_unit_normalization hB x)-T v)<t <->
    (N x)^+2-(B x v)^+2<t^+2*(N x)^+2).
Proof.
move=>hx hv ht.
have hN:0<=NS (T (inner_unit_normalization hB x)-T v):=inner_norm_nonnegative _ _.
have hSq:0<(N x)^+2 by rewrite exprn_gt0.
have hDist:=structure_projective_direction_distance hx hv.
rewrite -(ltr_sqr hN (ltW ht)).
rewrite -(ltr_pM2r hSq) hDist; reflexivity.
Qed.

(** Source for [structure_projective_direction_fibre]: the
    inverse image of F(k) has the two actual unit
    directions plus or minus k(g_j), Federer 3.3.4,
    p. 292. No selected representative of a line
    or of a square is introduced. *)
Theorem structure_projective_direction_fibre x v:
  0<N x ->N v= 1 ->
  (T (inner_unit_normalization hB x)=T v <->
    inner_unit_normalization hB x=v \/ inner_unit_normalization hB x= -v).
Proof.
move=>hx hv.
exact:(inner_projective_square_unit_fibre (inner_unit_normalization_norm hx) hv).
Qed.
End Directions.
