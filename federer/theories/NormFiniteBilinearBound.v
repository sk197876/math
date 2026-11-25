(** Federer (1969), 4.1.7, p. 356: boundedness
    of the original finite-dimensional coefficient
    operations used in the current product rules.
    Apply the prior finite linear bound to the
    original basis coordinates and fixed coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring lra.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP LinearBasis
  FiniteDualDimension Annihilator NormFiniteLinearBound NormBoundedBilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_finite_bilinear_bounded]: actual
    finite coefficient products are bounded, supporting
    Federer 4.1.7, p. 356, by the finite basis
    expansion and norm comparison of 2.7.16,
    pp. 133–134. No bound is assumed. *)
Theorem norm_finite_bilinear_bounded (R:realType) (Y1 Y2 Y3:lmodType R)
    (N1:Y1->R) (N2:Y2->R) (N3:Y3->R)
    (hN1:is_real_norm N1) (hN2:is_real_norm N2) (hN3:is_real_norm N3)
    n1 n2 (b1:'I_n1->Y1) (b2:'I_n2->Y2) (hb1:is_basis b1) (hb2:is_basis b2)
    (B:Y1->Y2->Y3) (hB:bilinear B):norm_bounded_bilinear N1 N2 N3 B.
Proof.
split; first exact:hB.
have hC i:exists c:R,0<=c /\forall x,`|dual_basis hb1 i x|<=c*N1 x.
  exact:(@norm_finite_linear_bounded R Y1 R^o N1 (fun t:R^o=>`|t|) hN1
    (@scalar_absolute_value_norm R) n1 b1 hb1 (dual_basis hb1 i)).
have [c hc]:=choice hC.
pose L (i:'I_n1):Hom Y2 Y3:=@HomMap R Y2 Y3 (fun y=>B (b1 i) y)
  (introT (asboolP _) (hB.2 (b1 i))).
have hD i:exists d:R,0<=d /\forall y,N3 (L i y)<=d*N2 y.
  exact:(@norm_finite_linear_bounded R Y2 Y3 N2 N3 hN2 hN3 n2 b2 hb2 (L i)).
have [d hd]:=choice hD.
exists (\sum_i c i*d i); split.
- apply:sumr_ge0=>i _; exact:mulr_ge0 (hc i).1 (hd i).1.
- move=>x y.
  have hExpand:B x y=\sum_i dual_basis hb1 i x *: B (b1 i) y.
    pose M:Hom Y1 Y3:=@HomMap R Y1 Y3 (fun z=>B z y) (introT (asboolP _) (hB.1 y)).
    change (M x=\sum_i dual_basis hb1 i x *: M (b1 i)).
    rewrite {1}(@basis_vector_expansion R Y1 n1 b1 hb1 x) linear_sum.
    apply:eq_bigr=>i _; exact:linearZ.
  rewrite hExpand.
  apply:le_trans (real_seminorm_sum hN3.1 _) _.
  rewrite mulr_suml.
  apply:ler_sum=>i _.
  rewrite (real_seminorm_scale hN3.1).
  have ha:0<=`|dual_basis hb1 i x| :=normr_ge0 _.
  have hb:0<=N3 (B (b1 i) y):=real_seminorm_nonnegative hN3.1 _.
  have hMul:=ler_pM ha hb ((hc i).2 x) ((hd i).2 y).
  have hEq:(c i*N1 x)*(d i*N2 y)=(c i*d i)*(N1 x*N2 y) by ring.
  by rewrite hEq in hMul.
Qed.
