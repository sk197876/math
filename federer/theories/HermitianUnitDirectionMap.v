(** Federer (1969), 3.4.12, p. 339: any two original
    Hermitian unit directions are related by a complex linear
    isometry. The construction is a local existence witness;
    all scalar and inner-product identities use Chapter 1. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom TensorUP Bilinear ScalarRestriction ComplexScalarSealed ComplexScalarLaws
  ComplexCoefficientAlgebra HermitianUP HermitianRealImaginary HermitianComplexLinearity
  InnerProductUP InnerProductLaws InnerNorm HermitianRankOneIsometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

(** Source for [hermitian_unit_direction_fixing_isometry_exists]: the
    original unitary sphere action is transitive, supporting
    3.4.12, p. 339. The supporting formulation supplies the
    actual complex map before placing it in the unitary group. *)
Theorem hermitian_unit_direction_fixing_isometry_exists (R:realType) (X:lmodType (ComplexScalars.C R)) H
    (hH:@is_hermitian_product R X H) (v w:X):
  inner_norm (hermitian_real_inner_product hH) v= 1 ->
  inner_norm (hermitian_real_inner_product hH) w= 1 ->
  exists L:Hom X X,L v=w /\(forall x y,H (L x) (L y)=H x y) /\
    forall x,H v x=0 ->H w x=0 ->L x=x.
Proof.
move=>hV hW.
case:(eqVneq v w)=>[hEqual|hDifferent].
- exists (hom_of_linear (linear_id X));split;first exact:hEqual.
  split;first by move=>x y.
  by move=>x _ _.
pose C:=ComplexScalars.C R.
have hOne:conjugate (1:C)= 1 by rewrite -(@rmorph1 R C (ComplexScalars.embed R)) conjugate_real rmorph1.
have hZero:conjugate (0:C)=0 by rewrite -(@rmorph0 R C (ComplexScalars.embed R)) conjugate_real rmorph0.
have hNeg x:conjugate (-x)= -conjugate x.
  change (complex_real_conjugate (-x)= -complex_real_conjugate x).
  by rewrite linearN.
have hSubtract x y:conjugate (x-y)=conjugate x-conjugate y by rewrite conjugate_add hNeg.
have hVV:H v v= 1.
  rewrite (hermitian_diagonal_real hH) -(inner_norm_sqr (hermitian_real_inner_product hH) v) hV expr1n rmorph1.
  reflexivity.
have hWW:H w w= 1.
  rewrite (hermitian_diagonal_real hH) -(inner_norm_sqr (hermitian_real_inner_product hH) w) hW expr1n rmorph1.
  reflexivity.
pose u:=v-w;pose d:= 1-H w v.
have hUU:H u u=d+conjugate d.
  rewrite /u /d (bilBl (hermitian_real_bilinear hH)) !(bilBr (hermitian_real_bilinear hH))
    hVV hWW hSubtract hOne -(hermitian_conjugate_symmetric hH w v).
  ring.
have hD:d!=0.
  apply/eqP=>hDZero.
  have hUZero:H u u=0 by rewrite hUU hDZero hZero addr0.
  have hRealZero:hermitian_real_part H u u=0 by rewrite /hermitian_real_part hUZero re_zero.
  have hVectorZero:u=0.
    apply/eqP;by rewrite -(inner_self_eq0 (hermitian_real_inner_product hH)) hRealZero eqxx.
  apply:(negP hDifferent).
  by rewrite -subr_eq0 -/u hVectorZero eqxx.
pose c:=d^-1.
have hCD:c*d= 1 by rewrite /c mulVf.
have hConjugate:conjugate c*conjugate d= 1 by rewrite -conjugate_mul hCD hOne.
have hTrace:c+conjugate c=conjugate c*c*H u u.
  rewrite hUU mulrDr.
  have hFirst:conjugate c*c*d=conjugate c by rewrite -mulrA hCD mulr1.
  have hSecond:conjugate c*c*conjugate d=c.
    rewrite [conjugate c*c]mulrC -mulrA hConjugate mulr1;reflexivity.
  by rewrite hFirst hSecond addrC.
have [L [hL hIsometry]]:=hermitian_rank_one_isometry_exists hH hTrace.
exists L;split.
- rewrite hL /u (bilBl (hermitian_real_bilinear hH)) hVV.
  change (v-(c*d)*:(v-w)=w).
  by rewrite hCD scale1r subKr.
- split;first exact:hIsometry.
  move=>x hvx hwx;by rewrite hL /u (bilBl (hermitian_real_bilinear hH)) hvx hwx
    subrr mulr0 scale0r subr0.
Qed.

(** Source for [hermitian_unit_direction_isometry_exists]: actual
    complex isometric alignment of any two original unit directions,
    supporting the U(n) Haar argument in 3.4.12, p. 339. *)
Theorem hermitian_unit_direction_isometry_exists (R:realType) (X:lmodType (ComplexScalars.C R)) H
    (hH:@is_hermitian_product R X H) (v w:X):
  inner_norm (hermitian_real_inner_product hH) v = 1 ->
  inner_norm (hermitian_real_inner_product hH) w = 1 ->
  exists L:Hom X X,L v=w /\forall x y,H (L x) (L y)=H x y.
Proof.
move=>hv hw;have [L [hL [hIsometry _]]]:=@hermitian_unit_direction_fixing_isometry_exists R X H hH v w hv hw.
exists L;by split.
Qed.
