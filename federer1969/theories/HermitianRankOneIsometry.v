(** Federer (1969), 3.4.12, p. 339: supporting actual
    unitary sphere transport. A rank-one complex linear map
    is an isometry when its scalar coefficient satisfies
    the stated Hermitian trace identity. This supplies a
    missing connection to the existing homogeneous Haar theory. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom TensorUP Bilinear ScalarRestriction ComplexScalarSealed ComplexScalarLaws
  ComplexCoefficientAlgebra HermitianUP HermitianComplexLinearity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ComplexScalarTheory.
Local Open Scope ring_scope.

(** Source for [hermitian_rank_one_isometry_exists]: the actual
    complex isometry used to align two unit directions in
    U(n), supporting 3.4.12, p. 339. No sphere transitivity
    or isometry conclusion is supplied as a premise. *)
Theorem hermitian_rank_one_isometry_exists (R:realType) (X:lmodType (ComplexScalars.C R)) H
    (hH:@is_hermitian_product R X H) (u:X) (c:ComplexScalars.C R):
  c+conjugate c=conjugate c*c*H u u ->
  exists L:Hom X X,(forall x,L x=x-(c*H u x)*:u) /\
    forall x y,H (L x) (L y)=H x y.
Proof.
move=>hTrace.
pose A:=fun x:X=>(c*H u x)*:u.
have hA:linear A.
  move=>a x y;rewrite /A (bilDr (hermitian_real_bilinear hH)) (hermitian_scale_right hH)
    mulrDr [c*(a*_)]mulrCA scalerDl !scalerA.
  reflexivity.
pose T:=fun x:X=>x-A x.
have hT:linear T.
  move=>a x y;rewrite /T hA scalerBr opprD addrACA.
  reflexivity.
exists (@HomMap (ComplexScalars.C R) X X T (introT (asboolP _) hT));split;first by move=>x.
move=>x y;change (H (x-A x) (y-A y)=H x y).
rewrite (bilBl (hermitian_real_bilinear hH)) !(bilBr (hermitian_real_bilinear hH)) /A
  !(hermitian_scale_left hH) !(hermitian_scale_right hH) !conjugate_mul
  -(hermitian_conjugate_symmetric hH u x).
have hExpression:
    (H x y-c*H u y*H x u)-(conjugate c*H x u*H u y-conjugate c*H x u*(c*H u y*H u u))=
    H x y+(conjugate c*c*H u u-(c+conjugate c))*(H x u*H u y) by ring.
rewrite hExpression -hTrace subrr mul0r addr0.
reflexivity.
Qed.
