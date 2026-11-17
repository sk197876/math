(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: the power determinant is an
    actual polynomial in the original real
    coefficients. Apply the existing linear-map,
    scalar-restriction, polynomial product and sum laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals fingroup perm.
From Federer Require Import TensorUP Bilinear Hom GrassmannAbbreviations LinearBasis FiniteDualDimension
  RingScalarRestriction ScalarRestriction InversionCount PolynomialFunctions
  PolynomialComposition PolynomialLinearComposition HomMonomorphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section PolynomialDeterminant.
Variable R:realType.
Variables K L:fieldType.
Variable eta:{rmorphism R->K}.
Variable phi:{rmorphism K->L}.
Local Notation V:=[the lmodType K of ring_restricted_space phi L^o].
Local Notation VR:=[the lmodType R of restricted_space eta V].
Local Notation KR:=[the lmodType R of restricted_space eta K^o].
Variables d n:nat.
Variable basis:'I_d->V.
Hypothesis hBasis:is_basis basis.
Variable x:'I_n->L.
Local Notation z:=(fun v:R_n R n=>\sum_i phi (eta (v i))*x i).

(** Source for [power_family_determinant_polynomial]: the
    determinant of the first d powers is
    polynomial in the original real direction,
    supporting the almost-everywhere simplicity assertion
    in 3.4.8(8), p. 330. Its coefficients
    may lie in the original larger field;
    no finite real dimension of that field
    or target norm is assumed. *)
Theorem power_family_determinant_polynomial:
  exists P:PolynomialFunction (R_n R n) KR,forall v:R_n R n,
    P v = \sum_(sigma:'S_d) FedererPermutation.index K sigma *
      \prod_(i<d) dual_basis hBasis (sigma i) ((z v)^+(i:nat)).
Proof.
have hDotLinear:linear (z:R_n R n->VR).
  move=>a u v.
  change ((\sum_i phi (eta ((a*:u+v) i))*x i) =
    phi (eta a)*(\sum_i phi (eta (u i))*x i)+(\sum_i phi (eta (v i))*x i)).
  rewrite mulr_sumr -big_split;apply:eq_bigr=>i _.
  rewrite !ffunE !rmorphD !rmorphM;by rewrite mulrDl mulrA.
pose dot:Hom (R_n R n) VR:=@HomMap R (R_n R n) VR z (introT (asboolP _) hDotLinear).
have hDot:@is_polynomial_function R (R_n R n) VR z.
  exact:(@polynomial_linear R (R_n R n) VR (hom_as_linear dot)).
have hMulL:@bilinear R VR VR VR (fun a b:L=>a*b).
  split.
  - move=>b a u v;change ((phi (eta a)*u+v)*b = phi (eta a)*(u*b)+v*b).
    by rewrite mulrDl mulrA.
  - move=>u a b c;change (u*(phi (eta a)*b+c) = phi (eta a)*(u*b)+u*c).
    by rewrite mulrDr mulrCA.
have hPower k:@is_polynomial_function R (R_n R n) VR (fun v=>(z v)^+k).
  elim:k=>[|k ih].
  - exact:(@composition_polynomial_constant R (R_n R n) VR 1).
  - have hProduct:=@composition_polynomial_product R (@pchar_num R) (R_n R n) VR
      (fun a b:L=>a*b) hMulL (fun v=>(z v)^+k) z ih hDot.
    have hSame:(fun v:R_n R n=>(z v)^+k.+1) = (fun v:R_n R n=>(z v)^+k*z v).
      by apply:funext=>v;rewrite exprS mulrC.
    by rewrite hSame.
have hEntry (i j:'I_d):@is_polynomial_function R (R_n R n) KR
    (fun v=>dual_basis hBasis j ((z v)^+(i:nat))).
  exact:(@polynomial_linear_postcompose R (R_n R n) VR KR
    (@restrict_linear R K eta V K^o (hom_as_linear (dual_basis hBasis j)))
    (fun v=>(z v)^+(i:nat)) (hPower (i:nat))).
have hMulK:@bilinear R KR KR KR (fun a b:K=>a*b).
  split.
  - move=>b a u v;change ((eta a*u+v)*b = eta a*(u*b)+v*b);by rewrite mulrDl mulrA.
  - move=>u a b c;change (u*(eta a*b+c) = eta a*(u*b)+u*c);by rewrite mulrDr mulrCA.
have hFiniteProduct (sigma:'S_d):forall s:seq 'I_d,
    @is_polynomial_function R (R_n R n) KR
      (fun v=>\prod_(i<-s) dual_basis hBasis (sigma i) ((z v)^+(i:nat))).
  elim=>[|i s ih].
  - have hEmpty:(fun v:R_n R n=>\prod_(i<-[::]) dual_basis hBasis (sigma i) ((z v)^+(i:nat))) =
        (fun _:R_n R n=>(1:K)) by apply:funext=>v;rewrite big_nil.
    rewrite hEmpty;exact:(@composition_polynomial_constant R (R_n R n) KR 1).
  - have hProduct:=@composition_polynomial_product R (@pchar_num R) (R_n R n) KR
      (fun a b:K=>a*b) hMulK (fun v=>dual_basis hBasis (sigma i) ((z v)^+(i:nat)))
      (fun v=>\prod_(j<-s) dual_basis hBasis (sigma j) ((z v)^+(j:nat))) (hEntry i (sigma i)) ih.
    have hSame:(fun v:R_n R n=>\prod_(j<-i::s) dual_basis hBasis (sigma j) ((z v)^+(j:nat))) =
        (fun v:R_n R n=>dual_basis hBasis (sigma i) ((z v)^+(i:nat))*
          \prod_(j<-s) dual_basis hBasis (sigma j) ((z v)^+(j:nat))).
      by apply:funext=>v;rewrite big_cons.
    by rewrite hSame.
have hProduct (sigma:'S_d):@is_polynomial_function R (R_n R n) KR
    (fun v=>\prod_(i<d) dual_basis hBasis (sigma i) ((z v)^+(i:nat))).
  have hEnum:(fun v:R_n R n=>\prod_(i<d) dual_basis hBasis (sigma i) ((z v)^+(i:nat))) =
      (fun v:R_n R n=>\prod_(i<-enum 'I_d) dual_basis hBasis (sigma i) ((z v)^+(i:nat))).
    by apply:funext=>v;rewrite -big_enum.
  rewrite hEnum;exact:(hFiniteProduct sigma (enum 'I_d)).
have hTerm (sigma:'S_d):@is_polynomial_function R (R_n R n) KR
    (fun v=>FedererPermutation.index K sigma *
      \prod_(i<d) dual_basis hBasis (sigma i) ((z v)^+(i:nat))).
  exact:(@composition_polynomial_product R (@pchar_num R) (R_n R n) KR
    (fun a b:K=>a*b) hMulK (fun _=>FedererPermutation.index K sigma)
    (fun v=>\prod_(i<d) dual_basis hBasis (sigma i) ((z v)^+(i:nat)))
    (@composition_polynomial_constant R (R_n R n) KR (FedererPermutation.index K sigma)) (hProduct sigma)).
have hSum:=@composition_polynomial_sum R (R_n R n) KR [the finType of 'S_d]
  (fun sigma v=>FedererPermutation.index K sigma *
    \prod_(i<d) dual_basis hBasis (sigma i) ((z v)^+(i:nat))) hTerm.
exists (@PolynomialMap R (R_n R n) KR _ (introT (asboolP _) hSum));by [].
Qed.
End PolynomialDeterminant.
