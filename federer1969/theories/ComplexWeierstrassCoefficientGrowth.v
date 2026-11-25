(** Federer (1969), 3.4.12, p. 339: the actual complex
    mixed coefficients satisfy the original common geometric bound.
    Reuse the established numerical factorial majorant of 3.4.6,
    p. 323, and the exact real restriction of the germ forms. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm SymmetricForms SymmetricOperatorNorm
  ComplexSymmetricFormRestriction HolomorphicGermUP HolomorphicGermFormsUP HolomorphicGermFormsSealed
  HolomorphicGermJetGrowth HolomorphicGermRealFormNorm ComplexWeierstrassCoefficientUP
  ComplexWeierstrassCoefficientNorm WeierstrassFactorialMajorant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_split_coefficient_growth]: the
    original bound on all transverse unit-ball coefficients, with
    the norm of v absorbed into the positive constant, in the
    complex extension of 3.4.6, p. 323. *)
Theorem complex_weierstrass_split_coefficient_growth (R:realType)
    (X K:lmodType (ComplexScalars.C R)) (NX:X->R) (NK:K->R)
    (hNX:is_complex_norm NX) (hNK:is_complex_norm NK)
    (alpha:holomorphic_germ_space (complex_norm_real hNX) (0:X))
    (v:X) (inclusion:Hom K X) (Cij:nat->nat->K->ComplexScalars.C R):
  (forall i j,is_complex_weierstrass_split_coefficient hNX alpha v inclusion i j (Cij i j)) ->
  (forall z,NX (inclusion z)=NK z) ->
  exists b c:R,0<b /\0<c /\forall i j z,NK z<=1 ->complex_modulus (Cij i j z)<=b*c^+(i+j).
Proof.
move=>hC hInclusion.
have [b [t [hb [ht hGrowth]]]]:=@holomorphic_germ_positive_jet_growth R X NX hNX 0 alpha.
pose d:=1+NX v.
pose c:=(2:R)*t*d.
have hV:0<=NX v:=real_seminorm_nonnegative (complex_norm_real hNX).1 v.
have hd:1<=d by rewrite /d lerDl.
have hD:0<d:=lt_le_trans ltr01 hd.
have hVD:NX v<=d by rewrite /d lerDr ler01.
have hPositive:0<c by rewrite /c !mulr_gt0 // ltr0n.
exists b,c;split;first exact:hb.
split;first exact:hPositive.
move=>i j z hz.
pose F:=@HolomorphicGermForms.value R X NX hNX 0 (i+j)%N alpha.
have [G hG]:=@complex_symmetric_form_real_exists R X (ComplexScalars.C R)^o (i+j)%N F.
pose L:=b*t^+(i+j)*((i+j)`!)%:R.
have hDerivative:(@symmetric_operator_norm R
    (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
    NX (complex_norm_real hNX).1 (@complex_modulus R) (i+j)%N G<=L%:E)%E.
  rewrite (@holomorphic_germ_real_form_norm R X NX hNX 0 (i+j)%N alpha G hG) lee_fin.
  exact:hGrowth (i+j)%N.
have hMixed:=@complex_weierstrass_split_coefficient_norm_bound R X K NX NK hNX
  alpha v inclusion i j (Cij i j) F G L (hC i j) (fun t=>erefl _) hG hInclusion hDerivative z.
apply:le_trans hMixed _.
exact:(@weierstrass_mixed_factorial_majorant R b t d (NX v) (NK z) i j
  (ltW hb) (ltW ht) hd hV hVD (real_seminorm_nonnegative (complex_norm_real hNK).1 z) hz).
Qed.
