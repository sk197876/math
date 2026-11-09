(** Federer (1969), 3.4.6, p. 323: actual split
    coefficients have a common positive geometric bound on
    the closed transverse unit ball. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import Hom RealNormUP SymmetricForms SymmetricOperatorNorm
  AnalyticGermUP AnalyticGermCoefficientForms AnalyticGermGrowthUP AnalyticGermGrowthSealed
  AnalyticGermGrowthCover WeierstrassCoefficientUP WeierstrassCoefficientNorm WeierstrassFactorialMajorant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_split_coefficient_growth]: the
    original bound ||f_(i,j)||<=b*c^(i+j), 3.4.6,
    p. 323. Factorial growth of the original analytic
    germ supplies b,c. Enlarging c absorbs the original
    direction's norm without changing v or the transverse splitting. *)
Theorem weierstrass_split_coefficient_growth (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (alpha:analytic_germ_space hNX (0:X)) (v:X) (inclusion:Hom K X)
    (C:nat->nat->K->R):
  (forall i j,is_weierstrass_split_coefficient alpha v inclusion i j (C i j)) ->
  (forall z,NX (inclusion z)=NK z) ->
  exists b c:R,0<b /\0<c /\forall i j z,NK z<=1 ->`|C i j z|<=b*c^+(i+j).
Proof.
move=>hC hInclusion.
have [s [t [hs [ht hGrowth]]]]:=@analytic_germ_positive_growth_cover R X NX hNX 0 alpha.
have [F [hF [_ hNorm]]]:=@analytic_germ_coefficient_forms_exists R X NX hNX 0 alpha.
pose b:=(s%:R:R).
pose d:=1+NX v.
pose c:=(2:R)*t%:R*d.
have hV:0<=NX v:=real_seminorm_nonnegative hNX.1 v.
have hd:1<=d by rewrite /d lerDl.
have hD:0<d:=lt_le_trans ltr01 hd.
have hVD:NX v<=d by rewrite /d lerDr ler01.
have hB:0<b by rewrite /b ltr0n.
have hT:0<(t%:R:R) by rewrite ltr0n.
have hPositive:0<c by rewrite /c !mulr_gt0 // ltr0n.
exists b,c;split;first exact:hB.
split;first exact:hPositive.
move=>i j z hz.
pose L:=b*t%:R^+(i+j)*((i+j)`!)%:R.
have hDerivative:(symmetric_operator_norm hNX.1 (fun r:R^o=>(`|r|)%R)
    (F (i+j)%N)<=L%:E)%E.
  rewrite hNorm lee_fin.
  exact:((analytic_germ_growth_membership (@AnalyticGermGrowth.laws R X NX hNX 0 s t) alpha).1 hGrowth (i+j)%N).
have hMixed:=@weierstrass_split_coefficient_norm_bound R X K NX NK hNX alpha v inclusion
  i j (C i j) (F (i+j)%N) L (hC i j) (hF (i+j)%N) hInclusion hDerivative z.
apply:le_trans hMixed _.
exact:(@weierstrass_mixed_factorial_majorant R b t%:R d (NX v) (NK z) i j
  (ltW hB) (ltW hT) hd hV hVD (real_seminorm_nonnegative hNK.1 z) hz).
Qed.
