(** Federer (1969), 3.4.6, pp. 322–323: the
    original mixed coefficients regroup exactly into every
    actual homogeneous Taylor polynomial. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  SymmetricForms HomogeneousPolynomialFunctions PolynomialDiagonalNorm AnalyticGermUP AnalyticGermJetsSealed
  AnalyticGermCoefficientForms WeierstrassCoefficientUP WeierstrassGroupedUP
  WeierstrassTransverseUP WeierstrassSplitFormExpansion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_original_coefficient_grouping]:
    the finite total-degree grouping in the displayed
    expansion of 3.4.6, pp. 322–323, is the
    original actual homogeneous Taylor coefficient. The
    exact transverse decomposition and finite binomial
    theorem prove the identity without an interchange
    of infinite sums. *)
Theorem weierstrass_original_coefficient_grouping (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (v:X)
    (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    (alpha:analytic_germ_space hNX (0:X)) (q:nat->nat->K->R):
  is_weierstrass_transverse_space NX NK v xi inclusion projection ->
  (forall i j,is_weierstrass_split_coefficient alpha v inclusion i j (q i j)) ->
  is_weierstrass_grouped_germ xi projection q alpha.
Proof.
move=>hSplit hQ m x.
have [F [hF _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX 0 alpha.
have hDecompose:x=(xi x)*:v+inclusion (projection x).
  by rewrite (weierstrass_transverse_projection_equation hSplit) addrC subrK.
have hPolynomial:(\sum_(i<m.+1) (xi x)^+i*q i (m-i)%N (projection x))=
    sform_polynomial_value (F m) x.
  have hExpansion:=@weierstrass_split_form_line_expansion R X m (F m) v (inclusion (projection x)) (xi x).
  rewrite -hDecompose in hExpansion.
  rewrite hExpansion.
  apply:eq_bigr=>i _.
  have hi:(i<=m)%N by have:=ltn_ord i;rewrite ltnS.
  have hActual:=hQ i (m-i)%N.
  rewrite /is_weierstrass_split_coefficient (subnKC hi) in hActual.
  by rewrite (hActual (F m) (hF m) (projection x)).
rewrite hPolynomial sform_polynomial_diagonal_value hF.
congr (_*_).
have hTuple:[ffun i:'I_m=>tnth [tuple x | _<m] i]=[ffun _:'I_m=>x].
  by apply/ffunP=>i;rewrite !ffunE tnth_mktuple.
by rewrite hTuple.
Qed.
