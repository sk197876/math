(** Federer (1969), 4.1.8, p. 361: the original
    coordinate-pullback covector bound has the displayed
    binomial constant. Reuse the original coordinate
    contraction laws and the earlier shuffle estimate. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanBlockLinearMaps
  AlternatingForms AlternatingDual AlternatingProduct ScalarCoefficients
  CurrentCoefficientNorms CoareaPerturbationBound CurrentFormNonexpansivePullback CurrentFormBinomialWedge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianCovectorBinomial.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation p := (hom_as_linear (@euclidean_first_block_map R m n)).
Local Notation q := (hom_as_linear (@euclidean_last_block_map R m n)).
Local Notation NA := (@current_form_comass R h2 m i).
Local Notation NB := (@current_form_comass R h2 n j).
Local Notation NC := (@current_form_comass R h2 (m+n) (i+j)).

(** Source for [current_cartesian_covector_binomial_bound]:
    the original pulled-back covector product is bounded by
    the binomial coefficient times the two comasses,
    supporting Federer 4.1.8, p. 361. *)
Theorem current_cartesian_covector_binomial_bound (a:A_m X R^o i) (b:A_m Y R^o j):
  NC (form_wedge h2 (scalar_bilinear R) (A_m_dual p a) (A_m_dual q b))<=
    'C(i+j,i)%:R*(NA a*NB b).
Proof.
apply:le_trans (@current_comass_binomial_wedge R h2 (m+n) i j _ _) _.
apply:ler_wpM2l;first exact:ler0n.
apply:ler_pM.
- exact:real_seminorm_nonnegative (@current_form_comass_real_norm R h2 (m+n) i).1 _.
- exact:real_seminorm_nonnegative (@current_form_comass_real_norm R h2 (m+n) j).1 _.
- exact:(@current_comass_nonexpansive_pullback R h2 (m+n) m p
    (fun z=>(@coarea_block_projection_norms R m n z).1) i a).
- exact:(@current_comass_nonexpansive_pullback R h2 (m+n) n q
    (fun z=>(@coarea_block_projection_norms R m n z).2) j b).
Qed.

(** Source for [current_cartesian_unit_covector_binomial]:
    the two original unit covectors give total comass at
    most the displayed binomial coefficient, Federer 4.1.8,
    p. 361, last covector estimate in the product argument. *)
Theorem current_cartesian_unit_covector_binomial (a:A_m X R^o i) (b:A_m Y R^o j):
  NA a<=1 ->NB b<=1 ->
  NC (form_wedge h2 (scalar_bilinear R) (A_m_dual p a) (A_m_dual q b))<='C(i+j,i)%:R.
Proof.
move=>hA hB;apply:le_trans (current_cartesian_covector_binomial_bound a b) _.
have hProduct:NA a*NB b<=1.
  apply:le_trans (ler_wpM2r (real_seminorm_nonnegative
    (@current_form_comass_real_norm R h2 n j).1 b) hA) _.
  by rewrite mul1r.
have h:=ler_wpM2l (ler0n R 'C(i+j,i)) hProduct;by rewrite mulr1 in h.
Qed.
End CurrentCartesianCovectorBinomial.
