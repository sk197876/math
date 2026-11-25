(** Federer (1969), 4.1.12, p. 369:
    every original weighted separated summand
    has comass at most one and
    derivative comass at most two.
    Apply the exact product and Leibniz
    estimates already proved for actual tests. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals lra.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockLinearMaps EuclideanCartesianMap CurrentCartesianDomain
  CurrentSpaces CurrentCoefficientNorms CurrentTestValueLaws CurrentTestExteriorDerivative
  CurrentCartesianTestProductSealed CurrentCartesianTestComass ReciprocalPowerSeriesBounds ReciprocalPowerSeriesWeights
  WeightedIntervalCutoffSealed WeightedIntervalCutoffNorms WeightedIntervalProductTests.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section WeightedIntervalProductTestTermBounds.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation AB := (@euclidean_cartesian_set R 1%N 1%N Full Full).
Local Notation hAB := (@current_cartesian_domain_open R 1%N 1%N Full Full hFull hFull).
Local Notation phi := (@WeightedIntervalCutoff.value R h2).
Local Notation va d := (@current_test_value R h2 1%N Full hFull d).
Local Notation vc d := (@current_test_value R h2 (1+1)%N AB hAB d).
Local Notation NA d := (@current_form_comass R h2 1%N d).
Local Notation NC d := (@current_form_comass R h2 (1+1)%N d).
Local Notation da := (@current_test_exterior_derivative R h2 1%N 0%N Full hFull).
Local Notation dc := (@current_test_exterior_derivative R h2 (1+1)%N 0%N AB hAB).
Local Notation Pure := (@CartesianTestProduct.value R h2 1%N 1%N Full Full hFull hFull 0%N 0%N).
Local Notation p := (@euclidean_first_block_map R 1%N 1%N).
Local Notation q := (@euclidean_last_block_map R 1%N 1%N).
Local Notation term := (@weighted_interval_product_test_term R h2).

(** Source for [weighted_interval_product_test_term_comass]:
    each original weighted product term
    has pointwise comass at most one,
    supporting M(psi_M)<=1 in Federer
    4.1.12, p. 369. *)
Theorem weighted_interval_product_test_term_comass n z:
  AB z->NC 0%N (vc 0%N (term n) z)<=1.
Proof.
move=>hz.
have hPhiP:=@weighted_interval_cutoff_point_comass R h2 n (p z).
have hPhiQ:=@weighted_interval_cutoff_point_comass R h2 n (q z).
have hNP:=real_seminorm_nonnegative (@current_form_comass_real_norm R h2 1%N 0%N).1
  (va 0%N (phi n) (p z)).
have hNQ:=real_seminorm_nonnegative (@current_form_comass_real_norm R h2 1%N 0%N).1
  (va 0%N (phi n) (q z)).
have hPure:=@current_cartesian_test_comass_bound R h2 1%N 1%N Full Full hFull hFull
  0%N 0%N (phi n) (phi n) z hz.
rewrite /= mul1r in hPure.
have hPureBound:NC 0%N (vc 0%N (Pure (phi n) (phi n)) z)<=1.
  exact:le_trans hPure (mulr_ile1 hNP hNQ hPhiP hPhiQ).
have hw:0<=reciprocal_power_series_weight R 3%N n:=
  ltW (reciprocal_power_series_weight_positive R 3%N n).
rewrite /weighted_interval_product_test_term current_test_scale_value
  (real_seminorm_scale (@current_form_comass_real_norm R h2 (1+1)%N 0%N).1)
  (ger0_norm hw).
have hBound:=ler_wpM2l hw hPureBound.
rewrite mulr1 in hBound.
exact:le_trans hBound (reciprocal_power_series_weight_le_one R 3%N n).
Qed.

(** Source for [weighted_interval_product_test_term_derivative_comass]:
    each original weighted term has
    derivative comass at most two;
    k^(-3) cancels the exact k^3
    derivative bound, supporting Federer
    4.1.12, p. 369. *)
Theorem weighted_interval_product_test_term_derivative_comass n z:
  AB z->NC 1%N (vc 1%N (dc (term n)) z)<=2.
Proof.
move=>hz.
pose k:R:=((n.+1)%:R)^+3.
have hk:0<=k by rewrite /k exprn_ge0 // ler0n.
have hPhiP:=@weighted_interval_cutoff_point_comass R h2 n (p z).
have hPhiQ:=@weighted_interval_cutoff_point_comass R h2 n (q z).
have hDP:=(@WeightedIntervalCutoff.laws R h2 n).2.2.2 (p z).
have hDQ:=(@WeightedIntervalCutoff.laws R h2 n).2.2.2 (q z).
have hNDP:=real_seminorm_nonnegative (@current_form_comass_real_norm R h2 1%N 1%N).1
  (va 1%N (da (phi n)) (p z)).
have hNDQ:=real_seminorm_nonnegative (@current_form_comass_real_norm R h2 1%N 1%N).1
  (va 1%N (da (phi n)) (q z)).
have hNP:=real_seminorm_nonnegative (@current_form_comass_real_norm R h2 1%N 0%N).1
  (va 0%N (phi n) (p z)).
have hNQ:=real_seminorm_nonnegative (@current_form_comass_real_norm R h2 1%N 0%N).1
  (va 0%N (phi n) (q z)).
have hPure:=@current_cartesian_test_derivative_comass_bound R h2 1%N 1%N Full Full hFull hFull
  0%N 0%N (phi n) (phi n) z hz.
rewrite /= !mul1r in hPure.
have hFirst:NA 1%N (va 1%N (da (phi n)) (p z))*NA 0%N (va 0%N (phi n) (q z))<=k.
  have h:=ler_pM hNDP hNQ hDP hPhiQ;by rewrite mulr1 in h.
have hSecond:NA 0%N (va 0%N (phi n) (p z))*NA 1%N (va 1%N (da (phi n)) (q z))<=k.
  have h:=ler_pM hNP hNDQ hPhiP hDQ;by rewrite mul1r in h.
have hPureBound:NC 1%N (vc 1%N (dc (Pure (phi n) (phi n))) z)<=2*k.
  have h:=le_trans hPure (lerD hFirst hSecond).
  by rewrite -mulr2n -mulr_natl in h.
have hw:0<=reciprocal_power_series_weight R 3%N n:=
  ltW (reciprocal_power_series_weight_positive R 3%N n).
rewrite /weighted_interval_product_test_term (linZ (hom_linear dc)) current_test_scale_value
  (real_seminorm_scale (@current_form_comass_real_norm R h2 (1+1)%N 1%N).1)
  (ger0_norm hw).
have hBound:=ler_wpM2l hw hPureBound.
rewrite mulrCA /k reciprocal_cube_derivative_product mulr1 in hBound.
exact:hBound.
Qed.
End WeightedIntervalProductTestTermBounds.
