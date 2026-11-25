(** Federer (1969), 4.1.12, p. 369:
    the actual original phi_k have
    M(phi_k)=1 and M(d phi_k)<=k^3.
    Their independent range, peak and derivative
    laws imply these original global supremum assertions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate AlternatingForms AlternatingZero
  CurrentSpaces CurrentCoefficientNorms CurrentZeroCovectorMaps CurrentTestExteriorDerivative
  ExtendedSupremumUP CurrentGlobalComassUP CurrentGlobalComassSealed CurrentGlobalComassBound
  WeightedIntervalEndpoints WeightedIntervalCutoffUP WeightedIntervalCutoffSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section WeightedIntervalCutoffNorms.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>
  norm_full_domain_interior (inner_norm (@euclidean_inner_productP R 1%N)) x).
Local Notation phi := (@WeightedIntervalCutoff.value R h2).
Local Notation value d := (@current_test_value R h2 1%N Full hFull d).
Local Notation N d := (@current_form_comass R h2 1%N d).
Local Notation M d := (@CurrentGlobalComass.value R h2 1%N d Full).
Local Notation d := (@current_test_exterior_derivative R h2 1%N 0%N Full hFull).

(** Source for [weighted_interval_cutoff_point_comass]:
    each original phi_k has pointwise
    comass at most one, supporting
    Federer 4.1.12, p. 369. *)
Lemma weighted_interval_cutoff_point_comass n x:N 0%N (value 0%N (phi n) x)<=1.
Proof.
have hRange:=(@WeightedIntervalCutoff.laws R h2 n).2.1 x.
rewrite current_zero_form_coefficient_norm (ger0_norm (andP hRange).1).
exact:(andP hRange).2.
Qed.

(** Source for [weighted_interval_cutoff_comass]: the
    original exact M(phi_k)=1 follows
    from its unit peak and upper
    bound, Federer 4.1.12, p. 369. *)
Theorem weighted_interval_cutoff_comass n:M 0%N (value 0%N (phi n))= 1%:E.
Proof.
have hUpper:(M 0%N (value 0%N (phi n))<=1%:E)%E.
  apply:(@current_global_comass_bound R h2 1%N 0%N Full (value 0%N (phi n)) 1).2=>x _.
  exact:weighted_interval_cutoff_point_comass.
have hLower:(1%:E<=M 0%N (value 0%N (phi n)))%E.
  apply:(extended_supremum_upper (@CurrentGlobalComass.laws R h2 1%N 0%N Full
    (value 0%N (phi n)))).
  exists (euclidean_one_embed (weighted_interval_right_endpoint R n));split;first exact:Logic.I.
  rewrite (@WeightedIntervalCutoff.laws R h2 n).2.2.1 current_zero_form_coefficient_norm.
  change (`|zero_form_value (@zero_form R X R^o 1)|= 1).
  by rewrite zero_formK normr1.
apply/eqP;by rewrite eq_le hUpper hLower.
Qed.

(** Source for [weighted_interval_cutoff_derivative_comass]:
    the original M(d phi_k)<=k^3
    retains its exact coefficient, Federer
    4.1.12, p. 369. *)
Theorem weighted_interval_cutoff_derivative_comass n:
  (M 1%N (value 1%N (d (phi n)))<=(((n.+1)%:R:R)^+3)%:E)%E.
Proof.
apply:(@current_global_comass_bound R h2 1%N 1%N Full
  (value 1%N (d (phi n))) (((n.+1)%:R:R)^+3)).2=>x _.
exact:(@WeightedIntervalCutoff.laws R h2 n).2.2.2 x.
Qed.
End WeightedIntervalCutoffNorms.
