(** Federer (1969), 4.1.12, pp. 367–368: a
    larger compact index increases the form seminorm
    and decreases its dual current seminorm. The
    original flat closures therefore form a directed
    family, with no compact exhaustion imposed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms
  CurrentCoefficientNorms CurrentSpaces SmoothCompactSet SmoothFunctionTopology
  SmoothDerivativeSeminormUP SmoothDerivativeSeminormLaws SmoothTestSpaces
  SmoothCurrentExteriorDerivative CurrentFlatFormSeminormSealed CurrentFlatFormSeminormLaws
  CurrentFlatDualSeminormUP CurrentFlatDualSeminormSealed CurrentFlatNorm
  ExtendedSupremumUP FlatCurrentsUP NormalCurrentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatCompactMonotone.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y d := (A_m X R^o d).
Local Notation NY d := (@current_form_comass R h2 n d).
Local Notation hNY d := (@current_form_comass_real_norm R h2 n d).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variables K L:smooth_compact_set hNX U.
Hypothesis hKL:smooth_compact_carrier K `<=` smooth_compact_carrier L.
Local Notation E d := (@current_smooth_space R h2 n U hU d).
Local Notation D d := (@current_smooth_derivatives R h2 n U hU d).
Local Notation hD d := (@current_smooth_derivative_laws R h2 n U hU d).
Local Notation nu d := (smooth_function_derivative_seminorm (hD d)).
Local Notation C := (@current_space R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).

(** Source for [current_zeroth_compact_monotone]: the
    original order-zero derivative seminorm increases
    with K, supporting Federer 4.1.12, pp. 367–368,
    by the preceding derivative-supremum law. *)
Lemma current_zeroth_compact_monotone d (phi:E d):nu d K 0%N phi<=nu d L 0%N phi.
Proof.
exact:(@smooth_derivative_seminorm_monotone R X (Y d) NX (NY d) hNX (hNY d) U (E d) (D d)
  K 0%N (nu d K 0%N) (smooth_function_derivative_seminorm_laws (hD d) K 0%N)
  L 0%N (nu d L 0%N) (smooth_function_derivative_seminorm_laws (hD d) L 0%N)
  (leqnn 0%N) hKL phi).
Qed.

(** Source for [current_flat_form_compact_monotone]:
    K contained in L implies F_K(phi)<=F_L(phi),
    supporting Federer 4.1.12, pp. 367–368.
    Both terms use the actual exterior derivative. *)
Theorem current_flat_form_compact_monotone (phi:E m):
  @CurrentFlatFormSeminorm.value R h2 n m U hU K phi<=
    @CurrentFlatFormSeminorm.value R h2 n m U hU L phi.
Proof.
rewrite !current_flat_form_seminorm_formula.
apply:le_max2;exact:current_zeroth_compact_monotone.
Qed.

(** Source for [current_flat_compact_monotone]: K
    contained in L implies F_L(T)<=F_K(T),
    supporting the directed original flat closures
    in Federer 4.1.12, p. 368. Infinite
    values and arbitrary actual currents are retained. *)
Theorem current_flat_compact_monotone (T:C):
  (@current_flat_norm R h2 n m U hU L T<=@current_flat_norm R h2 n m U hU K T)%E.
Proof.
apply:(extended_supremum_least (@CurrentFlatDualSeminorm.laws R h2 n m U hU L (action T)))
  =>a [phi [hPhi hValue]].
apply:(extended_supremum_upper (@CurrentFlatDualSeminorm.laws R h2 n m U hU K (action T))).
exists phi;split;last exact:hValue.
exact:le_trans (current_flat_form_compact_monotone (smooth_test_inclusion
  (@current_smooth_space_laws R h2 n U hU m) phi)) hPhi.
Qed.

(** Source for [flat_current_compact_monotone]: the
    original inclusion F_(m,K)(U) contained in
    F_(m,L)(U) when K is contained in L,
    supporting their union in Federer 4.1.12,
    p. 368. The same normal approximants suffice. *)
Theorem flat_current_compact_monotone (T:C):
  @is_flat_current_supported_in R h2 n m U hU K T->
    @is_flat_current_supported_in R h2 n m U hU L T.
Proof.
move=>hFlat epsilon hEpsilon.
have [S [[hNormal hSupport] hApprox]]:=@hFlat epsilon hEpsilon.
exists S;split.
- split;first exact:hNormal.
  move=>x hx;exact:hKL x (hSupport x hx).
- exact:le_lt_trans (current_flat_compact_monotone (T-S)) hApprox.
Qed.
End CurrentFlatCompactMonotone.
