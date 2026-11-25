(** Federer (1969), 4.1.12, pp. 367–368: the
    zero-mass and finite-mass algebra needed by the
    attained flat decomposition. Reuse the original
    mass supremum and the absolute variation bound
    already proved in 4.1.5, p. 349. *)
From mathcomp Require Import all_boot all_order all_algebra functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentCoefficientNorms CurrentSpaces CurrentMassUP CurrentMassSealed
  CurrentMassBasic CurrentGlobalComassSealed CurrentGlobalComassBound ExtendedSupremumUP
  SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain DistributionVariationBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentMassFiniteAlgebra.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT := [the choiceType of set_type (U:set (real_norm_metric_space hNX))].
Local Notation C := (@current_space R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation ev := (@current_test_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R (real_norm_metric_space hNX) U Y DT values).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation M := (@CurrentMass.value R h2 n m U hU).

(** Source for [current_mass_zero]: the original zero
    current has mass zero, supporting the infinite
    endpoint of the minimum formula in Federer
    4.1.12, pp. 367–368, including empty U. *)
Lemma current_mass_zero:M (0:C)=0.
Proof.
apply/eqP;rewrite eq_le;apply/andP;split;last exact:current_mass_nonnegative.
apply:(extended_supremum_least (@CurrentMass.laws R h2 n m U hU (0:C)))=>a [phi [_ <-]].
by rewrite (linear0 action) hom_zeroE.
Qed.

(** Source for [current_mass_unit_absolute]: the original
    current mass bounds the absolute action on every
    global unit-comass test, supporting Federer 4.1.12,
    pp. 367–368. This is the earlier absolute
    variation estimate on the original current domain. *)
Lemma current_mass_unit_absolute (T:C) (phi:DT):
  (@CurrentGlobalComass.value R h2 n m U (ev phi)<=1)%E->
  (`|action T phi|%:E<=M T)%E.
Proof.
move=>hPhi.
apply:(@distribution_variation_absolute_bound R UT Y NY hNY DT dvalues (action T)
  (fun _=>1) (M T) (@current_mass_majorant_one R h2 n m U hU T) phi)=>x.
exact:((@current_global_comass_bound R h2 n m U (ev phi) 1).1 hPhi
  (set_val x) (set_valP x)).
Qed.

(** Source for [current_finite_mass_linear_combination]:
    finite-mass currents are closed under original
    real linear combinations, supporting the normality
    of the optimal filling in Federer 4.1.12,
    pp. 367–368. The existing absolute unit-test
    bound supplies the finite mass estimate. *)
Theorem current_finite_mass_linear_combination c (S T:C):
  (M S < +oo)%E->(M T < +oo)%E->(M ((c*:S+T)%R) < +oo)%E.
Proof.
move=>hS hT.
have [a [ha hA]]:=@current_finite_mass_value R h2 n m U hU S hS.
have [b [hb hB]]:=@current_finite_mass_value R h2 n m U hU T hT.
have hUpper:(M ((c*:S+T)%R)<=(`|c| * a+b)%:E)%E.
  apply:(extended_supremum_least (@CurrentMass.laws R h2 n m U hU (c*:S+T)))=>z [phi [hPhi <-]].
  have hSB:=current_mass_unit_absolute S hPhi.
  have hTB:=current_mass_unit_absolute T hPhi.
  rewrite hA lee_fin in hSB;rewrite hB lee_fin in hTB.
  rewrite (linearP action) hom_addE hom_scaleE lee_fin.
  apply:(le_trans (lerD (ler_norm (c * action S phi)) (ler_norm (action T phi)))).
  rewrite normrM;exact:lerD (ler_wpM2l (normr_ge0 c) hSB) hTB.
exact:le_lt_trans hUpper (ltry _).
Qed.
End CurrentMassFiniteAlgebra.
