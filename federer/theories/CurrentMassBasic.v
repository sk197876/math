(** Federer (1969), 4.1.7, p. 358: basic
    consequences of the original current mass.
    The actual test supremum is nonnegative,
    bounds every admissible test and has a
    real value whenever it is finite. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain DistributionVariationUP
  DistributionVariationBasic ExtendedSupremumUP CurrentGlobalComassSealed CurrentMassUP CurrentMassVariation CurrentMassSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentMassBasic.
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

(** Source for [current_mass_majorant_one]: the
    actual mass has exactly the earlier scalar
    supremum law with majorant one, supporting
    Federer 4.1.7, p. 358. *)
Theorem current_mass_majorant_one (T:C):
  is_distribution_variation_value NY dvalues (action T) (fun _=>1) (M T).
Proof.
exact:(@current_mass_variation_law R h2 n m U hU T (M T)).1
  (@CurrentMass.laws R h2 n m U hU T).
Qed.

(** Source for [current_mass_nonnegative]: the
    original current mass is nonnegative, supporting
    Federer 4.1.7, p. 358. The
    zero test is always admissible. *)
Theorem current_mass_nonnegative (T:C):(0<=M T)%E.
Proof.
exact:(@distribution_variation_nonnegative R UT Y NY hNY DT dvalues (action T)
  (fun _=>1) (M T) (fun _=>ler01) (current_mass_majorant_one T)).
Qed.

(** Source for [current_finite_mass_value]: finite
    original mass has a nonnegative real
    supremum value, supporting Federer 4.1.7,
    p. 358. Both infinite endpoints are
    excluded by their proved order properties. *)
Theorem current_finite_mass_value (T:C):
  (M T < +oo)%E->exists b:R,0<=b /\M T=b%:E.
Proof.
move=>hFinite.
have hNonnegative:=current_mass_nonnegative T.
have hNumber:M T \is a fin_num.
  rewrite (ge0_fin_numE hNonnegative);exact:hFinite.
exists (fine (M T));split.
- have hEq:M T=(fine (M T))%:E by rewrite fineK.
  by rewrite hEq lee_fin in hNonnegative.
- by rewrite fineK.
Qed.

(** Source for [current_mass_unit_test_upper]: the
    original mass bounds each test of global
    comass at most one, supporting Federer
    4.1.7, p. 358. *)
Theorem current_mass_unit_test_upper (T:C) (phi:DT):
  (@CurrentGlobalComass.value R h2 n m U (ev phi)<=1)%E->
    ((action T phi)%:E<=M T)%E.
Proof.
move=>hPhi;apply:(extended_supremum_upper (@CurrentMass.laws R h2 n m U hU T)).
by exists phi.
Qed.
End CurrentMassBasic.
