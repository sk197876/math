(** Federer (1969), 4.1.13, pp. 369–370: restricting
    a current to the smaller support neighbourhood does not
    increase its mass. The actual test extension of 4.1.1,
    p. 345, preserves values and introduces only zeros. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentCoefficientNorms CurrentSpaces SmoothTestEvaluation
  CurrentGlobalComassUP CurrentGlobalComassSealed CurrentMassUP CurrentMassSealed
  CurrentMassBasic ExtendedSupremumUP CurrentOpenRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section CurrentOpenRestrictionMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Variables U V:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall x,V x->norm_domain_interior NX V x.
Hypothesis hUV:forall x,U x->V x.
Local Notation DU := (@current_test_space R h2 n U hU m).
Local Notation hEU := (@current_smooth_space_laws R h2 n U hU m).
Local Notation evU := (@current_test_value R h2 n U hU m).
Local Notation evV := (@current_test_value R h2 n V hV m).
Local Notation P := (@current_open_test_extension R h2 n m U V hU hV hUV).

(** Source for [current_open_test_extension_unit_comass]:
    an original unit-comass test on U remains admissible
    after zero extension to V, supporting the neighbourhood
    replacement in Federer 4.1.13, pp. 369–370.
    The statement includes empty U and V; equality of
    their possibly minus-infinite global comasses is not asserted. *)
Theorem current_open_test_extension_unit_comass (phi:DU):
  (@CurrentGlobalComass.value R h2 n m U (evU phi)<=1)%E->
    (@CurrentGlobalComass.value R h2 n m V (evV (P phi))<=1)%E.
Proof.
move=>hPhi.
apply:(extended_supremum_least (@CurrentGlobalComass.laws R h2 n m V (evV (P phi))))
  =>a [x [hx <-]].
rewrite current_open_test_extension_values.
case:(pselect (U x))=>hUx.
- apply:(le_trans _ hPhi).
  apply:(extended_supremum_upper (@CurrentGlobalComass.laws R h2 n m U (evU phi))).
  by exists x.
- have hZero:evU phi x=0:=smooth_test_value_outside hEU phi hUx.
  rewrite hZero (real_seminorm_zero (@current_form_comass_real_norm R h2 n m).1).
  by rewrite lee_fin.
Qed.

(** Source for [current_open_restriction_mass_bound]:
    the original restriction R_U T has mass at most
    M(T), supporting the replacement of U in Federer
    4.1.13, pp. 369–370. The proof uses the
    original test supremum and allows infinite masses. *)
Theorem current_open_restriction_mass_bound
    (T:@current_space R h2 n V hV m):
  (@CurrentMass.value R h2 n m U hU
    (@current_open_restriction R h2 n m U V hU hV hUV T)<=
    @CurrentMass.value R h2 n m V hV T)%E.
Proof.
apply:(extended_supremum_least (@CurrentMass.laws R h2 n m U hU
  (@current_open_restriction R h2 n m U V hU hV hUV T)))=>a [phi [hPhi <-]].
rewrite current_open_restriction_evaluation.
apply:current_mass_unit_test_upper.
exact:current_open_test_extension_unit_comass hPhi.
Qed.
End CurrentOpenRestrictionMass.
