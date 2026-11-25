(** Federer (1969), 4.1.7, pp. 355, 358:
    actual empty-domain current regressions.
    The literal global comass is the
    supremum of the empty value set,
    hence minus infinity by 2.1.1,
    p. 51. Every actual current
    on the empty domain still has
    mass zero, since its test space is zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces CurrentEvaluation
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation ExtendedSupremumUP CurrentGlobalComassUP
  CurrentGlobalComassSealed CurrentMassUP CurrentMassSealed CurrentMassBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EmptyCurrentDomainExamples.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).

(** Source for [empty_current_domain_open]:
    the empty domain satisfies the original
    openness hypothesis, a regression supporting
    Federer 4.1.7, p. 355. *)
Lemma empty_current_domain_open (x:X):set0 x->norm_domain_interior N set0 x.
Proof. by []. Qed.
Local Notation hEmpty := empty_current_domain_open.
Local Notation C := (@current_space R h2 n set0 hEmpty m).
Local Notation DT := (@current_test_space R h2 n set0 hEmpty m).
Local Notation hE := (@current_smooth_space_laws R h2 n set0 hEmpty m).
Local Notation action := (@current_value R h2 n set0 hEmpty m).

(** Source for [empty_current_domain_test_zero]:
    every actual test form on the
    empty open domain vanishes, a
    regression supporting Federer 4.1.7, p. 355,
    and the original test space of
    4.1.1, p. 344. *)
Example empty_current_domain_test_zero (phi:DT):phi=0.
Proof. apply:(smooth_test_values_extensional hE);by move=>x hx. Qed.

(** Source for [empty_current_domain_current_zero]:
    every actual current on the empty
    domain is zero, a regression supporting
    Federer 4.1.7, p. 355. The
    actual continuous-dual action determines the current. *)
Example empty_current_domain_current_zero (T:C):T=0.
Proof.
apply:(@current_values_extensional R h2 n m set0 hEmpty)=>phi.
rewrite (empty_current_domain_test_zero phi) !linear0 ?hom_zeroE;by [].
Qed.

(** Source for [empty_current_global_comass]:
    the original global-comass supremum on
    the empty domain is minus infinity,
    a regression for Federer 4.1.7,
    p. 358, using the explicit empty
    supremum convention in 2.1.1, p. 51. *)
Example empty_current_global_comass (phi:X->A_m X R^o m):
  @CurrentGlobalComass.value R h2 n m set0 phi = (-oo)%E.
Proof.
apply:(extended_supremum_unique (@CurrentGlobalComass.laws R h2 n m set0 phi)).
constructor.
- by move=>a [x [hx _]].
- move=>d _;exact:leNye.
Qed.

(** Source for [empty_current_domain_mass_zero]:
    the actual mass on the empty
    current domain is zero, a regression
    for Federer 4.1.7, p. 358.
    The empty global-comass value leaves the
    zero test admissible and changes no current value. *)
Example empty_current_domain_mass_zero (T:C):
  @CurrentMass.value R h2 n m set0 hEmpty T=0.
Proof.
apply/eqP;rewrite eq_le;apply/andP;split;last exact:current_mass_nonnegative.
apply:(extended_supremum_least (@CurrentMass.laws R h2 n m set0 hEmpty T))=>a [phi [_ <-]].
rewrite (empty_current_domain_test_zero phi) linear0;by rewrite lee_fin.
Qed.
End EmptyCurrentDomainExamples.
