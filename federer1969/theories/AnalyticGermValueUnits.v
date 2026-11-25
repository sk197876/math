(** Federer (1969), 3.4.7, p. 325: the
    original preparation multiplier is a unit precisely
    when its centre value is nonzero. The sealed
    value map retains every actual representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermRingLaws AnalyticGermRing AnalyticGermUnits AnalyticGermValueUP AnalyticGermValueSealed
  CommutativeFactorizationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [analytic_germ_value_unit_equivalence]: original
    centre value detects actual invertibility, as used
    for Q in 3.4.7, p. 325. The reciprocal
    analytic representative in the earlier unit theorem
    supplies the inverse. *)
Theorem analytic_germ_value_unit_equivalence (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (alpha:@analytic_germ_ring R X NX hNX a):
  is_commutative_unit alpha <->@AnalyticGermValue.map R X NX hNX a alpha<>0.
Proof.
have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
rewrite -hf (@AnalyticGermValue.laws R X NX hNX a f).
exact:(@analytic_germ_unit_iff_nonzero_value R X NX hNX a f).
Qed.

(** Source for [analytic_germ_nonunit_centre_zero]: every
    original nonunit has centre value zero, supporting
    the factorization step of 3.4.7, p. 325. *)
Lemma analytic_germ_nonunit_centre_zero (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (alpha:@analytic_germ_ring R X NX hNX a):
  ~is_commutative_unit alpha ->@AnalyticGermValue.map R X NX hNX a alpha = 0.
Proof.
move=>hNonunit;apply:contrapT=>hNonzero;apply:hNonunit.
exact:(@analytic_germ_value_unit_equivalence R X NX hNX a alpha).2 hNonzero.
Qed.
