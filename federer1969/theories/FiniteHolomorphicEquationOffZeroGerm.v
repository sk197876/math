(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 331:
    identify the actual equation system outside
    delta=0 with the corresponding original set
    germ. Reuse the generator-independent definition
    of var(F) from 3.4.5, p. 320. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicUP RealNormUP NormMetric NormAnalyticUP HolomorphicGermRepresentatives
  HolomorphicGermUP HolomorphicGermRing SetGermUP SetGermSealed CommutativeIdealUP
  FiniteAnalyticVarietyUP FiniteZeroSetSealed HolomorphicZeroGermSealed
  HolomorphicIdealVarietyGermUP HolomorphicIdealVarietyGermSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_holomorphic_equation_off_zero_germ]:
    Z consists of the common zeroes
    of the original finite equations in
    their neighbourhood, excluding delta=0,
    3.4.12, p. 339, extending 3.4.8(10), pp. 327 and 331. *)
Theorem finite_holomorphic_equation_off_zero_germ (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
    (F:set [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)])
    (hF:is_finitely_generated_commutative_ideal F) (J:finType)
    (f:J->@holomorphic_representative_type R X NX hNX a)
    (d:@holomorphic_representative_type R X NX hNX a) (U:set X):
  U a ->@open (real_norm_metric_space hNX) U ->
  (forall j,@is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)
    U (holomorphic_representative_value (f j))) ->
  @is_generated_commutative_ideal [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]
    [set alpha|exists j,holomorphic_germ (f j)=alpha] F ->
  @SetGerms.meet (Topological.clone (real_norm_metric_space hNX) _) a
    (@HolomorphicIdealVarietyGerm.value R X NX hNX a F hF)
    (@SetGerms.neg (Topological.clone (real_norm_metric_space hNX) _) a
      (@HolomorphicZeroGerm.value R X NX hNX a (holomorphic_germ d))) =
  @set_germ (Topological.clone (real_norm_metric_space hNX) _) a
    [set x|U x /\(forall j,holomorphic_representative_value (f j) x=0) /\
      holomorphic_representative_value d x!=0].
Proof.
move=>ha hU hAnalytic hGenerated.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
rewrite (@holomorphic_ideal_variety_germ_original_equation R X NX hNX a F _
  (@HolomorphicIdealVarietyGerm.laws R X NX hNX a F hF) J f U ha hU hAnalytic hGenerated)
  -(@HolomorphicZeroGerm.laws R X NX hNX a (holomorphic_germ d) d (erefl _))
  (@set_germ_complement_equation T a _ _ _ (@SetGerms.laws T a))
  (@set_germ_intersection_equation T a _ _ _ (@SetGerms.laws T a)).
congr (@set_germ T a _);apply/seteqP;split.
- move=>x [hZero hNot].
  have [hu hValues]:=(original_zero_set_membership (FiniteZeroSet.laws U _) x).1 hZero.
  split;first exact:hu.
  split;first exact:hValues.
  apply/eqP;exact:hNot.
- move=>x [hu [hValues hNot]];split.
  + apply/(original_zero_set_membership (FiniteZeroSet.laws U _) x);by split.
  + by move=>hZero;move/eqP:hNot;apply.
Qed.
