(** Federer (1969), 3.4.5, p. 320: the
    original ideal-to-variety operation enlarges no ideal
    already arising by local vanishing on a set germ. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing
  SetGermUP SetGermLaws SetGermOrder CommutativeIdealUP
  GermVanishingSealed GermVanishingMonotonicity FiniteZeroSetSealed FiniteGermGenerators
  FiniteGermVanishingContainment FiniteGeneratedGermVariety IdealVarietyGermUP IdealVarietyGermSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Laws.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX a).
Local Notation var I hI:=(@IdealVarietyGerm.value R X NX hNX a I hI).

(** Source for [ideal_in_vanishing_ideal_of_variety]: the
    printed inclusion I contained in ideal var(I),
    3.4.5, p. 320, for the original opaque operations. *)
Lemma ideal_in_vanishing_ideal_of_variety (I:set A)
    (hI:is_finitely_generated_commutative_ideal I):I `<=` ideal (var I hI).
Proof.
have [J [f [U [ha [hU [hAnalytic hGenerated]]]]]]:=
  @finite_germ_generator_system_exists R X NX hNX a I hI.
rewrite (@ideal_variety_germ_original_equation R X NX hNX a I (var I hI)
  (@IdealVarietyGerm.laws R X NX hNX a I hI) J f U ha hU hAnalytic hGenerated).
exact:(@finite_generated_germ_ideal_in_variety R X NX hNX a J f U I ha hU hGenerated).
Qed.

(** Source for [set_germ_in_variety_of_its_ideal]: every
    original set germ is contained in the variety of its
    finitely generated ideal, supporting 3.4.5, p. 320. *)
Lemma set_germ_in_variety_of_its_ideal (sigma:@set_germ_space T a)
    (hI:@is_finitely_generated_commutative_ideal A (ideal sigma)):
  set_germ_subset sigma (var (ideal sigma) hI).
Proof.
move:hI.
have [S <-]:=@set_germ_has_representative T a sigma.
move=>hI.
have [J [f [U [ha [hU [hAnalytic hGenerated]]]]]]:=
  @finite_germ_generator_system_exists R X NX hNX a (ideal (@set_germ T a S)) hI.
rewrite (@ideal_variety_germ_original_equation R X NX hNX a _ _
  (@IdealVarietyGerm.laws R X NX hNX a _ hI) J f U ha hU hAnalytic hGenerated).
apply:(@finite_germ_vanishing_containment R X NX hNX a J f U S ha hU)=>j.
apply:(generated_commutative_ideal_contains hGenerated);by exists j.
Qed.

(** Source for [vanishing_ideal_variety_recovery]: equality
    holds when I is the ideal of an original set germ,
    precisely as stated in 3.4.5, p. 320. *)
Theorem vanishing_ideal_variety_recovery (sigma:@set_germ_space T a)
    (hI:@is_finitely_generated_commutative_ideal A (ideal sigma)):
  ideal (var (ideal sigma) hI)=ideal sigma.
Proof.
apply/seteqP;split.
- exact:(@analytic_set_ideal_antitone R X NX hNX a sigma _
    (set_germ_in_variety_of_its_ideal hI)).
- exact:ideal_in_vanishing_ideal_of_variety.
Qed.
End Laws.
