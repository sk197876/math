(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 320: the
    variety germ attached to a finite generator family is
    independent of that family and its neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing
  SetGermUP SetGermOrder CommutativeIdealUP HolomorphicGermVanishingSealed HolomorphicGermVanishingIdeal
  FiniteZeroSetSealed FiniteHolomorphicGermZeroSystem FiniteHolomorphicGermVanishingContainment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FiniteGenerators.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable a:X.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)].
Local Notation P:=(@holomorphic_representative_type R X NX hNX a).
Local Notation value:=(@holomorphic_representative_value R X NX hNX a).
Local Notation germ:=(@holomorphic_germ R X NX hNX a).
Local Notation sgerm:=(@set_germ T a).
Local Notation ideal:=(@HolomorphicSetIdeal.value R X NX hNX a).
Local Notation zero I U f:=(@FiniteZeroSet.value [the zmodType of (ComplexScalars.C R)^o] X U I (fun i=>value (f i))).

(** Source for [finite_generated_holomorphic_germ_ideal_in_variety]: the
    printed inclusion I contained in ideal var(I),
    3.4.5, p. 320, for any original generator system. *)
Lemma finite_generated_holomorphic_germ_ideal_in_variety (I:finType) (f:I->P) (U:set X) (J:set A):
  U a ->@open T U ->
  @is_generated_commutative_ideal A [set alpha|exists i,germ (f i)=alpha] J ->
  J `<=` ideal (sgerm (zero I U f)).
Proof.
move=>ha hU hGenerated.
apply:(generated_commutative_ideal_minimal hGenerated
  (@holomorphic_set_ideal_ring_laws R X NX hNX a (sgerm (zero I U f)))).
move=>alpha [i <-];exact:(@finite_holomorphic_germ_zero_system_generators_vanish R X NX hNX a I f U ha hU i).
Qed.

(** Source for [finite_generated_holomorphic_germ_variety_independent]:
    any two original finite systems generating the same
    ideal give the same variety germ, 3.4.5, p. 320. *)
Theorem finite_generated_holomorphic_germ_variety_independent (I J:finType) (f:I->P) (g:J->P)
    (U V:set X) (L:set A):
  U a ->@open T U ->V a ->@open T V ->
  @is_generated_commutative_ideal A [set alpha|exists i,germ (f i)=alpha] L ->
  @is_generated_commutative_ideal A [set alpha|exists j,germ (g j)=alpha] L ->
  sgerm (zero I U f)=sgerm (zero J V g).
Proof.
move=>haU hU haV hV hF hG.
have hFIdeal:=finite_generated_holomorphic_germ_ideal_in_variety haU hU hF.
have hGIdeal:=finite_generated_holomorphic_germ_ideal_in_variety haV hV hG.
apply:set_germ_subset_antisymmetric.
- apply:(@finite_holomorphic_germ_vanishing_containment R X NX hNX a J g V (zero I U f) haV hV)=>j.
  apply:hFIdeal;apply:(generated_commutative_ideal_contains hG).
  by exists j.
- apply:(@finite_holomorphic_germ_vanishing_containment R X NX hNX a I f U (zero J V g) haU hU)=>i.
  apply:hGIdeal;apply:(generated_commutative_ideal_contains hF).
  by exists i.
Qed.
End FiniteGenerators.
