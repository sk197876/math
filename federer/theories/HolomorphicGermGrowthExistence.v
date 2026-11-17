(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: existence
    and uniqueness of the exact factorial-growth classes. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermOperationsUP RealNormUP HolomorphicGermUP HolomorphicGermGrowthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_germ_growth_class_exists]: the
    subsets displayed in 3.4.5, p. 319, exist
    with exactly the independently stated derivative bounds. *)
Theorem holomorphic_germ_growth_class_exists (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) s t:
  exists C:set (holomorphic_germ_space hNX a),is_holomorphic_germ_growth_class s t C.
Proof.
exists (fun alpha=>forall m,holomorphic_germ_jet_norm m alpha<=s%:R*t%:R^+m*(m`!)%:R).
by constructor.
Qed.

(** Source for [holomorphic_germ_growth_class_unique]: all-order
    membership determines the original subset uniquely,
    3.4.5, p. 319. *)
Lemma holomorphic_germ_growth_class_unique (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) s t
    (C D:set (holomorphic_germ_space hNX a)):
  is_holomorphic_germ_growth_class s t C ->is_holomorphic_germ_growth_class s t D ->C=D.
Proof.
move=>hC hD;apply/seteqP;split=>alpha hAlpha.
- exact:((holomorphic_germ_growth_membership hD alpha).2 ((holomorphic_germ_growth_membership hC alpha).1 hAlpha)).
- exact:((holomorphic_germ_growth_membership hC alpha).2 ((holomorphic_germ_growth_membership hD alpha).1 hAlpha)).
Qed.
