(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5), p. 328:
    the original vanishing ideal is an ideal, is
    proper, and every one minus its elements is a
    unit. These claims follow from the actual centre
    homomorphism and the proved unit criterion of
    3.4.7, p. 325. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm RealNormUP HolomorphicGermRing HolomorphicGermValueSealed
  HolomorphicGermValueUnits CommutativeIdealUP CommutativeFactorizationUP
  CommutativeIdealTrivial HolomorphicVanishingIdealUP HolomorphicVanishingIdealSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Laws.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Variable hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX.
Variable a:X.
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)].
Local Notation M:=(@HolomorphicVanishingIdeal.value R X NX hNX a).
Local Notation value:=(@HolomorphicGermValue.map R X NX hNX a).

(** Source for [holomorphic_vanishing_ideal_is_ideal]: actual
    vanishing germs form an ideal, supporting the local
    ring argument of 3.4.7, p. 325, and
    closedness in 3.4.8(5), p. 328. *)
Lemma holomorphic_vanishing_ideal_is_ideal:is_commutative_ideal M.
Proof.
have hM:=@HolomorphicVanishingIdeal.laws R X NX hNX a.
constructor.
- apply/(hM 0);exact:rmorph0.
- move=>alpha beta ha hb;apply/(hM (alpha+beta)).
  by rewrite rmorphD (hM alpha).1 // (hM beta).1 // addr0.
- move=>alpha ha;apply/(hM (-alpha)).
  by rewrite rmorphN (hM alpha).1 // oppr0.
- move=>alpha beta hb;apply/(hM (alpha*beta)).
  by rewrite rmorphM (hM beta).1 // mulr0.
Qed.

(** Source for [holomorphic_vanishing_ideal_proper]: one has
    nonzero centre value, so the original vanishing ideal
    is proper, supporting the same arguments, pp. 325, 328. *)
Lemma holomorphic_vanishing_ideal_proper:~M 1.
Proof.
move/(@HolomorphicVanishingIdeal.laws R X NX hNX a 1).1.
rewrite rmorph1;by move/eqP;rewrite oner_eq0.
Qed.

(** Source for [holomorphic_vanishing_one_minus_unit]: every
    one minus a vanishing germ has centre value one
    and hence an actual inverse, supporting the local
    closedness argument for 3.4.8(5), p. 328. *)
Lemma holomorphic_vanishing_one_minus_unit (alpha:G):M alpha ->is_commutative_unit (1-alpha).
Proof.
move=>ha;apply/(@holomorphic_germ_value_unit_equivalence R X NX hNX a (1-alpha)).
rewrite rmorphB rmorph1 (@HolomorphicVanishingIdeal.laws R X NX hNX a alpha).1 // subr0.
by move/eqP;rewrite oner_eq0.
Qed.

(** Source for [holomorphic_proper_ideal_vanishes]: every
    original proper ideal lies in the vanishing ideal,
    since a nonvanishing germ is a unit. This
    establishes the local ideal used in 3.4.7,
    p. 325, and 3.4.8(5), p. 328. *)
Lemma holomorphic_proper_ideal_vanishes (I:set G):
  is_commutative_ideal I ->~I 1 ->I `<=` M.
Proof.
move=>hI hProper alpha ha.
apply/(@HolomorphicVanishingIdeal.laws R X NX hNX a alpha).
apply:contrapT=>hNonzero;apply:hProper.
apply:(@commutative_ideal_unit_contains_one G I hI alpha ha).
exact:(@holomorphic_germ_value_unit_equivalence R X NX hNX a alpha).2 hNonzero.
Qed.
End Laws.
