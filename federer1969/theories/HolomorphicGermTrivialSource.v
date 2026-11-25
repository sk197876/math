(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: the
    scalar base case of the dimension induction. On
    a zero-dimensional source every germ is a constant;
    nonzero constants are actual analytic units. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicGermArithmeticRepresentatives RealNormUP HolomorphicGermRepresentatives HolomorphicGermUP
  HolomorphicGermRingLaws HolomorphicGermRing CommutativeFactorizationUP
  CommutativeDivisionRingNoetherian HolomorphicGermUnits CommutativeIdealUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_trivial_source_constant]:
    the scalar base case of 3.4.7, p. 325.
    An analytic representative on a trivial vector space
    defines its constant-value germ at the original centre. *)
Lemma holomorphic_germ_trivial_source_constant (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a
    (f:@holomorphic_representative_type R X NX hNX a):
  (forall x:X,x = a) ->holomorphic_germ f =
    holomorphic_germ (@holomorphic_constant_representative R X NX hNX a
      (holomorphic_representative_value f a)).
Proof.
move=>hTrivial;apply:holomorphic_germ_pointwise_equality=>x.
change (holomorphic_representative_value f x = holomorphic_representative_value f a).
by rewrite (hTrivial x).
Qed.

(** Source for [holomorphic_germ_trivial_source_unit]: the
    nonzero scalar germs in the base case of 3.4.7,
    p. 325, are units. Every inverse is supplied
    by the proved actual analytic reciprocal theorem. *)
Lemma holomorphic_germ_trivial_source_unit (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a:
  (forall x:X,x = a) ->forall alpha:@holomorphic_germ_ring R X NX hNX a,
    alpha<>0 ->is_commutative_unit alpha.
Proof.
move=>hTrivial alpha hNonzero.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
rewrite -hf;apply:(@holomorphic_germ_unit_iff_nonzero_value R X NX hNX a f).2=>hValue.
apply:hNonzero;rewrite -hf (@holomorphic_germ_trivial_source_constant R X NX hNX a f hTrivial) hValue.
reflexivity.
Qed.

(** Source for [holomorphic_germ_trivial_source_noetherian]:
    the Noetherian scalar base case in 3.4.7, p. 325. *)
Theorem holomorphic_germ_trivial_source_noetherian (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a:
  (forall x:X,x = a) ->
  is_noetherian_commutative_ring [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)].
Proof.
move=>hTrivial;apply:commutative_division_ring_noetherian.
exact:holomorphic_germ_trivial_source_unit hTrivial.
Qed.

(** Source for [holomorphic_germ_trivial_source_factorization]:
    the scalar factorization base case in 3.4.7, p. 325. *)
Theorem holomorphic_germ_trivial_source_factorization (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a:
  (forall x:X,x = a) ->
  is_unique_factorization_commutative_domain
    [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)].
Proof.
move=>hTrivial;apply:commutative_division_ring_factorization.
exact:holomorphic_germ_trivial_source_unit hTrivial.
Qed.
