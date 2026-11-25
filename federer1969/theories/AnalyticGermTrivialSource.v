(** Federer (1969), 3.4.7, p. 325: the
    scalar base case of the dimension induction. On
    a zero-dimensional source every germ is a constant;
    nonzero constants are actual analytic units. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermRingLaws AnalyticGermRing CommutativeFactorizationUP
  CommutativeDivisionRingNoetherian AnalyticGermUnits CommutativeIdealUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_germ_trivial_source_constant]:
    the scalar base case of 3.4.7, p. 325.
    An analytic representative on a trivial vector space
    defines its constant-value germ at the original centre. *)
Lemma analytic_germ_trivial_source_constant (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (f:@analytic_representative_type R X NX hNX a):
  (forall x:X,x = a) ->analytic_germ f =
    analytic_germ (@analytic_constant_representative R X NX hNX a
      (analytic_representative_value f a)).
Proof.
move=>hTrivial;apply:analytic_germ_pointwise_equality=>x.
change (analytic_representative_value f x = analytic_representative_value f a).
by rewrite (hTrivial x).
Qed.

(** Source for [analytic_germ_trivial_source_unit]: the
    nonzero scalar germs in the base case of 3.4.7,
    p. 325, are units. Every inverse is supplied
    by the proved actual analytic reciprocal theorem. *)
Lemma analytic_germ_trivial_source_unit (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a:
  (forall x:X,x = a) ->forall alpha:@analytic_germ_ring R X NX hNX a,
    alpha<>0 ->is_commutative_unit alpha.
Proof.
move=>hTrivial alpha hNonzero.
have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
rewrite -hf;apply:(@analytic_germ_unit_iff_nonzero_value R X NX hNX a f).2=>hValue.
apply:hNonzero;rewrite -hf (@analytic_germ_trivial_source_constant R X NX hNX a f hTrivial) hValue.
reflexivity.
Qed.

(** Source for [analytic_germ_trivial_source_noetherian]:
    the Noetherian scalar base case in 3.4.7, p. 325. *)
Theorem analytic_germ_trivial_source_noetherian (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a:
  (forall x:X,x = a) ->
  is_noetherian_commutative_ring [the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Proof.
move=>hTrivial;apply:commutative_division_ring_noetherian.
exact:analytic_germ_trivial_source_unit hTrivial.
Qed.

(** Source for [analytic_germ_trivial_source_factorization]:
    the scalar factorization base case in 3.4.7, p. 325. *)
Theorem analytic_germ_trivial_source_factorization (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a:
  (forall x:X,x = a) ->
  is_unique_factorization_commutative_domain
    [the comNzRingType of (@analytic_germ_ring R X NX hNX a)].
Proof.
move=>hTrivial;apply:commutative_division_ring_factorization.
exact:analytic_germ_trivial_source_unit hTrivial.
Qed.
