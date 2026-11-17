(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: assuming
    the original centre is zero loses no generality.
    An actual analytic left inverse makes the induced
    pullback surjective. Translation supplies this inverse;
    no arbitrary function on germs is assumed analytic. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicUP HolomorphicAtUP HolomorphicComposition RealNormUP NormAnalyticUP NormAnalyticComposition
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRingLaws HolomorphicGermRing
  HolomorphicPullbackRepresentative HolomorphicPullbackSealed HolomorphicPullbackRingMorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_ring_pullback_surjective_left_inverse]:
    translation of the original analytic germs in
    3.4.7, p. 325. An actual analytic left
    inverse supplies a preimage of every original
    germ, through its actual analytic representative. *)
Theorem holomorphic_ring_pullback_surjective_left_inverse (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (A:set X) (B:set Y) (u:X->Y) (v:Y->X) a
    (hu:@is_holomorphic_at R X Y NX NY hNX hNY A u a)
    (hv:@is_holomorphic_at R Y X NY NX hNY hNX B v (u a)):
  (forall x,v (u x) = x) ->
  forall alpha:@holomorphic_germ_ring R X NX hNX a,
    exists beta:@holomorphic_germ_ring R Y NY hNY (u a),
      @holomorphic_germ_ring_pullback R X Y NX NY hNX hNY A u a hu beta = alpha.
Proof.
move=>hInverse alpha.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
have [U [haU hF]]:=holomorphic_representative_holomorphic f.
have [V [haV [_ hV]]]:=hv.
have hComposite:=holomorphic_composition hV hF.
have hCentre:(fun y=>V y /\U (v y)) (u a) by split;last by rewrite hInverse.
have [g hG]:=@holomorphic_representative_from_domain R Y NY hNY (u a)
  (fun y=>V y /\U (v y)) (fun y=>holomorphic_representative_value f (v y)) hCentre hComposite.
exists (holomorphic_germ g).
change (@HolomorphicPullback.map R X Y NX NY hNX hNY A u a hu (holomorphic_germ g) = alpha).
rewrite (@HolomorphicPullback.laws R X Y NX NY hNX hNY A u a hu) -hf.
apply:holomorphic_germ_pointwise_equality=>x.
change (holomorphic_representative_value g (u x) = holomorphic_representative_value f x).
by rewrite hG hInverse.
Qed.
