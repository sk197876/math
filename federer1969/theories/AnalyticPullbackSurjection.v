(** Federer (1969), 3.4.7, p. 325: assuming
    the original centre is zero loses no generality.
    An actual analytic left inverse makes the induced
    pullback surjective. Translation supplies this inverse;
    no arbitrary function on germs is assumed analytic. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormAnalyticUP NormAnalyticComposition
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRingLaws AnalyticGermRing
  AnalyticPullbackRepresentative AnalyticPullbackSealed AnalyticPullbackRingMorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_ring_pullback_surjective_left_inverse]:
    translation of the original analytic germs in
    3.4.7, p. 325. An actual analytic left
    inverse supplies a preimage of every original
    germ, through its actual analytic representative. *)
Theorem analytic_ring_pullback_surjective_left_inverse (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (B:set Y) (u:X->Y) (v:Y->X) a
    (hu:@norm_analytic_at R X Y NX NY hNX hNY A u a)
    (hv:@norm_analytic_at R Y X NY NX hNY hNX B v (u a)):
  (forall x,v (u x) = x) ->
  forall alpha:@analytic_germ_ring R X NX hNX a,
    exists beta:@analytic_germ_ring R Y NY hNY (u a),
      @analytic_germ_ring_pullback R X Y NX NY hNX hNY A u a hu beta = alpha.
Proof.
move=>hInverse alpha.
have [f hf]:=@analytic_germ_has_representative R X NX hNX a alpha.
have hOuter:@norm_analytic_at R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R)
    setT (analytic_representative_value f) (v (u a)).
  rewrite hInverse;exact:analytic_representative_analytic f.
have hComposite:=@norm_analytic_at_composition R Y X R^o NY NX (fun t=>`|t|)
  hNY hNX (@scalar_absolute_value_norm R) B setT v (analytic_representative_value f)
  (u a) hv hOuter.
have [g hG]:=@analytic_representative_from_domain R Y NY hNY (u a)
  (fun y=>B y /\setT (v y)) (fun y=>analytic_representative_value f (v y)) hComposite.
exists (analytic_germ g).
change (@AnalyticPullback.map R X Y NX NY hNX hNY A u a hu (analytic_germ g) = alpha).
rewrite (@AnalyticPullback.laws R X Y NX NY hNX hNY A u a hu) -hf.
apply:analytic_germ_pointwise_equality=>x.
change (analytic_representative_value g (u x) = analytic_representative_value f x).
by rewrite hG hInverse.
Qed.
