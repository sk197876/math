(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: a
    finite transverse polynomial is the sum of its
    actual analytic term germs. This supporting finite-sum
    proof uses the opaque ring's representative equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicGermArithmeticRepresentatives RealNormUP HolomorphicGermRepresentatives HolomorphicGermOperationsUP HolomorphicGermUP
  HolomorphicGermSealed HolomorphicGermRingLaws HolomorphicGermRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_finite_sum_representative]:
    actual finite analytic sums represent the corresponding
    germ sums, supporting the remainder module in 3.4.7,
    p. 325. All selected representatives remain local. *)
Theorem holomorphic_finite_sum_representative (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a
    (F:seq (@holomorphic_representative_type R X NX hNX a)):
  exists f:@holomorphic_representative_type R X NX hNX a,
    (forall x,holomorphic_representative_value f x =
      \sum_(g<-F) holomorphic_representative_value g x) /\
    (holomorphic_germ f:@holomorphic_germ_ring R X NX hNX a) =
      \sum_(g<-F) (holomorphic_germ g:@holomorphic_germ_ring R X NX hNX a).
Proof.
elim:F=>[|g F [f [hValues hGerm]]].
- exists (@holomorphic_constant_representative R X NX hNX a 0);split.
  + move=>x;by rewrite big_nil.
  + by rewrite big_nil.
- exists (@holomorphic_add_representatives R X NX hNX a g f);split.
  + move=>x;rewrite big_cons.
    change (holomorphic_representative_value g x+holomorphic_representative_value f x =
      holomorphic_representative_value g x+\sum_(h<-F) holomorphic_representative_value h x).
    by rewrite hValues.
  + rewrite big_cons.
    rewrite -(@holomorphic_germ_add_equation _ _ _ _ _ _ _ _ (@HolomorphicGerms.laws R X NX hNX a)).
    change ((holomorphic_germ g:@holomorphic_germ_ring R X NX hNX a)+holomorphic_germ f =
      (holomorphic_germ g:@holomorphic_germ_ring R X NX hNX a)+
        \sum_(h<-F) (holomorphic_germ h:@holomorphic_germ_ring R X NX hNX a)).
    by rewrite hGerm.
Qed.

(** Source for [holomorphic_germ_finite_sum_equation]: the
    germ of a given finite sum is its ring
    sum, supporting 3.4.7, p. 325. The equation
    uses the original representative of that sum. *)
Lemma holomorphic_germ_finite_sum_equation (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a
    (F:seq (@holomorphic_representative_type R X NX hNX a))
    (g:@holomorphic_representative_type R X NX hNX a):
  (forall x,holomorphic_representative_value g x =
    \sum_(f<-F) holomorphic_representative_value f x) ->
  (holomorphic_germ g:@holomorphic_germ_ring R X NX hNX a) =
    \sum_(f<-F) (holomorphic_germ f:@holomorphic_germ_ring R X NX hNX a).
Proof.
move=>h;have [f [hf hGerm]]:=@holomorphic_finite_sum_representative R X NX hNX a F.
have hEqual:holomorphic_germ g = holomorphic_germ f.
  apply:holomorphic_germ_pointwise_equality=>x;by rewrite h hf.
by rewrite hEqual hGerm.
Qed.
