(** Federer (1969), 3.4.7, p. 325: a
    finite transverse polynomial is the sum of its
    actual analytic term germs. This supporting finite-sum
    proof uses the opaque ring's representative equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermSealed AnalyticGermRingLaws AnalyticGermRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_finite_sum_representative]:
    actual finite analytic sums represent the corresponding
    germ sums, supporting the remainder module in 3.4.7,
    p. 325. All selected representatives remain local. *)
Theorem analytic_finite_sum_representative (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (F:seq (@analytic_representative_type R X NX hNX a)):
  exists f:@analytic_representative_type R X NX hNX a,
    (forall x,analytic_representative_value f x =
      \sum_(g<-F) analytic_representative_value g x) /\
    (analytic_germ f:@analytic_germ_ring R X NX hNX a) =
      \sum_(g<-F) (analytic_germ g:@analytic_germ_ring R X NX hNX a).
Proof.
elim:F=>[|g F [f [hValues hGerm]]].
- exists (@analytic_constant_representative R X NX hNX a 0);split.
  + move=>x;by rewrite big_nil.
  + by rewrite big_nil.
- exists (@analytic_add_representatives R X NX hNX a g f);split.
  + move=>x;rewrite big_cons.
    change (analytic_representative_value g x+analytic_representative_value f x =
      analytic_representative_value g x+\sum_(h<-F) analytic_representative_value h x).
    by rewrite hValues.
  + rewrite big_cons.
    rewrite -(@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a)).
    change ((analytic_germ g:@analytic_germ_ring R X NX hNX a)+analytic_germ f =
      (analytic_germ g:@analytic_germ_ring R X NX hNX a)+
        \sum_(h<-F) (analytic_germ h:@analytic_germ_ring R X NX hNX a)).
    by rewrite hGerm.
Qed.

(** Source for [analytic_germ_finite_sum_equation]: the
    germ of a given finite sum is its ring
    sum, supporting 3.4.7, p. 325. The equation
    uses the original representative of that sum. *)
Lemma analytic_germ_finite_sum_equation (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (F:seq (@analytic_representative_type R X NX hNX a))
    (g:@analytic_representative_type R X NX hNX a):
  (forall x,analytic_representative_value g x =
    \sum_(f<-F) analytic_representative_value f x) ->
  (analytic_germ g:@analytic_germ_ring R X NX hNX a) =
    \sum_(f<-F) (analytic_germ f:@analytic_germ_ring R X NX hNX a).
Proof.
move=>h;have [f [hf hGerm]]:=@analytic_finite_sum_representative R X NX hNX a F.
have hEqual:analytic_germ g = analytic_germ f.
  apply:analytic_germ_pointwise_equality=>x;by rewrite h hf.
by rewrite hEqual hGerm.
Qed.
