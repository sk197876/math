(** Federer (1969), 3.4.5, p. 319: the germ
    map induced by analytic composition is contravariantly
    compatible with actual composition and the identity map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormAnalyticUP NormAnalyticComposition AnalyticGermUP
  AnalyticGermRepresentatives AnalyticGermRingLaws
  AnalyticPullbackRepresentative AnalyticPullbackUP AnalyticPullbackSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_germ_pullback_identity]: the
    original representative equation gives the identity on germs,
    implicit in 3.4.5, p. 319. *)
Theorem analytic_germ_pullback_identity (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:set X) a
    (hId:@norm_analytic_at R X X NX NX hNX hNX A (fun x=>x) a)
    (alpha:analytic_germ_space hNX a):
  @AnalyticPullback.map R X X NX NX hNX hNX A (fun x=>x) a hId alpha=alpha.
Proof.
have [f <-]:=@analytic_germ_has_representative R X NX hNX a alpha.
rewrite (@AnalyticPullback.laws R X X NX NX hNX hNX A (fun x=>x) a hId).
apply:analytic_germ_pointwise_equality=>x;reflexivity.
Qed.

(** Source for [analytic_germ_pullback_composition]: the
    pullback of a composite is the composite of the two
    original germ maps, following their displayed representative
    equation in 3.4.5, p. 319. *)
Theorem analytic_germ_pullback_composition (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (A:set X) (B:set Y) (u:X->Y) (v:Y->Z) a
    (hu:@norm_analytic_at R X Y NX NY hNX hNY A u a)
    (hv:@norm_analytic_at R Y Z NY NZ hNY hNZ B v (u a))
    (alpha:analytic_germ_space hNZ (v (u a))):
  @AnalyticPullback.map R X Z NX NZ hNX hNZ (fun x=>A x /\ B (u x))
    (fun x=>v (u x)) a (norm_analytic_at_composition hu hv) alpha=
  @AnalyticPullback.map R X Y NX NY hNX hNY A u a hu
    (@AnalyticPullback.map R Y Z NY NZ hNY hNZ B v (u a) hv alpha).
Proof.
have [f <-]:=@analytic_germ_has_representative R Z NZ hNZ (v (u a)) alpha.
rewrite (@AnalyticPullback.laws R X Z NX NZ hNX hNZ _ _ a _)
  (@AnalyticPullback.laws R Y Z NY NZ hNY hNZ B v (u a) hv)
  (@AnalyticPullback.laws R X Y NX NY hNX hNY A u a hu).
apply:analytic_germ_pointwise_equality=>x;reflexivity.
Qed.
