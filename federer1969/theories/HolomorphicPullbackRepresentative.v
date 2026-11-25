(** Federer (1969), 3.4.12, p. 339, extending 3.4.5,
    p. 319: actual holomorphic composition induces original
    representatives and preserves their local equality. Reuse the
    chain rule and the existing real continuity theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  NormMetric NormRegularity NormClassZeroTopology NormAnalyticLocal NormAnalyticOperations
  LocalGermUP HolomorphicUP HolomorphicAtUP HolomorphicComposition HolomorphicGermRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section Composition.
Variable R:realType.
Variables X Y:lmodType (ComplexScalars.C R).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Variables (NX:XR->R) (NY:YR->R).
Variables (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Variable A:set X.
Variable u:X->Y.
Variable a:X.
Variable hu:@is_holomorphic_at R X Y NX NY hNX hNY A u a.
Local Notation C:=(ComplexScalars.C R).

(** Source for [holomorphic_pullback_representative_holomorphic]: the
    actual composite is holomorphic near its original centre,
    extending the representative equation of 3.4.5, p. 319. *)
Lemma holomorphic_pullback_representative_holomorphic
    (f:@holomorphic_representative_type R Y NY hNY (u a)):
  exists U:set X,U a /\is_holomorphic hNX (@complex_modulus_real_norm R) U
    (fun x=>holomorphic_representative_value f (u x)).
Proof.
have [U [haU [_ hU]]]:=hu.
have [V [haV hV]]:=holomorphic_representative_holomorphic f.
exists (fun x=>U x /\V (u x));split;first by split.
exact:holomorphic_composition hU hV.
Qed.

(** Source for [holomorphic_pullback_representative]: the actual
    function composed with u, extending 3.4.5, p. 319. *)
Definition holomorphic_pullback_representative
    (f:@holomorphic_representative_type R Y NY hNY (u a)):
    @holomorphic_representative_type R X NX hNX a:=
  exist _ (fun x=>holomorphic_representative_value f (u x))
    (holomorphic_pullback_representative_holomorphic f).

(** Source for [holomorphic_pullback_preserves_local_equality]: actual
    continuity pulls a target neighbourhood back to a source
    neighbourhood, so the map depends only on the original
    germ, extending 3.4.5, p. 319. *)
Lemma holomorphic_pullback_preserves_local_equality
    (f g:@holomorphic_representative_type R Y NY hNY (u a)):
  @locally_equal_at (Topological.clone (real_norm_metric_space hNY) _) C (u a)
    (holomorphic_representative_value f) (holomorphic_representative_value g) ->
  @locally_equal_at (Topological.clone (real_norm_metric_space hNX) _) C a
    (holomorphic_representative_value (holomorphic_pullback_representative f))
    (holomorphic_representative_value (holomorphic_pullback_representative g)).
Proof.
move=>[V [hV [hVa hEq]]].
have [U [hUa [_ hU]]]:=hu.
have hClass:=norm_class_continuous (norm_analytic_class_all_orders hU.1 0%N).
have hNear:=@norm_class_zero_continuous_at R XR YR NX NY hNX hNY U u a hClass hUa V
  (open_nbhs_nbhs (conj hV hVa)).
change (nbhs (a:real_norm_metric_space hNX) (fun x=>V (u x))) in hNear.
rewrite nbhsE in hNear.
have [W [hW hWa] hWV]:=hNear.
exists W;split;first exact:hW.
split;first exact:hWa.
move=>x hx;exact:hEq (u x) (hWV x hx).
Qed.
End Composition.
