(** Federer (1969), 3.4.12, p. 339, extending 3.4.5,
    p. 320: the zero germ of each original holomorphic
    function is a holomorphic variety germ. Finite systems
    remain finite systems; no complex sum-of-squares reduction is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import HolomorphicUP NormAnalyticLocal RealNormUP ScalarRestriction ComplexScalarSealed NormMetric NormAnalyticDomain
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRingLaws
  SetGermUP SetGermLocality FiniteHolomorphicVarietyUP HolomorphicVarietyGermUP HolomorphicZeroGermSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_zero_germ_is_variety]: one actual
    holomorphic equation defines a variety germ, 3.4.12, p. 339. *)
Lemma holomorphic_zero_germ_is_variety (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a
    (alpha:holomorphic_germ_space hNX a):
  @is_holomorphic_variety_germ R X NX hNX a (@HolomorphicZeroGerm.value R X NX hNX a alpha).
Proof.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
have [U [ha hHol]]:=holomorphic_representative_holomorphic f.
have hU:@open T U:=norm_analytic_domain_open hHol.1.
pose S:set X:=U `&` [set x|holomorphic_representative_value f x=0].
exists U,S;split;first exact:ha.
split.
- split;first exact:hU.
  exists (Finite.clone 'I_1 _),(fun _=>holomorphic_representative_value f);split;first by move=>_.
  move=>x;split.
  + move=>[hx hz];split;first exact:hx.
    by move=>_.
  + move=>[hx hz];split;first exact:hx.
    exact:hz ord0.
- rewrite /S (@set_germ_neighbourhood_intersection T a U [set x|holomorphic_representative_value f x=0] hU ha).
  exact:(@HolomorphicZeroGerm.laws R X NX hNX a alpha f hf).
Qed.
