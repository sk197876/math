(** Consequences of the open-cost specifications supporting Federer (1969),
    2.5.14, pp. 107–108. These consequences do not depend on an
    implementation of the envelope. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import OpenCoverContentUP NonnegativeSum NonnegativeSumSupport ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [open_cover_content_mono]: monotonicity of alpha on open
    sets, supporting the assertion Phi(V)=alpha(V) in Federer 2.5.14, p. 107
    It follows from a singleton open cover. *)
Lemma open_cover_content_mono (R : realType) (X : topologicalType)
    (a : set X -> \bar R) (ha : is_open_cover_content a) W V :
  open W -> open V -> W `<=` V -> a W <= a V.
Proof.
move=> hW hV hWV.
have hc : W `<=` \bigcup_(U in [set V]) U by move=> x hx; exists V=> //; exact: hWV x hx.
have ho U : [set V] U -> open U by move=> ->.
have hb := @open_cover_content_cover R X a ha W [set V] hW (countable1 V) ho hc.
by rewrite nonnegative_sum_singleton // in hb; exact: (@open_cover_content_nonnegative R X a ha V hV).
Qed.

(** Source for [open_cover_envelope_open_value]: Phi(V)=alpha(V) for open V
    in Federer 2.5.14, p. 107 *)
Lemma open_cover_envelope_open_value (R : realType) (X : topologicalType)
    (a nu : set X -> \bar R) (ha : is_open_cover_content a)
    (hn : is_open_cover_envelope a nu) V : open V -> nu V=a V.
Proof.
move=> hV; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (open_cover_envelope_lower hn hV)=> x hx; exact hx.
- apply: (open_cover_envelope_greatest hn)=> W hW hVW.
  exact: (@open_cover_content_mono R X a ha V W hV hW hVW).
Qed.

(** Source for [open_cover_envelope_unique]: supporting uniqueness of the
    infimum-defined Phi in Federer 2.5.14, p. 107 *)
Lemma open_cover_envelope_unique (R : realType) (X : topologicalType)
    (a mu nu : set X -> \bar R) :
  is_open_cover_envelope a mu -> is_open_cover_envelope a nu -> forall S, mu S=nu S.
Proof.
move=> hm hn S; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (open_cover_envelope_greatest hn)=> V hV hSV; exact (@open_cover_envelope_lower R X a mu hm S V hV hSV).
- apply: (open_cover_envelope_greatest hm)=> V hV hSV; exact (@open_cover_envelope_lower R X a nu hn S V hV hSV).
Qed.

(** Source for [open_cover_envelope_infimum]: recovery of the displayed
    infimum formula for Phi(A) in Federer 2.5.14, p. 107 *)
Lemma open_cover_envelope_infimum (R : realType) (X : topologicalType)
    (a nu : set X -> \bar R) (hn : is_open_cover_envelope a nu) S :
  nu S=extended_real_inf [set c | exists V, open V /\ S `<=` V /\ c=a V].
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: extended_real_inf_greatest=> c [V [hV [hSV ->]]]; exact (@open_cover_envelope_lower R X a nu hn S V hV hSV).
- apply: (open_cover_envelope_greatest hn)=> V hV hSV; apply: extended_real_inf_lower.
  exists V; split=> //; by split.
Qed.
