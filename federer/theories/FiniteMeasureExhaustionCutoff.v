(** Federer (1969), 3.1.4, p. 215: choose finite cutoffs whose
    complement has arbitrarily small measure inside a finite-measure
    set E. The set E itself need not be measurable, as in the book. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction
  MeasureFiniteClosure MeasureContinuityAbove ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_exhaustion_cutoff]: the first two
    measure approximations in Federer 3.1.4, p. 215. Restricting
    the outer measure to E avoids adding measurability of E; only
    the increasing approximating sets must be measurable. *)
Theorem finite_measure_exhaustion_cutoff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (E : set X) (B : nat -> set X) :
  is_measure mu -> mu E < +oo ->
  (forall p, measure_measurable mu (B p)) ->
  (forall p q, (p<=q)%N -> B p `<=` B q) ->
  mu (E `\` \bigcup_p B p)=0 ->
  forall e : R, (0<e)%R -> exists p, forall q, (p<=q)%N -> mu (E `\` B q) < e%:E.
Proof.
move=> hm hE hB hmono hnull e he.
pose nu := measure_restrict mu E.
pose C p := ~` B p.
have hnu := measure_restrict_is_measure hm E.
have hC p : measure_measurable nu (C p).
  apply: measure_restrict_measurable; exact: measure_measurable_complement (hB p).
have hCm p q : (p<=q)%N -> C q `<=` C p.
  by move=> hpq x hx hn; apply: hx; exact: hmono p q hpq x hn.
have hfin : nu (C 0%N) < +oo.
  apply: le_lt_trans _ hE; apply: (measure_mono hm)=> x [hx _]; exact hx.
have hh := (measure_continuity_above hnu hC hCm hfin).2.2.
have hid : \bigcap_p C p=~` \bigcup_p B p.
  by rewrite /C setC_bigcup.
have hzero : nu (\bigcap_p C p)=0 by rewrite hid /nu /measure_restrict -setDE hnull.
rewrite /nu in hzero.
rewrite hzero in hh.
exact: hh e%:E (ltac:(by rewrite lte_fin)).
Qed.

(** Source for [finite_common_eventual_cutoff]: the simultaneous
    choice over i=1,...,m in Federer 3.1.4, p. 215. This is a
    finite maximum argument, including the empty family. *)
Lemma finite_common_eventual_cutoff (J : finType) (P : J -> nat -> Prop) :
  (forall j, exists p, forall q, (p<=q)%N -> P j q) ->
  exists p, forall j q, (p<=q)%N -> P j q.
Proof.
move=> hP.
have hs : forall s : seq J, exists p, forall j, j \in s -> forall q, (p<=q)%N -> P j q.
  elim=> [|j s [p hp]].
  - exists 0%N; by move=> j; rewrite in_nil.
  - have [r hr] := hP j.
    exists (maxn p r)=> k; rewrite in_cons=> /orP [/eqP ->|hk] q hq.
    + apply: hr; exact: leq_trans (leq_maxr p r) hq.
    + apply: (hp k hk q); exact: leq_trans (leq_maxl p r) hq.
have [p hp] := hs (enum J).
exists p=> j q hq; apply: (hp j _ q hq); by rewrite mem_enum.
Qed.
