(** Private maximal-family proof for Federer (1969), 2.8.13, pp. 149–150.
    The strict large-radius supremum argument is the book's. The
    set-theoretic maximal principle is the existing general background.
    Source context: ControlledCenterSelectionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import DirectionalLimitationUP RadiusCoverSelectionUP
  ControlledCenterSelectionUP ControlledCenterSaturationLaws StrictLargeMember.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [maximal_center_saturated_family_exists]: the
    maximal member of the class D in Federer 2.8.13, p. 149.
    Chain unions supply the general maximal principle's hypothesis;
    the eligible family need not be countable or nonempty. *)
Theorem maximal_center_saturated_family_exists (R : realType) (X : metricType R)
    (tau : R) (Q : set (X * R)) :
  1 < tau -> exists P, is_center_saturated_family tau Q P /\
    forall S, is_center_saturated_family tau Q S -> P `<=` S -> S `<=` P.
Proof.
move=> ht.
pose D P := is_center_saturated_family tau Q P.
pose T := {P : set (X * R) | D P}.
pose rel (a b : T) := `[< sval a `<=` sval b >].
have hrefl a : rel a a by apply/asboolP.
have htrans a b c : rel a b -> rel b c -> rel a c.
  move=> /asboolP hab /asboolP hbc; apply/asboolP=> p hp; exact: hbc (hab p hp).
have hanti a b : rel a b -> rel b a -> a = b.
  move=> /asboolP hab /asboolP hba; case: a hab hba=> a ha; case: b=> b hb hab hba.
  apply: eq_exist; apply/seteqP; by split.
have hchain (C : set T) : total_on C rel -> exists b, forall a, C a -> rel a b.
  move=> hc.
  pose E := sval @` C.
  have hs P : E P -> is_center_saturated_family tau Q P.
    by move=> [a ha <-]; exact: svalP a.
  have hcomp P S : E P -> E S -> P `<=` S \/ S `<=` P.
    move=> [a ha <-] [b hb <-].
    have [/asboolP hab|/asboolP hba] := hc a b ha hb; by [left|right].
  pose U := \bigcup_(P in E) P.
  have hU : D U := @chain_union_center_saturated R X tau Q E ht hs hcomp.
  exists (exist D U hU)=> a ha; apply/asboolP=> p hp.
  exists (sval a); last exact hp.
  by exists a.
have [a hmax] := @Zorn T rel hrefl htrans hanti hchain.
exists (sval a); split; first exact: svalP a.
move=> S hS hPS; pose b : T := exist D S hS.
have hab : rel a b by apply/asboolP.
have he := hmax b hab; change (sval b `<=` sval a); by rewrite he.
Qed.

(** Source for [controlled_center_selection_exists]: the
    conclusion of Federer 2.8.13, pp. 149–150. An uncovered
    center would allow insertion of a remaining pair with large
    enough radius, contradicting maximality. Strictness in the
    original radius comparison is preserved. *)
Theorem controlled_center_selection_exists (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X*R)) :
  1 < tau -> 0 < mu -> is_bounded_positive_radius_family mu Q ->
  exists P, is_controlled_center_selection tau Q P.
Proof.
move=> ht hm hQ.
have [P [hP hmax]] := @maximal_center_saturated_family_exists R X tau Q ht.
have ht0 : 0 < tau := lt_trans ltr01 ht.
exists P; constructor.
- exact: center_saturated_members hP.
- exact: center_saturated_controlled hP.
- move=> q hq.
  have [hc|huncov] := @center_saturated_alternative R X tau Q P hP q hq; first exact hc.
  pose K := [set k : X*R | Q k /\ forall p, P p -> p.2 < mdist p.1 k.1].
  have hqK : K q by split=> // p hp; exact: (huncov p hp).1.
  have hpos k (hk : K k) : 0 < k.2 := (andP (hQ k hk.1)).1.
  have hbound : exists C, forall k, K k -> k.2 <= C.
    exists mu=> k hk; exact: ltW (andP (hQ k hk.1)).2.
  have [w [hw hlarge]] := @bounded_positive_strict_large_member R
    [the choiceType of (X*R)%type] K (fun k => k.2) tau
    (ex_intro _ q hqK) hpos hbound ht.
  have hi : is_center_saturated_family tau Q (P `|` [set w]).
    apply: (@center_saturated_insert_large_remaining R X tau Q P w hP hw.1 (hpos w hw) hw.2).
    move=> k hk hun; rewrite ltr_pdivrMr // mulrC.
    exact: hlarge k (conj hk hun).
  have hsub : P `<=` P `|` [set w] by move=> p hp; left.
  have hwP : P w := hmax _ hi hsub w (or_intror (erefl _)).
  have hbad := lt_trans (hpos w hw) (hw.2 w hwP).
  by rewrite mdistxx ltxx in hbad.
Qed.
