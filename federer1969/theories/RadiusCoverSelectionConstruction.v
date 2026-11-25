(** Private existence proof for Federer (1969), 2.8.10, p. 147. Follow the
    printed class D, closure under chain unions, a maximal member, and
    insertion of a remaining pair with sufficiently large radius. The only
    external selection principle is the general set-theoretic Zorn
    background already used in this project. No covering theorem is
    imported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RadiusCoverSelectionUP RadiusSaturationLaws StrictLargeMember.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [maximal_radius_saturated_family_exists]: the
    maximal member of D in Federer 2.8.10, p. 147.
    The chain-union law supplies the hypothesis of the general
    maximal principle; no radius bounds are needed at this stage. *)
Theorem maximal_radius_saturated_family_exists (R : realType) (X : metricType R)
    (tau : R) (Q : set (X * R)) :
  exists P, is_radius_saturated_family tau Q P /\
    forall S, is_radius_saturated_family tau Q S -> P `<=` S -> S `<=` P.
Proof.
pose D P := is_radius_saturated_family tau Q P.
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
  have hs P : E P -> is_radius_saturated_family tau Q P.
    by move=> [a ha <-]; exact: svalP a.
  have hcomp P S : E P -> E S -> P `<=` S \/ S `<=` P.
    move=> [a ha <-] [b hb <-].
    have [/asboolP hab|/asboolP hba] := hc a b ha hb; by [left|right].
  pose U := \bigcup_(P in E) P.
  have hU : D U := @chain_union_radius_saturated R X tau Q E hs hcomp.
  exists (exist D U hU)=> a ha; apply/asboolP=> p hp.
  exists (sval a); last exact hp.
  by exists a.
have [a hmax] := @Zorn T rel hrefl htrans hanti hchain.
exists (sval a); split; first exact: svalP a.
move=> S hS hPS; pose b : T := exist D S hS.
have hab : rel a b by apply/asboolP.
have he := hmax b hab; change (sval b `<=` sval a); by rewrite he.
Qed.

(** Source for [radius_cover_selection_exists]: the complete
    existence conclusion of Federer 2.8.10, p. 147.
    A remaining pair would allow insertion of a radius t
    with tau*t strictly above all remaining radii, contradicting
    maximality. Both printed inequalities are strict where
    Federer makes them strict. Empty Q is permitted. *)
Theorem radius_cover_selection_exists (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X * R)) :
  1 < tau -> 0 < mu -> is_bounded_positive_radius_family mu Q ->
  exists P, is_radius_cover_selection tau Q P.
Proof.
move=> ht hmu hQ.
have [P [hP hmax]] := @maximal_radius_saturated_family_exists R X tau Q.
have ht0 : 0 < tau := lt_trans ltr01 ht.
exists P; constructor.
- exact: radius_saturated_members hP.
- exact: radius_saturated_separated hP.
- move=> q hq.
  case: (pselect (exists p, P p /\ mdist q.1 p.1 <= q.2+p.2))=> [[p [hp hnear]]|hn].
  * exact (@radius_saturated_controls_nearby R X tau Q P hP q p hq hp hnear).
  * pose K := [set k : X * R | Q k /\ forall p, P p -> k.2+p.2 < mdist k.1 p.1].
    have hqK : K q.
      split=> // p hp; rewrite ltNge; apply/negP=> hnear; apply: hn; by exists p.
    have hpos k (hk : K k) : 0 < k.2 := (andP (hQ k hk.1)).1.
    have hbounded : exists C, forall k, K k -> k.2 <= C.
      exists mu=> k hk; exact: ltW (andP (hQ k hk.1)).2.
    have [w [hw hlarge]] := @bounded_positive_strict_large_member R
      [the choiceType of (X * R)%type] K (fun k => k.2) tau
      (ex_intro _ q hqK) hpos hbounded ht.
    have hi : is_radius_saturated_family tau Q (P `|` [set w]).
      apply: (@radius_saturated_insert_large_remaining R X tau Q P w hP hw.1 hw.2).
      move=> k hk hsep; rewrite ltr_pdivrMr // mulrC.
      exact: hlarge k (conj hk hsep).
    have hsub : P `<=` P `|` [set w] by move=> p hp; left.
    have hwP : P w := hmax _ hi hsub w (or_intror (erefl _)).
    have hsep := hw.2 w hwP.
    have hbad := lt_trans (addr_gt0 (hpos w hw) (hpos w hw)) hsep.
    by rewrite mdistxx ltxx in hbad.
Qed.
