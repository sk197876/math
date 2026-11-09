(** Federer (1969), 3.3.16, p. 299: original countably
    rectifiable carriers have Borel countably rectifiable enlargements. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RectifiableSetUP RectifiableElementary RectifiableClosure CountablyRectifiableUnions
  TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countably_rectifiable_closed_family_enlargement]:
    supporting carrier assembly for Federer 3.3.16, p. 299, from
    the closure assertion in 3.2.14, p. 252. Closing each original
    bounded Lipschitz image gives a countable family of closed
    rectifiable sets containing the unchanged original carrier. *)
Lemma countably_rectifiable_closed_family_enlargement (R:realType) (X:metricType R) m (S:set X):
  is_countably_m_rectifiable m S ->exists G:set (set X),countable G /\
    (forall F,G F ->closed F /\is_m_rectifiable m F) /\S `<=` \bigcup_(F in G) F.
Proof.
move=>[C [hC [hRect hUnion]]].
exists (closure @` C); split; first exact:sub_countable (card_image_le _ _) hC.
split.
- move=>F [A hA <-]; split; [exact:closed_closure|exact:rectifiable_closure (hRect A hA)].
- move=>x hx; rewrite hUnion in hx; have [A hA hAx]:=hx.
  exists (closure A); first by exists A.
  exact:subset_closure hAx.
Qed.

(** Source for [countably_rectifiable_borel_enlargement]:
    supporting Borel carrier for Federer 3.3.16, p. 299. The
    countable closed family gives a Borel countably rectifiable
    superset. No equality or nullity of its added points is claimed. *)
Lemma countably_rectifiable_borel_enlargement (R:realType) (X:metricType R) m (S:set X):
  is_countably_m_rectifiable m S ->exists U,S `<=` U /\borel_set U /\is_countably_m_rectifiable m U.
Proof.
move=>hS.
have [G [hG [hClosed hCover]]]:=countably_rectifiable_closed_family_enlargement hS.
exists (\bigcup_(F in G) F); split; first exact:hCover.
split.
- apply:borel_set_countable_union hG _=>F hF; exact:closed_borel_set (hClosed F hF).1.
- apply:countably_rectifiable_countable_union hG _=>F hF.
  exact:RectifiableElementary.rectifiable_countably_rectifiable (hClosed F hF).2.
Qed.
