(** Federer (1969), 3.2.14, p. 252, final
    convention: zero rectifiable sets are finite.
    Hence countably zero rectifiable means countable,
    including empty sets in arbitrary metric spaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import RectifiableSetUP RectifiableElementary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countably_zero_rectifiable_countable]:
    the countable-family consequence of Federer's
    finite-set convention, 3.2.14, p. 252. *)
Theorem countably_zero_rectifiable_countable (R : realType)
    (X : metricType R) (E : set X) :
  is_countably_m_rectifiable 0 E <-> countable E.
Proof.
split.
- move=> [C [hc [hC ->]]].
  apply: bigcup_countable hc _=> F hF; exact: finite_set_countable (hC F hF).
- move=> hE; exists ((fun x : X => [set x]) @` E); split.
  + exact: sub_countable (card_image_le _ _) hE.
  + split.
    * move=> F [x hx <-]; exact: finite_set1.
    * apply/seteqP; split=> x.
      - move=> hx; exists [set x]; first by exists x.
        reflexivity.
      - by move=> [F [y hy <-] ->].
Qed.
