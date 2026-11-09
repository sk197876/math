(** Federer (1969), 3.3.20, p. 308:
    the actual four first-level corners reduce to a diagonal pair or one row/column. *)
From mathcomp Require Import all_boot.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [four_corner_hit_boolean_alternative]:
    finite supporting case distinction in the
    initial Omega reduction of 3.3.20,
    p. 308. Either opposite corners are
    both hit, or all hits lie in one
    row or one column. The four booleans
    represent actual cell-hit membership downstream. *)
Lemma four_corner_hit_boolean_alternative (a b c d:bool):
  (a&&d)||((b&&c)||((~~a&&~~b)||((~~c&&~~d)||((~~a&&~~c)||(~~b&&~~d))))).
Proof. by case:a;case:b;case:c;case:d. Qed.

(** Source for [four_corner_hit_alternative]: supporting
    original first-level case split in 3.3.20,
    p. 308. The original hit predicate
    is retained. The conclusion also holds when
    no corner, or only one corner, is hit;
    a separate first-split argument excludes those
    cases where required. *)
Lemma four_corner_hit_alternative (H:bool*bool->bool):
  (exists b d,H (b,d) /\H (negb b,negb d)) \/
  exists axis b:bool,forall p,H p ->(if axis then p.1 else p.2)=b.
Proof.
have h:=four_corner_hit_boolean_alternative (H (false,false)) (H (false,true))
  (H (true,false)) (H (true,true)).
move:h=>/orP[/andP[h00 h11]|/orP[/andP[h01 h10]|/orP[/andP[h00 h01]|/orP[/andP[h10 h11]|/orP[/andP[h00 h10]|/andP[h01 h11]]]]]].
- left;exists false,false;by split.
- left;exists false,true;by split.
- right;exists true,true;move=>[[] []] hx=>//=;
    first [by move:hx;rewrite (negPf h00)|by move:hx;rewrite (negPf h01)].
- right;exists true,false;move=>[[] []] hx=>//=;
    first [by move:hx;rewrite (negPf h10)|by move:hx;rewrite (negPf h11)].
- right;exists false,true;move=>[[] []] hx=>//=;
    first [by move:hx;rewrite (negPf h00)|by move:hx;rewrite (negPf h10)].
- right;exists false,false;move=>[[] []] hx=>//=;
    first [by move:hx;rewrite (negPf h01)|by move:hx;rewrite (negPf h11)].
Qed.
