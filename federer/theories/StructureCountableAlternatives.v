(** Federer (1969), 3.3.4, p. 291: the countable
    assembly of the P_v, Q_v and R_v alternatives.
    The set-theoretic inclusion uses their actual monotonicity,
    not any measurability or choice of a density witness. *)
From mathcomp Require Import all_boot all_order boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [structure_countable_alternatives_inclusion]:
    the displayed inclusion of the intersection of
    P_v union Q_v union R_v in P union Q union R,
    Federer 3.3.4, p. 291. Here P is the union
    of the P_v, Q and R the respective intersections;
    Q_v and R_v decrease with v. *)
Theorem structure_countable_alternatives_inclusion (X:Type)
    (P Q R:nat->set X):
  (forall i j,(i<=j)%N ->Q j `<=` Q i) ->
  (forall i j,(i<=j)%N ->R j `<=` R i) ->
  (\bigcap_i (P i `|` Q i `|` R i)) `<=`
    ((\bigcup_i P i) `|` (\bigcap_i Q i) `|` (\bigcap_i R i)).
Proof.
move=>hQ hR x hx.
case:(pselect ((\bigcup_i P i) x))=>hP; first by left; left.
case:(pselect ((\bigcap_i Q i) x))=>hAllQ; first by left; right.
right=>i _; apply:contrapT=>hNoR; apply:hAllQ=>j _.
apply:contrapT=>hNoQ.
have hAlt:=hx (maxn i j) I.
case:hAlt=>[[hPi|hQj]|hRi].
- apply:hP; by exists (maxn i j).
- apply:hNoQ; exact:(hQ j (maxn i j) (leq_maxr i j) x hQj).
- apply:hNoR; exact:(hR i (maxn i j) (leq_maxl i j) x hRi).
Qed.
