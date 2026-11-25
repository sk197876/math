(** Federer (1969), 2.1.6, p. 58: aleph zero is an Ulam number. Source
    editions and the cardinal representation convention: UlamCardinalUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum MeasureUP MeasureIndexedCover
  UlamCardinalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

(** Source for [measure_countable_null_singletons]: Federer
    2.1.6, p. 58, supporting proof of the countable case: cover
    the set by its singleton subsets and apply the measure inequality.
    Finiteness of the measure and measurability are unnecessary here. *)
Lemma measure_countable_null_singletons (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (X : set I) :
  countable X -> (forall x, X x -> mu [set x] = 0) -> mu X = 0.
Proof.
move=> hX hz; apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
have hc : X `<=` \bigcup_(x in X) [set x] by move=> x hx; exists x.
have h := @measure_indexed_cover R I I mu hm X X (fun x => [set x]) hX hc.
by rewrite (nonnegative_sum_zero hz) in h.
Qed.

(** Source for [ulam_set_countable]: Federer 2.1.6, p. 58:
    aleph zero, and therefore every smaller cardinal, is Ulam.
    The statement includes empty and finite cardinal representatives. *)
Theorem ulam_set_countable (R : realType) (J : choiceType) (D : set J) :
  countable D -> is_ulam_set R D.
Proof.
move=> hD I mu X hm hX _ _ hz.
apply: (@measure_countable_null_singletons R I mu hm X _ hz).
exact: sub_countable hX hD.
Qed.
