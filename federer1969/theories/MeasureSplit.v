(** Federer (1969), 2.1.2, pp. 53-54. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSumBoolean MeasureUP MeasureIndexedCover MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_binary_cover]: Federer 2.1.2,
    pp. 53-54, supporting two-set case of the defining cover inequality. *)
Lemma measure_binary_cover (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (T A B : set I) :
  T `<=` A `|` B -> mu T <= mu A + mu B.
Proof.
move=> hc.
have hcover : T `<=` \bigcup_(b in @setT bool) (if b then A else B).
  move=> x hx; case: (hc x hx)=> hxAB.
  - by exists true.
  - by exists false.
have h := @measure_indexed_cover R I _ mu hm T setT
  (fun b : bool => if b then A else B) (finite_set_countable (@finite_finset _ (@setT bool))) hcover.
rewrite nonnegative_sum_bool in h; first exact h.
by move=> []; exact: (@measure_nonnegative R I mu hm).
Qed.

(** Source for [measure_split_upper]: Federer 2.1.2, p. 54, sentence after
    the measurability definition: the test-set measure never exceeds the sum
    of the two parts. the present statement follows Federer. *)
Lemma measure_split_upper (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (T A : set I) :
  mu T <= mu (T `&` A) + mu (T `\` A).
Proof.
apply: (@measure_binary_cover R I mu hm T (T `&` A) (T `\` A))=> x hx.
case: (pselect (A x))=> ha; [left | right]; by split.
Qed.

(** Source for [measure_measurable_finite_test]: Federer 2.1.2, p. 54,
    second display; it suffices to prove the reverse splitting inequality
    for tests of measure less than infinity. *)
Lemma measure_measurable_finite_test (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (A : set I) :
  measure_measurable mu A <->
  (forall T, mu T < +oo -> mu (T `&` A) + mu (T `\` A) <= mu T).
Proof.
split=> h.
- by move=> T _; rewrite -(h T).
- move=> T; apply/eqP; rewrite eq_le (measure_split_upper hm) /=.
  case: (ltP (mu T) +oo)=> ht; first exact: h.
  have he : mu T = +oo by apply/eqP; rewrite eq_le leey ht.
  by rewrite he leey.
Qed.

(** Source for [measure_measurable_empty]: Federer 2.1.2, p. 54, paragraph
    after counting measure; the empty set is measurable. *)
Lemma measure_measurable_empty (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) :
  measure_measurable mu set0.
Proof. by move=> T; rewrite setI0 setD0 (measure_empty hm) add0e. Qed.

(** Source for [measure_measurable_whole]: Federer 2.1.2, p. 54, same
    paragraph; the whole space is measurable. *)
Lemma measure_measurable_whole (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) :
  measure_measurable mu setT.
Proof. by move=> T; rewrite setIT setDT (measure_empty hm) adde0. Qed.
