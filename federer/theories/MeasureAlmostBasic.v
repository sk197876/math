(** Federer (1969), 2.3.1, p. 72: supporting logical rules for null
    exceptional sets, derived from the measure laws in 2.1.2, pp. 53–54.
    Countable intersections of conull truth sets support the common-domain
    argument in 2.3.2(6), pp. 73–74. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum MeasureUP MeasureBasic MeasureSplit
  MeasureIndexedCover MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_null_subset]: supporting downward closure
    of exceptional null sets in Federer 2.3.1, p. 72,
    by monotonicity from 2.1.2, p. 53. *)
Lemma measure_null_subset (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A B : set X) :
  A `<=` B -> mu B = 0 -> mu A = 0.
Proof.
move=> hAB hB; apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT -hB.
exact (@measure_mono R X mu hm A B hAB).
Qed.

(** Source for [measure_null_union]: supporting union of two
    exceptional sets for Federer 2.3.1, p. 72, by the
    covering inequality of 2.1.2, p. 53. *)
Lemma measure_null_union (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A B : set X) :
  mu A = 0 -> mu B = 0 -> mu (A `|` B) = 0.
Proof.
move=> hA hB; apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
have h := @measure_binary_cover R X mu hm (A `|` B) A B (fun x hx => hx).
by rewrite hA hB add0e in h.
Qed.

(** Source for [measure_null_countable_union]: supporting common
    exceptional set for Federer 2.3.2(6), pp. 73–74, using
    the almost convention of 2.3.1, p. 72. *)
Lemma measure_null_countable_union (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J) (N : J -> set X) :
  countable D -> (forall j, D j -> mu (N j) = 0) ->
  mu (\bigcup_(j in D) N j) = 0.
Proof.
move=> hc hn; apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
have h := @measure_indexed_cover R X J mu hm (\bigcup_(j in D) N j) D N hc
  (fun x hx => hx).
by rewrite (nonnegative_sum_zero hn) in h.
Qed.

(** Source for [measure_almost_everywhere_true]: supporting true
    statement under the convention of Federer 2.3.1, p. 72. *)
Lemma measure_almost_everywhere_true (R : realType) (X : choiceType)
    (mu : set X -> \bar R) : is_measure mu -> measure_almost_everywhere mu setT.
Proof. by move=> hm; rewrite /measure_almost_everywhere setCT (measure_empty hm). Qed.

(** Source for [measure_almost_everywhere_mono]: supporting
    implication rule for almost assertions in Federer 2.3.1, p. 72. *)
Lemma measure_almost_everywhere_mono (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (P Q : set X) :
  P `<=` Q -> measure_almost_everywhere mu P -> measure_almost_everywhere mu Q.
Proof.
move=> hPQ hP; apply: (@measure_null_subset R X mu hm (~` Q) (~` P))=> //.
by move=> x hn hp; apply: hn; exact: hPQ.
Qed.

(** Source for [measure_almost_everywhere_and]: supporting finite
    conjunction rule for Federer 2.3.1, p. 72. *)
Lemma measure_almost_everywhere_and (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (P Q : set X) :
  measure_almost_everywhere mu P -> measure_almost_everywhere mu Q ->
  measure_almost_everywhere mu (P `&` Q).
Proof.
move=> hP hQ; rewrite /measure_almost_everywhere setCI.
exact (@measure_null_union R X mu hm (~` P) (~` Q) hP hQ).
Qed.

(** Source for [measure_almost_everywhere_countable]: supporting
    countable conjunction rule for the common domain in Federer
    2.3.2(6), pp. 73–74; notation from 2.3.1, p. 72. *)
Lemma measure_almost_everywhere_countable (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set J) (P : J -> set X) :
  countable D -> (forall j, D j -> measure_almost_everywhere mu (P j)) ->
  measure_almost_everywhere mu (\bigcap_(j in D) P j).
Proof.
move=> hc hp; rewrite /measure_almost_everywhere setC_bigcap.
exact (@measure_null_countable_union R X J mu hm D (fun j => ~` P j) hc hp).
Qed.

(** Source for [measure_almost_everywhere_on_whole]: direct
    consistency of the absolute and relative conventions in
    Federer 2.3.1, p. 72, first and final displays. *)
Lemma measure_almost_everywhere_on_whole (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (P : set X) :
  measure_almost_everywhere_on mu setT P <-> measure_almost_everywhere mu P.
Proof. by rewrite /measure_almost_everywhere_on /measure_almost_everywhere setTD. Qed.

(** Source for [measure_almost_everywhere_on_implication]: supporting
    reformulation of the relative phrase in Federer 2.3.1, p. 72:
    almost all x satisfy the implication from membership in A to P. *)
Lemma measure_almost_everywhere_on_implication (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A P : set X) :
  measure_almost_everywhere_on mu A P <->
  measure_almost_everywhere mu [set x | A x -> P x].
Proof.
have he : ~` [set x | A x -> P x] = A `\` P.
  apply/seteqP; split=> x.
  - move=> hn; split.
    + apply: contrapT=> ha; apply: hn=> hx; exfalso; exact: ha hx.
    + move=> hp; apply: hn=> _; exact hp.
  - by move=> [ha hn] h; apply: hn; exact: h ha.
by rewrite /measure_almost_everywhere_on /measure_almost_everywhere he.
Qed.

(** Source for [measure_almost_contains_iff]: direct final
    convention of Federer 2.3.1, p. 72: B contains almost all of
    A exactly when membership in B holds almost everywhere on A. *)
Lemma measure_almost_contains_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (A B : set X) :
  measure_almost_included mu A B <-> measure_almost_everywhere_on mu A B.
Proof. by []. Qed.

(** Source for [measure_almost_everywhere_false]: supporting
    zero-measure boundary of Federer 2.3.1, p. 72. The almost
    predicate is not a proper filter when the whole space is null. *)
Lemma measure_almost_everywhere_false (R : realType) (X : choiceType)
    (mu : set X -> \bar R) :
  measure_almost_everywhere mu set0 <-> mu setT = 0.
Proof. by rewrite /measure_almost_everywhere setC0. Qed.
