(** Federer (1969), 2.3.8, p. 78: null changes do not affect the
    pseudodistance. Supporting consequences of the measure axioms in 2.1.2,
    p. 53. Source context: MeasureGauge.v. No measurability of the modified
    sets is assumed in these numerical identities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureSplit
  MeasureAlmostUP MeasureAlmostBasic MeasureGauge MeasureGaugeComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_null_modification_value]: supporting
    numerical null-invariance for Federer 2.3.8, p. 78,
    derived from the two binary-cover inequalities. *)
Lemma measure_null_modification_value (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A B E : set X) :
  mu E = 0 -> (forall x, ~ E x -> (A x <-> B x)) -> mu A = mu B.
Proof.
move=> he hab.
have hAB : A `<=` B `|` E.
  move=> x hx; case: (pselect (E x))=> hE; first by right.
  left; exact: (proj1 (hab x hE) hx).
have hBA : B `<=` A `|` E.
  move=> x hx; case: (pselect (E x))=> hE; first by right.
  left; exact: (proj2 (hab x hE) hx).
have h1 := @measure_binary_cover R X mu hm A B E hAB.
have h2 := @measure_binary_cover R X mu hm B A E hBA.
rewrite he adde0 in h1.
rewrite he adde0 in h2.
apply/eqP; by rewrite eq_le h1 h2.
Qed.

(** Source for [almost_equal_preimage_measure]: supporting inverse-
    image measure invariance for the almost-equality interpretation
    in Federer 2.3.8, p. 78. Partial domains may differ on
    a null set. *)
Lemma almost_equal_preimage_measure (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X Y) (A : set Y) :
  measure_almost_equal mu f g ->
  mu (partial_function_preimage f A) = mu (partial_function_preimage g A).
Proof.
move=> he; apply: (@measure_null_modification_value R X mu hm
  _ _ (~` partial_function_agreement f g) he).
move=> x hn; have [y [hy hz]] : partial_function_agreement f g x.
  by apply: contrapT=> h; exact: hn.
split=> [[z [hgz hA]]|[z [hgz hA]]]; exists z; split=> //.
- have e := partial_function_single_valued hy hgz; by rewrite -e.
- have e := partial_function_single_valued hz hgz; by rewrite -e.
Qed.

(** Source for [measure_gauge_almost_invariance]: supporting
    almost-equality invariance of the gauge in Federer 2.3.8,
    p. 78; unlike a norm on pointwise functions, it ignores
    null modifications. *)
Lemma measure_gauge_almost_invariance (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : Y -> R)
    (f g : partial_function X Y) :
  measure_almost_equal mu f g -> measure_gauge mu N f = measure_gauge mu N g.
Proof.
move=> he; apply: measure_gauge_superlevel_invariance=> r.
exact (@almost_equal_preimage_measure R X Y mu hm f g [set y | r < (N y)%:E] he).
Qed.
