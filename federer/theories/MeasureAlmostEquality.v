(** Federer (1969), 2.3.1, p. 72: almost equality of functions and its
    supporting equivalence laws. Reflexivity requires a conull domain; it is
    not asserted for an arbitrary partial function. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_almost_equal_self]: supporting precise
    reflexivity condition for Federer 2.3.1, p. 72:
    a function is almost equal to itself exactly when its domain
    contains almost all of the measured space. *)
Lemma measure_almost_equal_self (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (f : partial_function X Y) :
  measure_almost_equal mu f f <->
  measure_almost_everywhere mu (partial_function_domain f).
Proof. by rewrite /measure_almost_equal partial_function_agreement_self. Qed.

(** Source for [measure_almost_equal_sym]: supporting symmetry
    of almost equality in Federer 2.3.1, p. 72. *)
Lemma measure_almost_equal_sym (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (f g : partial_function X Y) :
  measure_almost_equal mu f g -> measure_almost_equal mu g f.
Proof. by rewrite /measure_almost_equal partial_function_agreement_sym. Qed.

(** Source for [measure_almost_equal_trans]: supporting
    transitivity of almost equality in Federer 2.3.1, p. 72;
    the two exceptional null sets are combined by subadditivity. *)
Lemma measure_almost_equal_trans (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g h : partial_function X Y) :
  measure_almost_equal mu f g -> measure_almost_equal mu g h ->
  measure_almost_equal mu f h.
Proof.
move=> hfg hgh.
exact: (@measure_almost_everywhere_mono R X mu hm _ _
  (@partial_function_agreement_trans X Y f g h)
  (measure_almost_everywhere_and hm hfg hgh)).
Qed.

(** Source for [measure_almost_equal_domain_left]: supporting domain
    consequence of the equality convention in Federer 2.3.1, p. 72 *)
Lemma measure_almost_equal_domain_left (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : partial_function X Y) :
  measure_almost_equal mu f g ->
  measure_almost_everywhere mu (partial_function_domain f).
Proof.
exact: (@measure_almost_everywhere_mono R X mu hm _ _
  (@partial_function_agreement_domain_left X Y f g)).
Qed.

(** Source for [measure_almost_equal_domains]: supporting common
    domain consequence of Federer 2.3.1, p. 72: almost equal
    functions are both defined almost everywhere. *)
Lemma measure_almost_equal_domains (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (f g : partial_function X Y) :
  measure_almost_equal mu f g ->
  measure_almost_everywhere mu (partial_function_domain f `&` partial_function_domain g).
Proof.
move=> h; apply: (@measure_almost_everywhere_and R X mu hm).
- exact (@measure_almost_equal_domain_left R X Y mu hm f g h).
- exact (@measure_almost_equal_domain_left R X Y mu hm g f
    (@measure_almost_equal_sym R X Y mu f g h)).
Qed.

(** Source for [measure_almost_equal_total]: direct equality
    formula in Federer 2.3.1, p. 72, for total maps. *)
Lemma measure_almost_equal_total (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (f g : X -> Y) :
  measure_almost_equal mu (partial_function_total f) (partial_function_total g) <->
  mu (~` [set x | f x = g x]) = 0.
Proof. by rewrite /measure_almost_equal partial_function_total_agreement. Qed.

(** Source for [measure_almost_equal_empty_self]: supporting
    empty-domain case of Federer 2.3.1, p. 72. The empty
    function is almost equal to itself exactly for a null ambient space. *)
Lemma measure_almost_equal_empty_self (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) :
  measure_almost_equal mu (@partial_function_empty X Y) (@partial_function_empty X Y)
    <-> mu setT = 0.
Proof.
by rewrite measure_almost_equal_self partial_function_empty_domain measure_almost_everywhere_false.
Qed.
