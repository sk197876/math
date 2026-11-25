(** Federer (1969), 2.6.7, printed p. 121: the section measures f(y)-f(a)
    and g(b)-g(x) are differences of finite measures of nested half-lines.
    This supporting lemma uses the measurable splitting law of 2.1.2, p. 54. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal ring.
From Federer Require Import MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_nested_difference]: finite
    subtraction used in the two section computations of Federer
    2.6.7, p. 121. Only the smaller set must be measurable;
    both given measure values are finite real numbers. *)
Lemma finite_measure_nested_difference (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (A B : set X) (a b : R) :
  measure_measurable mu A -> A `<=` B -> mu A=a%:E -> mu B=b%:E ->
  mu (B `\` A)=(b-a)%R%:E.
Proof.
move=> hA hAB ha hb.
have hfin : mu (B `\` A) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  have hsub : B `\` A `<=` B by move=> x [hx _].
  have hle := @measure_mono R X mu hm _ B hsub.
  rewrite hb in hle; exact: le_lt_trans hle (ltry b).
have hs := hA B; rewrite (setIidr hAB) ha hb in hs.
have hh := congr1 fine hs; rewrite fineD // in hh.
change (b=(a+fine (mu (B `\` A)))%R) in hh.
have hd : fine (mu (B `\` A))=(b-a)%R by rewrite hh; ring.
by rewrite -(fineK hfin) hd.
Qed.
