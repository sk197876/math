(** Federer (1969), 2.5.3, proof p. 95: estimates for differences of finite
    measurable sets, from the splitting definition in 2.1.2, p. 54. The
    supporting lemma below proves finiteness before converting to real
    subtraction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measurable_difference_value]: finite subtraction
    identity used in Federer 2.5.3, proof p. 95 Only the removed set A must
    be measurable for this supporting identity. *)
Lemma finite_measurable_difference_value (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (V A : set X) :
  measure_measurable mu A -> A `<=` V -> mu V < +oo ->
  mu (V `\` A)=(fine (mu V)-fine (mu A))%R%:E.
Proof.
move=> hA hAV hV.
have hVfin : mu V \is a fin_num by rewrite ge0_fin_numE //; exact: (@measure_nonnegative R X mu hm V).
have hAfin : mu A \is a fin_num.
  rewrite ge0_fin_numE; last exact: (@measure_nonnegative R X mu hm A).
  exact: le_lt_trans (@measure_mono R X mu hm A V hAV) hV.
have hDV : V `\` A `<=` V by move=> x [hx _].
have hDfin : mu (V `\` A) \is a fin_num.
  rewrite ge0_fin_numE; last exact: (@measure_nonnegative R X mu hm (V `\` A)).
  exact: le_lt_trans (@measure_mono R X mu hm _ V hDV) hV.
have hI : V `&` A=A.
  apply/seteqP; split=> x; first by move=> [_ hx].
  move=> hx; split=> //; exact: hAV x hx.
have hsplit := hA V.
rewrite hI -(fineK hVfin) -(fineK hAfin) -(fineK hDfin) -EFinD in hsplit.
have he : fine (mu V)=(fine (mu A)+fine (mu (V `\` A)))%R by injection hsplit.
by rewrite -(fineK hDfin) he addrAC subrr add0r.
Qed.
