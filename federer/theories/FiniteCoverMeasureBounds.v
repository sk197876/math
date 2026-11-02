(** Finite covering estimate in Federer (1969), 2.8.15, p. 150: summing the
    measures of the intersections with 2 zeta+1 color unions bounds the
    target measure, so one intersection has at least the corresponding
    average measure. These are supporting finite-sum and order lemmas, not
    extra measure axioms. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum MeasureUP MeasureIndexedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_type_nonnegative_sum]: supporting finite
    sum notation in the displayed estimate of Federer 2.8.15,
    p. 150. The existing abstract nonnegative sum agrees with
    ordinary finite addition, also for an empty finite index type. *)
Lemma finite_type_nonnegative_sum (R : realType) (I : finType) (f : I -> \bar R) :
  (forall i, (0 <= f i)%E) -> nonnegative_sum setT f = (\sum_i f i)%E.
Proof.
move=> hf.
pose B : {fset I} := [fset i in enum I]%fset.
have hT : @setT I = [set i | i \in B].
  by apply/seteqP; split=> i hi //; rewrite /= /B in_fset mem_enum.
rewrite hT nonnegative_sum_finite; last by move=> i _; exact: hf.
have hp : perm_eq (B : seq I) (enum I).
  apply: uniq_perm; [exact: fset_uniq|exact: enum_uniq|].
  by move=> i; rewrite /B in_fset.
rewrite -big_enum; exact: perm_big hp.
Qed.

(** Source for [measure_finite_indexed_cover]: the finite covering
    inequality in Federer 2.8.15, p. 150 No measurability of the target or
    covering pieces is needed for this bound. *)
Lemma measure_finite_indexed_cover (R : realType) (X : choiceType)
    (I : finType) (mu : set X -> \bar R) (hm : is_measure mu)
    (T : set X) (U : I -> set X) :
  T `<=` \bigcup_(i in @setT I) U i -> (mu T <= \sum_i mu (U i))%E.
Proof.
move=> hc.
have h := @measure_indexed_cover R X I mu hm T setT U
  (finite_set_countable (@finite_finset _ (@setT I))) hc.
have hn i : (0 <= mu (U i))%E := @measure_nonnegative R X mu hm (U i).
by rewrite (@finite_type_nonnegative_sum R I (fun i => mu (U i)) hn) in h.
Qed.

(** Source for [finite_real_cover_average_piece]: the choice of an index
    with measure at least the average in Federer 2.8.15, p. 150 This scalar
    supporting lemma needs only a positive finite index size and the sum
    bound. *)
Lemma finite_real_cover_average_piece (R : realType) (N : nat)
    (p : 'I_N -> R) (t : R) : (0 < N)%N -> t <= \sum_i p i ->
  exists i, t <= N%:R * p i.
Proof.
move=> hN ht.
have hNr : (0 < N%:R :> R) by rewrite ltr0n.
have hN0 : (N%:R != 0 :> R) := lt0r_neq0 hNr.
apply: contrapT=> hn.
have hlt i : p i < t/N%:R.
  rewrite ltr_pdivlMr // mulrC ltNge; apply/negP=> hle; apply: hn; by exists i.
have hhas : has predT (enum 'I_N).
  apply/hasP; exists (@Ordinal N 0 hN); by rewrite ?mem_enum.
have hs : \sum_i p i < \sum_(i : 'I_N) t/N%:R.
  rewrite -!big_enum; exact: ltr_sum hhas (fun i _ => hlt i).
rewrite sumr_const card_ord -[(t/N%:R) *+ N]mulr_natr divfK // in hs.
by have := le_lt_trans ht hs; rewrite ltxx.
Qed.
