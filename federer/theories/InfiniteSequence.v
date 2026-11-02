(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From mathcomp.classical Require Import boolp.
From Federer Require Import AlternatingCoordinates.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.4.4, dim V=infinity: every finite
    family fails to span V. Successively adjoining an element outside
    the preceding span gives a countable independent sequence. *)
(** Source for [ordinal_snoc]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition ordinal_snoc (T : Type) n (f : 'I_n -> T) (x : T) (i : 'I_n.+1) :=
  if unlift ord_max i is Some j then f j else x.
(** Source for [ordinal_snoc_last]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma ordinal_snoc_last (T : Type) n (f : 'I_n -> T) x : ordinal_snoc f x ord_max = x.
Proof. by rewrite /ordinal_snoc unlift_none. Qed.
(** Source for [ordinal_snoc_before]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma ordinal_snoc_before (T : Type) n (f : 'I_n -> T) x i :
  ordinal_snoc f x (widen_ord (leqnSn n) i) = f i.
Proof.
have he : widen_ord (leqnSn n) i = lift ord_max i by apply: val_inj; exact (esym (lift_max i)).
by rewrite he /ordinal_snoc liftK.
Qed.
(** Source for [ordinal_snoc_lift]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma ordinal_snoc_lift (T : Type) n (f : 'I_n -> T) x i : ordinal_snoc f x (lift ord_max i) = f i.
Proof. by rewrite /ordinal_snoc liftK. Qed.

Section IndependentSequence.
Variable K : fieldType.
Variable V : lmodType K.
(** Source for [infinite_dimensional]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition infinite_dimensional : Prop := forall n (e : 'I_n -> V),
  exists v : V, forall c : 'I_n -> K, v != \sum_i c i *: e i.
(** Source for [finite_independent_snoc]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma finite_independent_snoc n (e : 'I_n -> V) v :
  finite_independent e -> (forall c : 'I_n -> K, v != \sum_i c i *: e i) ->
  finite_independent (ordinal_snoc e v).
Proof.
move=> he hv c hc.
rewrite big_ord_recr ordinal_snoc_last in hc.
have hs : (\sum_i c (widen_ord (leqnSn n) i) *: ordinal_snoc e v (widen_ord (leqnSn n) i)) =
    \sum_i c (widen_ord (leqnSn n) i) *: e i.
  apply: eq_bigr => i _; by rewrite ordinal_snoc_before.
rewrite hs in hc.
change ((\sum_i c (widen_ord (leqnSn n) i) *: e i) + c ord_max *: v = 0) in hc.
case hlast : (c ord_max == 0).
- move/eqP: hlast => hl; rewrite hl scale0r addr0 in hc.
  have hz := he _ hc.
  move=> i; case: (unliftP ord_max i) => [j ->|->] //.
  have hj : lift ord_max j = widen_ord (leqnSn n) j by apply: val_inj; exact: lift_max.
  by rewrite hj; exact: hz.
- have hn : c ord_max != 0 := negbT hlast.
  have hh := congr1 (fun z : V => (c ord_max)^-1 *: z) (addr0_eq hc).
  rewrite scalerN scalerA (mulVf hn) scale1r in hh.
  have heq : v = \sum_i (-(c ord_max)^-1*c (widen_ord (leqnSn n) i)) *: e i.
    under eq_bigr do rewrite -scalerA.
    rewrite -(scaler_sumr (-(c ord_max)^-1)) scaleNr.
    exact (esym hh).
  by have hv' := hv (fun i => -(c ord_max)^-1*c (widen_ord (leqnSn n) i)); rewrite -heq eqxx in hv'.
Qed.
Hypothesis hinf : infinite_dimensional.
(** Source for [outside_finite_span]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition outside_finite_span n (e : 'I_n -> V) : V :=
  sval (constructive_indefinite_description (hinf e)).
(** Source for [outside_finite_spanP]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma outside_finite_spanP n (e : 'I_n -> V) c : outside_finite_span e != \sum_i c i *: e i.
Proof. exact: (svalP (constructive_indefinite_description (hinf e))). Qed.
(** Source for [independent_frame]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Fixpoint independent_frame n : 'I_n -> V :=
  match n as j return 'I_j -> V with
  | 0%N => fun _ => 0
  | j.+1 => ordinal_snoc (@independent_frame j) (outside_finite_span (@independent_frame j))
  end.
(** Source for [independent_sequence]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition independent_sequence n := outside_finite_span (@independent_frame n).
(** Source for [independent_frameP]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma independent_frameP n : finite_independent (@independent_frame n).
Proof.
elim: n => [|n ih].
- move=> c hc i; have hi := ltn_ord i; by rewrite ltn0 in hi.
- exact: finite_independent_snoc ih (outside_finite_spanP (@independent_frame n)).
Qed.
(** Source for [independent_frameE]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma independent_frameE n (i : 'I_n) : @independent_frame n i = independent_sequence (val i).
Proof.
elim: n i => [|n ih] i; first by have hi := ltn_ord i; rewrite ltn0 in hi.
case: (unliftP ord_max i) => [j ->|->].
- change (ordinal_snoc (@independent_frame n) (independent_sequence n) (lift ord_max j) =
    independent_sequence (val (lift ord_max j))).
  rewrite ordinal_snoc_lift.
  exact (eq_trans (ih j) (congr1 independent_sequence (esym (lift_max j)))).
- exact: ordinal_snoc_last.
Qed.
(** Source for [independent_sequence_prefix]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Theorem independent_sequence_prefix n : finite_independent (fun i : 'I_n => independent_sequence (val i)).
Proof.
move=> c hc; apply (@independent_frameP n c).
have hs : (\sum_i c i *: @independent_frame n i) = \sum_i c i *: independent_sequence (val i).
  by apply: eq_bigr => i _; rewrite independent_frameE.
by rewrite hs.
Qed.
End IndependentSequence.
