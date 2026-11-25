(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp.
From Federer Require Import AlternatingAlgebra.
From Federer Require Import FiniteIndependence OneFormLinear.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.3, 'choosing e_j': a finite independent family of
    linear functionals has a biorthogonal family of vectors, even when
    V has infinite dimension. The construction successively removes
    the components already detected by the other functionals. *)
(** Source for [ordinal_cons]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Definition or construction used to formalise this
    passage. *)
Definition ordinal_cons (T : Type) n (x : T) (f : 'I_n -> T) (i : 'I_n.+1) :=
  if unlift ord0 i is Some j then f j else x.
(** Source for [ordinal_cons0]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma ordinal_cons0 (T : Type) n (x : T) (f : 'I_n -> T) : ordinal_cons x f ord0 = x.
Proof. by rewrite /ordinal_cons unlift_none. Qed.
(** Source for [ordinal_consS]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma ordinal_consS (T : Type) n (x : T) (f : 'I_n -> T) i :
  ordinal_cons x f (lift ord0 i) = f i.
Proof. by rewrite /ordinal_cons liftK. Qed.

(** Source for [finite_independent_tail]: Federer (1969), 1.4.3, p. 19,
    opening assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma finite_independent_tail (K : fieldType) (V : lmodType K) n (e : 'I_n.+1 -> V) :
  finite_independent e -> finite_independent (fun i => e (lift ord0 i)).
Proof.
move=> he c hc i.
pose d := ordinal_cons (0 : K) c.
have hd : \sum_j d j *: e j = 0.
  rewrite big_ord_recl /d ordinal_cons0 scale0r add0r.
  under eq_bigr do rewrite ordinal_consS.
  exact: hc.
have h := he d hd (lift ord0 i); by rewrite /d ordinal_consS in h.
Qed.

Section Evaluation.
Variable K : fieldType.
Variable V : lmodType K.
(** Source for [hom_sumE]: Federer (1969), 1.4.3, p. 19, opening assertion
    and biorthogonal-vector argument. In words: Increasing products of a
    finite independent family of covectors are independent; evaluation on
    the corresponding products of biorthogonal vectors gives the Kronecker
    pairing. Supporting lemma for this passage; not separately stated in the
    book. *)
Lemma hom_sumE (I : finType) (f : I -> Hom V K^o) v :
  (\sum_i f i) v = \sum_i f i v.
Proof. exact (big_morph (fun f : Hom V K^o => f v) (fun f g => hom_addE f g v) (@hom_zeroE K V K^o v) _ _ _). Qed.
(** Source for [biorthogonal_sum]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma biorthogonal_sum (I : finType) (f : I -> Hom V K^o) (e : I -> V) :
  (forall i j, f i (e j) = if i == j then 1 else 0) ->
  forall c : I -> K, forall i, f i (\sum_j c j *: e j) = c i.
Proof.
move=> h c i; rewrite linear_sum.
change ((\sum_j f i (c j *: e j)) = c i).
under eq_bigr do rewrite (linZ (hom_linear (f i))) h.
change ((\sum_j c j * (if i == j then 1 else 0)) = c i).
rewrite (bigD1 i) //= eqxx mulr1.
have hz : (\sum_(j | j != i) c j * (if i == j then 1 else 0)) = 0.
  apply: big1 => j hj; by rewrite eq_sym (negbTE hj) mulr0.
by rewrite hz addr0.
Qed.
(** Source for [nonzero_hom_vector]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma nonzero_hom_vector (f : Hom V K^o) : f != 0 -> exists v, f v != 0.
Proof.
move=> hf; have [h|h] := pselect (exists v, f v != 0); first exact: h.
have he : f = 0.
  apply: hom_ext => v; rewrite hom_zeroE.
  apply/eqP; apply/negPn/negP=> hv; apply: h; by exists v.
by rewrite he eqxx in hf.
Qed.
End Evaluation.

Section Residual.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Variable omega : 'I_n.+1 -> Hom V K^o.
Hypothesis homega : finite_independent omega.
Variable e : 'I_n -> V.
(** Source for [residual_functional]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Definition or construction used to formalise this
    passage. *)
Definition residual_functional : Hom V K^o :=
  omega ord0 - \sum_i (omega ord0 (e i) : K) *: omega (lift ord0 i).
(** Source for [residual_functional_nonzero]: Federer (1969), 1.4.3, p. 19,
    opening assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma residual_functional_nonzero : residual_functional != 0.
Proof.
apply/negP=> /eqP hr.
pose c := ordinal_cons (1 : K) (fun i => - omega ord0 (e i)).
have hc : \sum_i c i *: omega i = 0.
  rewrite big_ord_recl /c ordinal_cons0 scale1r.
  under eq_bigr do rewrite ordinal_consS scaleNr.
  rewrite sumrN; exact hr.
have h := @homega c hc ord0.
by move/eqP: h; rewrite /c ordinal_cons0 oner_eq0.
Qed.
Hypothesis hdual : forall i j : 'I_n,
  omega (lift ord0 i) (e j) = if i == j then 1 else 0.
(** Source for [residual_vector]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Definition or construction used to formalise this
    passage. *)
Definition residual_vector (v : V) : V := v - \sum_i (omega (lift ord0 i) v : K) *: e i.
(** Source for [residual_vector_tail]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma residual_vector_tail v i : omega (lift ord0 i) (residual_vector v) = 0.
Proof.
rewrite /residual_vector (linB (hom_linear (omega (lift ord0 i)))) (biorthogonal_sum hdual) subrr.
by [].
Qed.
(** Source for [residual_vector_head]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma residual_vector_head v : omega ord0 (residual_vector v) = residual_functional v.
Proof.
rewrite /residual_vector (linB (hom_linear (omega ord0))) linear_sum.
change (omega ord0 v - \sum_i omega ord0 ((omega (lift ord0 i) v : K) *: e i) =
  omega ord0 v - (\sum_i (omega ord0 (e i) : K) *: omega (lift ord0 i)) v).
rewrite hom_sumE; congr (_ - _); apply: eq_bigr => i _.
rewrite (linZ (hom_linear (omega ord0))) hom_scaleE.
change (omega (lift ord0 i) v * omega ord0 (e i) = omega ord0 (e i) * omega (lift ord0 i) v).
exact: mulrC.
Qed.
End Residual.

(** Source for [biorthogonal_exists]: Federer (1969), 1.4.3, p. 19, opening
    assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem biorthogonal_exists (K : fieldType) (V : lmodType K) n
    (omega : 'I_n -> Hom V K^o) : finite_independent omega ->
  exists e : 'I_n -> V, forall i j, omega i (e j) = if i == j then 1 else 0.
Proof.
elim: n omega => [|n ih] omega homega.
- exists (fun i : 'I_0 => 0); move=> i j; have hi := ltn_ord i; by rewrite ltn0 in hi.
- have [e he] := ih (fun i => omega (lift ord0 i)) (finite_independent_tail homega).
  have [v hv] := nonzero_hom_vector (residual_functional_nonzero homega e).
  pose z := residual_vector omega e v.
  have hz : omega ord0 z != 0 by rewrite /z residual_vector_head.
  pose u := (omega ord0 z : K)^-1 *: z.
  have hu0 : omega ord0 u = 1.
    rewrite /u (linZ (hom_linear (omega ord0))).
    change ((omega ord0 z)^-1 * omega ord0 z = 1); exact: mulVf hz.
  have hut i : omega (lift ord0 i) u = 0.
    rewrite /u (linZ (hom_linear (omega (lift ord0 i)))) /z (residual_vector_tail he) scaler0.
    by [].
  exists (ordinal_cons u (fun i => e i - (omega ord0 (e i) : K) *: u)) => i j.
  case: (unliftP ord0 i) => [a ->|->]; case: (unliftP ord0 j) => [b ->|->].
  + rewrite ordinal_consS (linB (hom_linear (omega (lift ord0 a))))
      (linZ (hom_linear (omega (lift ord0 a)))) hut scaler0 subr0 he.
    by rewrite (inj_eq (@lift_inj _ ord0)).
  + by rewrite ordinal_cons0 hut lift_eqF.
  + rewrite ordinal_consS (linB (hom_linear (omega ord0))) (linZ (hom_linear (omega ord0))) hu0 eq_liftF.
    change (omega ord0 (e b) - omega ord0 (e b) * 1 = 0); by rewrite mulr1 subrr.
  + by rewrite ordinal_cons0 hu0 eqxx.
Qed.

(** Federer 1.4.3, applied to the actual one-covectors. *)
(** Source for [covectors_biorthogonal]: Federer (1969), 1.4.3, p. 19,
    opening assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem covectors_biorthogonal (K : fieldType) (V : lmodType K) n
    (omega : 'I_n -> A_m V K^o 1) : finite_independent omega ->
  exists e : 'I_n -> V, forall i j, omega i [tuple e j] = if i == j then 1 else 0.
Proof.
move=> hw.
have hh : finite_independent (fun i => one_hom (omega i)).
  exact (@finite_independent_map K (Finite.clone 'I_n _) (A_m V K^o 1) (Hom V K^o)
    (GRing.Linear.clone _ _ _ _ (@one_hom K V K^o) _) omega (@one_hom_injective K V K^o) hw).
exact: biorthogonal_exists hh.
Qed.
