(** Federer (1969), 1.6.5, pp. 25-26: supporting zero case for
    extending the adapted-family computation. If a nonzero factor
    of the chosen volume annihilates both input words, both sides
    of the desired contraction identity vanish. This supplies an
    explicit argument for the nontransverse basis pairs that the
    displayed proof does not compute separately. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors CovectorKernelProjection ProductSpaceMaps
  CovectorProductNaturality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Import FedererProduct.

(** Source for [one_hom_dualE]: Federer 1.6.5, p. 26,
    evaluation of omega_j composed with f. Supporting evaluation
    identity for the one-form/functional identification. *)
Lemma one_hom_dualE (K : fieldType) (V W : lmodType K)
  (f : {linear V -> W}) (a : A_m W K^o 1) v :
  one_hom (A_m_dual f a) v = one_hom a (f v).
Proof.
rewrite !one_homE A_m_dualE.
have ht : map_tuple f [tuple v] = [tuple f v] by apply: val_inj.
by rewrite ht.
Qed.

Section Missing.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable omega : 'I_n -> A_m V K^o 1.
Variable j : 'I_n.
Variable d : V.
Hypothesis hd : one_hom (omega j) d = 1.
Variables x y : seq V.
Hypotheses (hx : forall v, v \in x -> one_hom (omega j) v = 0)
  (hy : forall v, v \in y -> one_hom (omega j) v = 0).
Local Notation volume := (one_forms_wedge h2 (scalar_bilinear K) (1 : K^o) omega).
Local Notation W := (GRing.Lmodule.clone K (V * V)%type _).
Local Notation gamma := (fun i => A_m_dual (f_map V) (omega i)).

(** Source for [product_missing_volume_factor]: Federer 1.6.5,
    pp. 25-26, supporting nontransverse left member. The pulled-back
    missing covector annihilates every P and Q factor, so contraction
    by the pulled-back volume gives zero. *)
Theorem product_missing_volume_factor :
  left_interior_hom h2
    (wedge (exterior_word [seq P v | v <- x]) (exterior_word [seq Q v | v <- y]))
    (form_homogeneous (A_m_dual (f_map V) volume)) = 0.
Proof.
rewrite one_forms_wedge_natural exterior_word_cat.
have hn : one_hom (gamma j) (P d) = 1.
  rewrite one_hom_dualE; change (one_hom (omega j) (f (P d)) = 1).
  by rewrite f_P hd.
apply: (@word_contraction_missing_covector K h2 W n gamma j (P d) hn).
move=> w; rewrite mem_cat => /orP [/mapP [v hv ->]|/mapP [v hv ->]].
- rewrite one_hom_dualE; change (one_hom (omega j) (f (P v)) = 0).
  by rewrite f_P (hx hv).
- rewrite one_hom_dualE; change (one_hom (omega j) (f (Q v)) = 0).
  rewrite f_Q linearN; change (- one_hom (omega j) v = 0).
  by rewrite (hy hv) oppr0.
Qed.

(** Source for [product_missing_dual_factor]: Federer 1.6.5,
    pp. 25-26, supporting nontransverse right member after applying
    dual_product_contraction. The mixed contraction is zero when
    the same volume factor annihilates both words. *)
Theorem product_missing_dual_factor :
  left_interior_hom h2 (exterior_word x)
    (right_interior_hom (exterior_word y) (form_homogeneous volume)) = 0.
Proof. exact: (@mixed_words_missing_covector K h2 V n omega j d hd x y hx hy). Qed.
End Missing.
