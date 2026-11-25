(** Federer (1969), 1.7.5, p. 32: replacing each vector by its residual
    modulo the span of preceding vectors does not change their exterior
    product. This algebraic supporting lemma does not require independence
    or an inner product. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ExteriorAlgebra ExteriorGrading GradedComponents
  FiniteExteriorPowers ExteriorExpansion FinitePrefixes FiniteSpans
  FiniteSpanTransfer SimpleProducts AssociatedSubspace Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_word_rcons]: Federer 1.7.5,
    p. 32, supporting last-factor decomposition of an exterior word. *)
Lemma exterior_word_rcons (R : fieldType) (V : lmodType R) (s : seq V) v :
  exterior_word (rcons s v) = wedge (exterior_word s) (exterior_generator v).
Proof.
by rewrite -cats1 -exterior_word_cat exterior_word_cons exterior_word_nil wedge_unitr.
Qed.

(** Source for [exterior_product_prefix_last]: Federer
    1.7.5, p. 32, supporting decomposition of an indexed
    product into its initial product and last factor. *)
Lemma exterior_product_prefix_last (R : fieldType) (V : lmodType R)
    n (v : 'I_n.+1 -> V) :
  component_val (e_lambda v (ord_tuple n.+1)) =
    wedge (component_val (e_lambda (family_prefix (leqnSn n) v) (ord_tuple n)))
      (exterior_generator (v ord_max)).
Proof.
rewrite !e_lambdaE /ord_tuple /= enum_ordSr map_rcons -map_comp exterior_word_rcons; by [].
Qed.

(** Source for [triangular_exterior_product_change]: Federer
    1.7.5, p. 32, the identity v1 wedge ... wedge vm =
    w1 wedge ... wedge wm whenever vi-wi belongs to the span
    of the earlier vj. This covers dependent families and the empty product. *)
Theorem triangular_exterior_product_change (R : fieldType) (V : lmodType R)
    n (v w : 'I_n -> V) :
  (forall i : 'I_n, in_finite_span (family_prefix (ltnW (ltn_ord i)) v) (v i-w i)) ->
  e_lambda v (ord_tuple n) = e_lambda w (ord_tuple n).
Proof.
elim: n v w => [|n ih] v w ht.
- apply: val_inj; change (component_val (e_lambda v (ord_tuple 0)) =
    component_val (e_lambda w (ord_tuple 0))).
  by rewrite !e_lambdaE /ord_tuple /= enum_ord0.
pose v0 := family_prefix (leqnSn n) v.
pose w0 := family_prefix (leqnSn n) w.
have ht0 (i : 'I_n) : in_finite_span (family_prefix (ltnW (ltn_ord i)) v0) (v0 i-w0 i).
  pose j := widen_ord (leqnSn n) i.
  have hh := ht j.
  apply: (proj2 (@finite_span_extensional R V i
    (family_prefix (ltnW (ltn_ord i)) v0)
    (family_prefix (ltnW (ltn_ord j)) v) _ (v0 i-w0 i))) hh.
  move=> a; rewrite /v0; exact: family_prefix_compose.
have hh := ih v0 w0 ht0.
have hl : in_finite_span v0 (v ord_max-w ord_max).
  have ha := ht ord_max.
  apply: (proj2 (@finite_span_extensional R V n v0
    (family_prefix (ltnW (ltn_ord (ord_max : 'I_n.+1))) v) _ _)) ha.
  move=> i; rewrite /v0 /family_prefix; congr (v _); exact: val_inj.
have hz := @product_associated_span R V n v0 (v ord_max-w ord_max) hl.
change (wedge (component_val (e_lambda v0 (ord_tuple n)))
  (exterior_generator (v ord_max-w ord_max)) = 0) in hz.
rewrite linearB (bilBr (wedge_bilinear V)) in hz.
have hlast : wedge (component_val (e_lambda v0 (ord_tuple n))) (exterior_generator (v ord_max)) =
    wedge (component_val (e_lambda v0 (ord_tuple n))) (exterior_generator (w ord_max)).
  by apply/eqP; rewrite -subr_eq0 hz eqxx.
apply: val_inj; change (component_val (e_lambda v (ord_tuple n.+1)) =
  component_val (e_lambda w (ord_tuple n.+1))).
by rewrite !exterior_product_prefix_last hlast hh.
Qed.
