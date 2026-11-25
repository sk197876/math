(** Federer (1969), 4.1.6, pp. 352–353: unit-tuple
    consequences of the original induced multilinear norm.
    These exact bounds include degree zero and support
    the coefficient products and exterior differentiation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP TensorFamilyUP ContinuousMultilinearUP NormMultilinearBound
  AlternatingForms AlternatingFormNormBound AlternatingFormNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [alternating_form_unit_tuple_bound]: the
    actual corrected supremum norm of 3.1.11 bounds
    evaluation on every unit tuple, as used in Federer
    4.1.6, pp. 352–353. Empty tuples are included. *)
Lemma alternating_form_unit_tuple_bound (R:realType) (V W:lmodType R)
    (NV:V->R) (NW:W->R) (hNV:is_real_norm NV) m (phi:A_m V W m) c
    (hc:is_multilinear_operator_norm NV NW (form_ordered_value phi) c) (t:m.-tuple V):
  (forall i,NV (tnth t i)<=1) ->NW (phi t)<=c.
Proof.
move=>hUnit.
have hProduct:(\prod_(i<m) NV (tnth t i))<=1.
  have hOne:(\prod_(i<m) (1:R))= 1 by apply:big1.
  rewrite -[X in _<=X]hOne.
  apply:ler_prod=>i _; apply/andP; split.
  - exact:real_seminorm_nonnegative hNV.1 _.
  - exact:hUnit.
have hBound:=multilinear_operator_bound hc [ffun i=>tnth t i].
rewrite form_ordered_value_tuple in hBound.
apply:le_trans hBound _.
have hProduct':(\prod_(i<m) NV ([ffun j=>tnth t j] i))<=1.
  by under eq_bigr do rewrite ffunE.
have h:=ler_wpM2l (multilinear_operator_nonnegative hc) hProduct'.
by rewrite mulr1 in h.
Qed.

(** Source for [alternating_form_unit_tuple_least]: the
    original norm is bounded by each common unit-tuple
    bound, Federer 4.1.6, p. 352, using the
    normalization theorem already proved for 3.1.1(4). *)
Lemma alternating_form_unit_tuple_least (R:realType) (V W:lmodType R)
    (NV:V->R) (NW:W->R) (hNV:is_real_norm NV) (hNW:is_real_norm NW)
    m (phi:A_m V W m) c (hc:is_multilinear_operator_norm NV NW (form_ordered_value phi) c) b:
  0<=b ->(forall t:m.-tuple V,(forall i,NV (tnth t i)<=1)->NW (phi t)<=b) ->c<=b.
Proof.
move=>hB hUnit; apply:(multilinear_operator_least hc hB).
apply:(@norm_multilinear_normalized_bound R m (fun _=>V) W (fun _=>NV) NW
  (fun _=>hNV) hNW (form_ordered_value phi) (form_ordered_value_multilinear phi) b).
move=>u hu.
rewrite /form_ordered_value CovectorProducts.pairing_e_lambda.
apply:hUnit=>i; by rewrite tnth_map tnth_ord_tuple; exact:hu.
Qed.
