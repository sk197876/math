(** Federer (1969), 2.10.38, printed pp. 198–199: supporting algebra for the
    equality between every initial endpoint exterior norm and the product of
    its box widths. Subtracting earlier axis components gives a triangular
    family with these diagonal entries. The algebraic identity below allows
    zero diagonal entries and dependent families; no inverse triangular
    matrix is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ExteriorAlgebra ExteriorGrading GradedComponents
  FiniteExteriorPowers ExteriorExpansion FinitePrefixes FiniteSpans
  FiniteSpanTransfer SimpleProducts AssociatedSubspace Bilinear TriangularProductChange.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [triangular_exterior_product_scaling]: supporting
    exterior-product identity for 2.10.38, p. 199.
    In words, a family triangular relative to another family
    has exterior product equal to that family's product
    multiplied by the diagonal product. This strengthens the
    required real case to any field, includes the empty
    product, and does not require nonzero diagonal entries. *)
Theorem triangular_exterior_product_scaling (R : fieldType) (V : lmodType R)
    n (v e : 'I_n -> V) (c : 'I_n -> R) :
  (forall i : 'I_n, in_finite_span (family_prefix (ltnW (ltn_ord i)) e)
    (v i-c i*:e i)) ->
  e_lambda v (ord_tuple n)=(\prod_(i<n) c i)*:e_lambda e (ord_tuple n).
Proof.
elim: n v e c=> [|n IH] v e c ht.
- apply: val_inj.
  change (component_val (e_lambda v (ord_tuple 0))=
    component_val ((\prod_(i<0) c i)*:e_lambda e (ord_tuple 0))).
  by rewrite big_ord0 scale1r !e_lambdaE /ord_tuple /= enum_ord0.
pose v0 := family_prefix (leqnSn n) v.
pose e0 := family_prefix (leqnSn n) e.
pose c0 := family_prefix (leqnSn n) c.
have ht0 (i : 'I_n) : in_finite_span (family_prefix (ltnW (ltn_ord i)) e0)
    (v0 i-c0 i*:e0 i).
  pose j := widen_ord (leqnSn n) i.
  apply: (proj2 (@finite_span_extensional R V i
    (family_prefix (ltnW (ltn_ord i)) e0)
    (family_prefix (ltnW (ltn_ord j)) e) _ _)) (ht j).
  move=> a; rewrite /e0; exact: family_prefix_compose.
have hh := IH v0 e0 c0 ht0.
have hl : in_finite_span e0 (v ord_max-c ord_max*:e ord_max).
  apply: (proj2 (@finite_span_extensional R V n e0
    (family_prefix (ltnW (ltn_ord (ord_max : 'I_n.+1))) e) _ _)) (ht ord_max).
  move=> i; rewrite /e0 /family_prefix; congr (e _); exact: val_inj.
have hz := @product_associated_span R V n e0 (v ord_max-c ord_max*:e ord_max) hl.
change (wedge (component_val (e_lambda e0 (ord_tuple n)))
  (exterior_generator (v ord_max-c ord_max*:e ord_max))=0) in hz.
rewrite linearB linearZ (bilBr (wedge_bilinear V))
  (bilZr (wedge_bilinear V)) in hz.
have hlast : wedge (component_val (e_lambda e0 (ord_tuple n)))
    (exterior_generator (v ord_max))=
  c ord_max*:wedge (component_val (e_lambda e0 (ord_tuple n)))
    (exterior_generator (e ord_max)).
  by apply/eqP; rewrite -subr_eq0 hz eqxx.
apply: val_inj.
change (component_val (e_lambda v (ord_tuple n.+1))=
  component_val ((\prod_(i<n.+1) c i)*:e_lambda e (ord_tuple n.+1))).
rewrite linearZ !exterior_product_prefix_last hh linearZ
  (bilZl (wedge_bilinear V)) hlast scalerA big_ord_recr.
rewrite /c0 /family_prefix /e0.
change ((\prod_(i<n) c (widen_ord (leqnSn n) i)*c ord_max)*:
  wedge (component_val (e_lambda (family_prefix (leqnSn n) e) (ord_tuple n)))
    (exterior_generator (e ord_max))=
  (\prod_(i<n) c (widen_ord (leqnSn n) i)*c ord_max)*:
    component_val (e_lambda e (ord_tuple n.+1))).
by rewrite exterior_product_prefix_last.
Qed.
