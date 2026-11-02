(** Federer (1969), 1.6.6, p. 27: coordinate comparison and pullback of
    volume forms. This supporting lemma specialises the multiplicativity of
    the dual map in 1.4.2, p. 18, to fixed degrees. Source context are
    recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates AlternatingProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [form_pullback_product]: Federer 1.6.6, p. 27,
    pullback of complex and real volume products. Supporting consequence
    of Federer 1.4.2, p. 18: pullback preserves the alternating product. *)
Lemma form_pullback_product (K : fieldType) (h2 : (1+1 : K) != 0)
    (V V' W : lmodType K) (f : {linear V -> V'})
    (mu : W -> W -> W) (hm : TensorUP.bilinear mu)
    p q (a : A_m V' W p) (b : A_m V' W q) :
  A_m_dual f (form_wedge h2 hm a b) =
  form_wedge h2 hm (A_m_dual f a) (A_m_dual f b).
Proof.
apply: (can_inj (@form_includeK K V W (p+q))).
rewrite -A_star_dual_include !form_wedge_include A_star_dual_multiplicative
  !A_star_dual_include.
by [].
Qed.
