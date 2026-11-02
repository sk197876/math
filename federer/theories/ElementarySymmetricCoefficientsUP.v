(** Federer (1969), 3.2.36, p. 273: independently
    specify elementary symmetric coefficients by their generating polynomial. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import PositivePolynomialCoefficientUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_elementary_symmetric_coefficients]: the m-th
    elementary symmetric functions of the edge lengths in Federer
    3.2.36, p. 273. The independent defining law specifies their
    coefficients in the product of 1+c_i t. It refers to no
    geometric volume or box construction. The erratum p. 5 corrects
    book p. 273 line 18 to m-th. The empty product and zeroth
    coefficient are retained. Existence and uniqueness are proof
    obligations; the predicate selects no global coefficient family. *)
Definition is_elementary_symmetric_coefficients (R:realType) n
    (c:'I_n->R) (e:'I_n.+1->R):Prop:=
  forall t:R,\prod_(i:'I_n) (1+c i*t)=\sum_(j:'I_n.+1) e j*t^+j.

(** Source for [elementary_symmetric_coefficients_unique]: the unique
    identification of the elementary symmetric edge functions in
    Federer 3.2.36, p. 273. The independent product-polynomial
    law and the project's internal positive-radius root count prove
    uniqueness for all real edge values, including zero widths and
    the empty edge family. No external polynomial library is used. *)
Theorem elementary_symmetric_coefficients_unique (R:realType) n
    (c:'I_n->R) (e d:'I_n.+1->R):
  is_elementary_symmetric_coefficients c e ->is_elementary_symmetric_coefficients c d ->
  forall j,e j=d j.
Proof.
move=>hE hD.
pose a (j:nat):R^o:=e (inord j).
pose b (j:nat):R^o:=d (inord j).
have hPowers (t:R):0<t ->\sum_(j<n.+1) t^+j*:a j=\sum_(j<n.+1) t^+j*:b j.
  move=>ht.
  have hLeft: \sum_(j<n.+1) t^+j*:a j=\sum_(j:'I_n.+1) e j*t^+j.
    apply:eq_bigr=>j _; by rewrite /a inord_val mulrC.
  have hRight: \sum_(j<n.+1) t^+j*:b j=\sum_(j:'I_n.+1) d j*t^+j.
    apply:eq_bigr=>j _; by rewrite /b inord_val mulrC.
  by rewrite hLeft hRight -(hE t) -(hD t).
have hCoefficients:=@positive_finite_power_coefficients_unique R R^o n.+1 a b hPowers.
move=>j; have h:=hCoefficients j (ltn_ord j).
by rewrite /a /b inord_val in h.
Qed.
