(** Federer (1969), 4.1.6, p. 352: the
    original induced norm on degree-zero forms is
    exactly the coefficient norm. This justifies
    the printed interpretation d phi=D phi. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP AlternatingForms AlternatingZero
  AlternatingFormNormUP AlternatingFormUnitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [alternating_form_zero_norm]: the
    normed identification A^0(V,W)=W used in
    Federer 4.1.6, p. 352, with the
    original multilinear norm of 3.1.11. *)
Theorem alternating_form_zero_norm (R:realType) (V W:lmodType R)
    (NV:V->R) (NW:W->R) (hNV:is_real_norm NV) (hNW:is_real_norm NW)
    (P:A_m V W 0->R) (hP:is_alternating_form_norm NV NW P) (phi:A_m V W 0):
  P phi=NW (zero_form_value phi).
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply:(alternating_form_unit_tuple_least hNV hNW (hP phi)
    (real_seminorm_nonnegative hNW.1 (zero_form_value phi))).
  move=>t _; rewrite (tuple0 t); exact:lexx.
- have hUnit (i:'I_0):NV (tnth ([tuple]:0.-tuple V) i)<=1.
    have hi:=ltn_ord i; by rewrite ltn0 in hi.
  exact:(alternating_form_unit_tuple_bound hNV (hP phi) hUnit).
Qed.
