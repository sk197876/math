(** Federer (1969), 4.1.6, p. 352: the actual
    multilinear norm on forms, behind an opaque interface.
    The exact least-bound specification and the finite-source
    existence proof precede this selection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP AlternatingForms AlternatingFormNormUP AlternatingFormNormExistence
  InnerProductUP InnerNorm LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type AlternatingFormNormSignature.
(** Source for [value]: the induced norm of Federer
    4.1.6, p. 352, on the original alternating forms. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0)
  (V W:lmodType R) (B:V->V->R) (hB:is_inner_product B)
  n (e:'I_n->V),is_basis e ->forall (NW:W->R),is_real_norm NW ->
  forall m,A_m V W m->R.
(** Source for [laws]: exact original multilinear norm
    laws, Federer 4.1.6, p. 352. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0)
  (V W:lmodType R) (B:V->V->R) (hB:is_inner_product B)
  n (e:'I_n->V) (he:is_basis e) (NW:W->R) (hNW:is_real_norm NW) m,
  is_alternating_form_norm (inner_norm hB) NW (@value R h2 V W B hB n e he NW hNW m).
(** Source for [norm_laws]: the induced finite norm is
    a norm, Federer 4.1.6, p. 352. *)
Parameter norm_laws:forall (R:realType) (h2:(1+1:R)!=0)
  (V W:lmodType R) (B:V->V->R) (hB:is_inner_product B)
  n (e:'I_n->V) (he:is_basis e) (NW:W->R) (hNW:is_real_norm NW) m,
  is_real_norm (@value R h2 V W B hB n e he NW hNW m).
End AlternatingFormNormSignature.
Module AlternatingFormNorm:AlternatingFormNormSignature.
(** Source for [value]: select only the already proved
    norm witness, Federer 4.1.6, p. 352. *)
Definition value (R:realType) (h2:(1+1:R)!=0)
    (V W:lmodType R) (B:V->V->R) (hB:is_inner_product B)
    n (e:'I_n->V) (he:is_basis e) (NW:W->R) (hNW:is_real_norm NW) m:A_m V W m->R:=
  proj1_sig (cid (@alternating_form_norm_exists R h2 V W B hB n e he NW hNW m)).
(** Source for [laws]: the opaque witness satisfies the
    exact independent norm laws, Federer 4.1.6, p. 352. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0)
    (V W:lmodType R) (B:V->V->R) (hB:is_inner_product B)
    n (e:'I_n->V) (he:is_basis e) (NW:W->R) (hNW:is_real_norm NW) m:
  is_alternating_form_norm (inner_norm hB) NW (@value R h2 V W B hB n e he NW hNW m).
Proof. exact:(proj2_sig (cid (@alternating_form_norm_exists R h2 V W B hB n e he NW hNW m))).2. Qed.
(** Source for [norm_laws]: the norm property was proved
    before sealing, Federer 4.1.6, p. 352. *)
Lemma norm_laws (R:realType) (h2:(1+1:R)!=0)
    (V W:lmodType R) (B:V->V->R) (hB:is_inner_product B)
    n (e:'I_n->V) (he:is_basis e) (NW:W->R) (hNW:is_real_norm NW) m:
  is_real_norm (@value R h2 V W B hB n e he NW hNW m).
Proof. exact:(proj2_sig (cid (@alternating_form_norm_exists R h2 V W B hB n e he NW hNW m))).1. Qed.
End AlternatingFormNorm.
