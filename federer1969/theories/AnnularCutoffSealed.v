(** Opaque smooth annular cutoff for Federer (1969),
    3.1.23, pp. 236–237. Only the proved qualitative
    and differential-bound laws are exposed downstream. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  AnnularCutoffUP AnnularCutoffConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type AnnularCutoffSignature.
(** Source for [value]: the normalized radial cutoff supporting
    u in Federer 3.1.23, pp. 236–237. *)
Parameter value:forall (R:realType) (X:lmodType R) (B:X->X->R)
  (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e) (t:R),
  0<t<1 -> X->R^o.
(** Source for [bound]: a positive finite bound for the
    normalized cutoff differential, Federer 3.1.23, p. 237. *)
Parameter bound:forall (R:realType) (X:lmodType R) (B:X->X->R)
  (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e) (t:R),
  0<t<1 -> R.
(** Source for [laws]: range, plateaus, radiality, smoothness
    and differential bound for the cutoff in Federer
    3.1.23, pp. 236–237, proved by the implementation. *)
Parameter laws:forall (R:realType) (X:lmodType R) (B:X->X->R)
  (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e) (t:R) (ht:0<t<1),
  is_norm_annular_cutoff (inner_norm_real_norm hB) t
    (@value R X B hB n e he t ht) (@bound R X B hB n e he t ht).
End AnnularCutoffSignature.

Module AnnularCutoff:AnnularCutoffSignature.
(** Source for [value]: select the proved smooth cutoff,
    Federer 3.1.23, pp. 236–237, hidden by opaque sealing. *)
Definition value (R:realType) (X:lmodType R) (B:X->X->R)
    (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e) (t:R) (ht:0<t<1):X->R^o:=
  projT1 (cid (@norm_annular_cutoff_exists R X B hB n e he t ht)).
(** Source for [bound]: select the bound accompanying that
    same cutoff, Federer 3.1.23, p. 237. *)
Definition bound (R:realType) (X:lmodType R) (B:X->X->R)
    (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e) (t:R) (ht:0<t<1):R:=
  projT1 (cid (projT2 (cid (@norm_annular_cutoff_exists R X B hB n e he t ht)))).
(** Source for [laws]: proof of all exposed cutoff laws,
    Federer 3.1.23, pp. 236–237. *)
Lemma laws (R:realType) (X:lmodType R) (B:X->X->R)
    (hB:is_inner_product B) n (e:'I_n->X) (he:is_basis e) (t:R) (ht:0<t<1):
  is_norm_annular_cutoff (inner_norm_real_norm hB) t
    (@value R X B hB n e he t ht) (@bound R X B hB n e he t ht).
Proof. exact (projT2 (cid (projT2 (cid (@norm_annular_cutoff_exists R X B hB n e he t ht))))). Qed.
End AnnularCutoff.
