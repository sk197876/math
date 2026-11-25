(** Federer (1969), 3.3.4, pp. 289–290:
    independently specify the active-space operator
    by its action on that space and by
    identity on the complementary kernel. The
    direct-sum argument is the algebra of 1.1.2,
    pp. 2–3; no extension is assumed to exist. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_injection_extension]: the
    operator acting as h on the active
    space and fixing its complement, supporting
    H and K in Federer 3.3.4, pp. 289–290.
    The supplied retraction q independently specifies
    that complement as its exact kernel. *)
Definition is_injection_extension (K:fieldType) (U V:lmodType K)
    (w:Hom U V) (q:Hom V U) (h:Hom U U) (H:Hom V V):=
  (forall u,H (w u)=w (h u)) /\ forall x,q x=0 ->H x=x.

(** Source for [injection_extension_decomposition]:
    supporting the active/complement split in
    Federer 3.3.4, p. 290. The two
    defining laws and the retraction identity
    determine the extension on every original
    vector; this is a consequence of the
    specification, not access to an implementation. *)
Lemma injection_extension_decomposition (K:fieldType) (U V:lmodType K)
    (w:Hom U V) (q:Hom V U) (h:Hom U U) (H:Hom V V):
  cancel w q ->is_injection_extension w q h H ->forall x,
    H x=x-w (q x)+w (h (q x)).
Proof.
move=>hCancel [hActive hFixed] x.
have hNormal:q (x-w (q x))=0.
  rewrite (linearB (hom_as_linear q)).
  by rewrite !hom_as_linearE hCancel subrr.
have hSplit:x=(x-w (q x))+w (q x) by rewrite subrK.
by rewrite {1}hSplit (linearD (hom_as_linear H)) !hom_as_linearE hFixed // hActive.
Qed.

(** Source for [injection_extension_unique]: the
    action on the active space and identity
    on its complement uniquely determine the
    original operator in Federer 3.3.4,
    pp. 289–290. The kernel and range
    decomposition covers the whole original space. *)
Lemma injection_extension_unique (K:fieldType) (U V:lmodType K)
    (w:Hom U V) (q:Hom V U) (h:Hom U U) (H G:Hom V V):
  cancel w q ->is_injection_extension w q h H ->is_injection_extension w q h G ->H=G.
Proof.
move=>hCancel hH hG; apply:hom_ext=>x.
by rewrite (injection_extension_decomposition hCancel hH) (injection_extension_decomposition hCancel hG).
Qed.
