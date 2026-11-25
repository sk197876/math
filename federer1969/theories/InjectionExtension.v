(** Federer (1969), 3.3.4, pp. 289–290:
    public active/complement extension laws derived
    only from the opaque operator's independent
    specification. No implementation is imported here. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom TensorUP InjectionExtensionUP InjectionExtensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [injection_extension]: the unique
    active/complement operator supporting Federer
    3.3.4, pp. 289–290, accessed through
    its existing proved opaque specification. *)
Definition injection_extension (K:fieldType) (U V:lmodType K)
    (w:Hom U V) (q:Hom V U) (hCancel:cancel w q) (h:Hom U U):=
  @InjectionExtension.value K U V w q h hCancel.

(** Source for [injection_extension_specification]:
    action on the actual active range and
    identity on its complementary kernel,
    supporting Federer 3.3.4, pp. 289–290. *)
Lemma injection_extension_specification (K:fieldType) (U V:lmodType K)
    (w:Hom U V) (q:Hom V U) (hCancel:cancel w q) (h:Hom U U):
  is_injection_extension w q h (injection_extension hCancel h).
Proof. exact:InjectionExtension.laws. Qed.

(** Source for [injection_extension_projection]: the
    actual active coordinate of the extended
    vector is h(q x), supporting Federer
    3.3.4, pp. 289–290. This follows
    from the direct-sum decomposition and the
    supplied retraction identity alone. *)
Lemma injection_extension_projection (K:fieldType) (U V:lmodType K)
    (w:Hom U V) (q:Hom V U) (hCancel:cancel w q) (h:Hom U U) x:
  q (injection_extension hCancel h x)=h (q x).
Proof.
rewrite (injection_extension_decomposition hCancel (injection_extension_specification hCancel h)).
by rewrite (linearD (hom_as_linear q)) (linearB (hom_as_linear q)) !hom_as_linearE !hCancel subrr add0r.
Qed.

(** Source for [injection_extension_composition]: the
    active-space extensions form the actual
    subgroup fixing the complementary kernel,
    supporting H and K in Federer 3.3.4,
    pp. 289–290. Composition is proved
    from the independent action and fixed-space laws. *)
Lemma injection_extension_composition (K:fieldType) (U V:lmodType K)
    (w:Hom U V) (q:Hom V U) (hCancel:cancel w q) (h g:Hom U U):
  hom_comp (injection_extension hCancel h) (injection_extension hCancel g)=
    injection_extension hCancel (hom_comp h g).
Proof.
apply:(injection_extension_unique hCancel); last exact:injection_extension_specification.
have [hActive hFixed]:=injection_extension_specification hCancel h.
have [gActive gFixed]:=injection_extension_specification hCancel g.
split.
- by move=>u; rewrite hom_compE gActive hActive.
- by move=>x hx; rewrite hom_compE gFixed // hFixed.
Qed.

(** Source for [injection_extension_identity]: the
    actual identity on the active space
    extends to identity on the whole space,
    supporting the subgroup in Federer 3.3.4,
    pp. 289–290. *)
Lemma injection_extension_identity (K:fieldType) (U V:lmodType K)
    (w:Hom U V) (q:Hom V U) (hCancel:cancel w q):
  injection_extension hCancel (hom_of_linear (@linear_id K U))=hom_of_linear (@linear_id K V).
Proof.
apply:(injection_extension_unique hCancel); first exact:injection_extension_specification.
by split.
Qed.

(** Source for [injection_extension_inverse]: an
    actual inverse active map extends to
    the actual inverse on the original whole
    space, supporting the subgroup in Federer
    3.3.4, pp. 289–290. *)
Lemma injection_extension_inverse (K:fieldType) (U V:lmodType K)
    (w:Hom U V) (q:Hom V U) (hCancel:cancel w q) (h g:Hom U U):
  cancel h g ->cancel (injection_extension hCancel h) (injection_extension hCancel g).
Proof.
move=>hInverse x.
have hComposition:hom_comp g h=hom_of_linear (@linear_id K U) by apply:hom_ext.
change (hom_comp (injection_extension hCancel g) (injection_extension hCancel h) x=x).
by rewrite injection_extension_composition hComposition injection_extension_identity.
Qed.
