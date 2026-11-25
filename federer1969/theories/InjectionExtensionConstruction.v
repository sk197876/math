(** Private existence witness for the independently
    specified active/complement operator supporting
    Federer (1969), 3.3.4, pp. 289–290.
    Only its sealing module and the assumptions
    audit may import this construction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom TensorUP InjectionExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [injection_extension_exists]: existence
    of the operator acting as h on an
    actual split injection and fixing its
    complementary kernel, supporting Federer 3.3.4,
    pp. 289–290, by the direct-sum laws
    of 1.1.2, pp. 2–3. *)
Lemma injection_extension_exists (K:fieldType) (U V:lmodType K)
    (w:Hom U V) (q:Hom V U) (h:Hom U U):
  cancel w q ->exists H:Hom V V,is_injection_extension w q h H.
Proof.
move=>hCancel.
pose H:Hom V V:=hom_of_linear (@linear_id K V)-hom_comp w q+hom_comp w (hom_comp h q).
exists H; split.
- move=>u; change (w u-w (q (w u))+w (h (q (w u)))=w (h u)).
  by rewrite hCancel subrr add0r.
- move=>x hx; change (x-w (q x)+w (h (q x))=x).
  have hW0:w 0=0:=linear0 (hom_as_linear w).
  have hH0:h 0=0:=linear0 (hom_as_linear h).
  by rewrite hx hH0 hW0 subr0 addr0.
Qed.
