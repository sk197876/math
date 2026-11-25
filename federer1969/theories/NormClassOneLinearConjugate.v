(** Federer (1969), 3.2.28(1), printed p. 263:
    linear coordinate changes in the Gram regular-level
    argument preserve the actual class-one field. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormClassOneUP NormClassOneLinear NormClassOneComposition
  NormClassOneRestriction NormClassOneLinearPostcompose.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_class_one_full_linear_conjugate]: the
    actual differential v Df(e a) e under linear ambient
    and target coordinates, supporting Federer 3.2.28(1),
    p. 263, by 3.1.1(2), p. 210. Boundedness
    is the only linear-map hypothesis; no inverse is needed. *)
Theorem norm_class_one_full_linear_conjugate (R:realType)
    (A X Y B:lmodType R) (NA:A->R) (NX:X->R) (NY:Y->R) (NB:B->R)
    (hNA:is_real_norm NA) (hNX:is_real_norm NX)
    (hNY:is_real_norm NY) (hNB:is_real_norm NB)
    (e:Hom A X) (v:Hom Y B) (f:X->Y) (D:X->Hom X Y):
  norm_bounded_linear NA NX e ->norm_bounded_linear NY NB v ->
  is_norm_class_one_field NX NY (fun _=>True) f D ->
  is_norm_class_one_field NA NB (fun _=>True)
    (fun a=>v (f (e a))) (fun a=>hom_comp v (hom_comp (D (e a)) e)).
Proof.
move=>hE hV hD.
have hEF:=@norm_class_one_linear_field R A X NA NX hNA hNX
  (fun _=>True) e (fun a _=>@norm_full_domain_interior R A NA a) hE.
have hC:=@norm_class_one_composite_field R A X Y NA NX NY hNA hNX hNY
  (fun _=>True) (fun _=>True) e f (fun _=>e) D hEF hD.
have hT:=@norm_class_one_field_open_restriction R A Y NA NY
  (fun _=>True /\ True) (fun _=>True) (fun a=>f (e a))
  (fun a=>hom_comp (D (e a)) e) (fun a _=>conj I I)
  (fun a _=>@norm_full_domain_interior R A NA a) hC.
exact:(@norm_class_one_linear_postcompose R A Y B NA NY NB hNA hNB
  (fun _=>True) (fun a=>f (e a)) (fun a=>hom_comp (D (e a)) e) v hT hV).
Qed.
