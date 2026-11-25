(** Federer (1969), 4.1.1, p. 345: extension by
    zero of compactly supported smooth tests from U
    to V. The original values on U and the new
    zero values specify the operator independently. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_test_zero_extension]: exact original
    and zero-extension values in Federer 4.1.1,
    p. 345. Continuity, injectivity and existence
    are separate assertions to prove. *)
Record is_test_zero_extension (R:fieldType) (X:Type) (Y A B:lmodType R)
    (U V:X->Prop) (evA:A->X->Y) (evB:B->X->Y) (L:Hom A B):Prop:={
  (** Source for [test_zero_extension_original]: no value
      on U changes, Federer 4.1.1, p. 345. *)
  test_zero_extension_original:forall f x,U x ->evB (L f) x=evA f x;
  (** Source for [test_zero_extension_zero]: all new values
      on V minus U are zero, Federer 4.1.1,
      p. 345. *)
  test_zero_extension_zero:forall f x,V x ->~U x ->evB (L f) x=0
}.
