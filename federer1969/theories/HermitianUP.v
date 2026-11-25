(** Federer (1969), 1.8.2, p. 39, opening paragraph: a Hermitian product is
    real bilinear, linear under multiplication by i in its second argument,
    conjugate symmetric, and positive on nonzero diagonal vectors. The
    convention is linearity in the second slot. Scalar background and source
    editions: ComplexScalarUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP ScalarRestriction ComplexScalarSealed ComplexScalarLaws Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_hermitian_product]: Federer 1.8.2,
    p. 39, opening three displayed conditions together with real
    bilinearity. This specification imposes no finite-dimensional
    hypothesis and assumes no existence of a product on every space. *)
Record is_hermitian_product (R : realFieldType)
    (V : lmodType (ComplexScalars.C R))
    (H : V -> V -> ComplexScalars.C R) : Prop := {
  hermitian_real_bilinear :
    @bilinear R (restricted_space (ComplexScalars.embed R) V)
      (restricted_space (ComplexScalars.embed R) V)
      (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) H;
  hermitian_i_right : forall v w, H v (ComplexScalars.ii R *: w) =
    ComplexScalars.ii R * H v w;
  hermitian_conjugate_symmetric : forall v w,
    H w v = ComplexScalarTheory.conjugate (H v w);
  hermitian_positive : forall v, v != 0 -> 0 < ComplexScalars.re (H v v)
}.
