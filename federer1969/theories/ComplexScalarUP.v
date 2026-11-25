(** Federer (1969), 1.6.6, pp. 26-27, real and imaginary parts and
    conjugation. This specification describes the elementary scalar
    background; the exterior-algebra claims are proved from these laws. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_complex_scalar_system]: Federer 1.6.6, p. 26,
    opening and conjugation paragraphs. Abstract specification of the
    real and imaginary coordinates of complex numbers, with the usual
    embedding of R and a square root of -1. These are scalar background
    laws, not assumptions of the alternating-form or determinant claims. *)
Record is_complex_scalar_system (R : realFieldType) (C : fieldType)
    (embed : {rmorphism R -> C}) (ii : C) (re im : C -> R) : Prop := {
  complex_re_add : forall x y, re (x + y) = re x + re y;
  complex_im_add : forall x y, im (x + y) = im x + im y;
  complex_re_scale : forall a x, re (embed a * x) = a * re x;
  complex_im_scale : forall a x, im (embed a * x) = a * im x;
  complex_re_one : re 1 = 1;
  complex_im_one : im 1 = 0;
  complex_re_i : re ii = 0;
  complex_im_i : im ii = 1;
  complex_decomposition : forall x, x = embed (re x) + ii * embed (im x);
  complex_i_square : ii * ii = -1
}.
