(** Federer (1969), 3.1.3(3), p. 213: a linear epimorphism is a
    coordinate projection after a linear change of coordinates. The
    automorphism below, followed by the standard block split, is the
    printed isomorphism beta:R^n -> R^m x R^(n-m). *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_euclidean_epimorphism_chart]: abstract laws of the
    linear isomorphism beta in Federer 3.1.3(3), p. 213. Its first m
    coordinates equal the supplied epimorphism. Measure transport is
    derived separately, rather than included in this specification. *)
Record is_euclidean_epimorphism_chart (R : realType) n m
    (p : {linear R_n R n -> R_n R m}) (hmn : (m<=n)%N)
    (f g : {linear R_n R n -> R_n R n}) : Prop := {
  (** Source for [epimorphism_chart_forward_inverse]: the first
      inverse identity of beta, Federer 3.1.3(3), p. 213. *)
  epimorphism_chart_forward_inverse : cancel f g;
  (** Source for [epimorphism_chart_backward_inverse]: the second
      inverse identity of beta, Federer 3.1.3(3), p. 213. *)
  epimorphism_chart_backward_inverse : cancel g f;
  (** Source for [epimorphism_chart_coordinates]: the first-block
      identity identifying alpha^-1(W) with W times the kernel
      coordinates, Federer 3.1.3(3), p. 213. *)
  epimorphism_chart_coordinates : forall x i, f x (widen_ord hmn i)=p x i
}.
