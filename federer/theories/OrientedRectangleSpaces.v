(** Federer (1969), 4.1.8, p. 362: the
    actual current spaces and original binary products
    for finite oriented rectangular parallelepipeds.
    Factor dimensions and domains remain independent. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear CurrentSpaces OrientedSegmentFactor OrientedRectangleDomain
  CurrentCartesianProductSealed CurrentCartesianProductBilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section OrientedRectangleSpaces.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation Factor := (oriented_segment_factor R).

(** Source for [oriented_rectangle_space]: the actual
    degree-k current space on the original finite
    Cartesian domain, supporting the finite Stokes
    formula in Federer 4.1.8, p. 362. *)
Definition oriented_rectangle_space (f:seq Factor) k:=
  @current_space R h2 (oriented_rectangle_dimension f) (@oriented_rectangle_domain R f)
    (@oriented_rectangle_domain_open R f) k.

(** Source for [oriented_rectangle_product]: the original
    binary current product attaching the first factor
    to a nonempty remaining family, supporting the
    induction in Federer 4.1.8, p. 362. *)
Definition oriented_rectangle_product (a b:Factor) (t:seq Factor) i j:
    oriented_rectangle_space [::a] i->oriented_rectangle_space (b::t) j->
      oriented_rectangle_space (a::b::t) (i+j):=
  @CartesianCurrentProduct.value R h2 (oriented_segment_factor_dimension a)
    (oriented_rectangle_dimension (b::t)) i j (@oriented_segment_factor_domain R a)
    (@oriented_rectangle_domain R (b::t)) (@oriented_segment_factor_open R a)
    (@oriented_rectangle_domain_open R (b::t)).

(** Source for [oriented_rectangle_product_bilinear]: each
    original attachment product is bilinear, supporting
    expansion of the Stokes sum in Federer 4.1.8,
    p. 362, by the preceding p. 361 product law. *)
Lemma oriented_rectangle_product_bilinear a b t i j:
  bilinear (@oriented_rectangle_product a b t i j).
Proof.
exact:(@current_cartesian_product_bilinear R h2 (oriented_segment_factor_dimension a)
  (oriented_rectangle_dimension (b::t)) i j (@oriented_segment_factor_domain R a)
  (@oriented_rectangle_domain R (b::t)) (@oriented_segment_factor_open R a)
  (@oriented_rectangle_domain_open R (b::t))).
Qed.
End OrientedRectangleSpaces.

Arguments oriented_rectangle_product : clear implicits.
