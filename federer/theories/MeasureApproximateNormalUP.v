(** Federer (1969), 3.2.16, p. 253:
    the approximate normal cone is the polar of
    the approximate tangent cone, for the norm
    induced by a supplied inner product. The
    inner product and norm laws are proved interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import InnerProductUP InnerNorm HilbertFormCompactness
  MeasureApproximateTangentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_approximate_normal_cone]: the
    displayed definition of Nor_m(phi,a) in Federer
    3.2.16, p. 253. Its vectors have
    nonpositive scalar product with every approximate
    tangent vector, including the zero vector. *)
Definition measure_approximate_normal_cone (R : realType)
    (X : lmodType R) (B : X -> X -> R) (hB : is_inner_product B)
    (phi : set X -> \bar R) m (a : X) : set X :=
  [set u | forall v,
    measure_approximate_tangent_cone (inner_norm_real_norm hB) phi m a v -> B u v<=0].
