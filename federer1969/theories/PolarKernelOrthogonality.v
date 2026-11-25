(** Federer (1969), 1.7.3, p. 30: the injection factor h maps ker f
    orthogonally into the perpendicular of im f. These consequences use only
    the abstract factorisation laws, not its construction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP OrthogonalMaps PolarFactorisationUP
  Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Kernel.
Variable R : realFieldType.
Variables V U : lmodType R.
Variable B : V -> V -> R.
Variable C : U -> U -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hC : is_inner_product C.
Variable f : {linear V -> U}.
Variable g : {linear V -> V}.
Variable h : {linear V -> U}.
Hypothesis hF : is_injection_factorisation B C f g h.

(** Source for [injection_factor_kernel]: Federer 1.7.3,
    p. 30, supporting identity ker g=ker f for the symmetric
    factor, because the orthogonal factor is injective. *)
Lemma injection_factor_kernel x : f x = 0 <-> g x = 0.
Proof.
split.
- move=> hx; apply: (@orthogonal_map_injective R V U B C hB hC h
    (injection_factor_orthogonal hF)).
  by rewrite linear0 (injection_factor_equation hF) hx.
- move=> hx; by rewrite -(injection_factor_equation hF) hx linear0.
Qed.

(** Source for [injection_factor_kernel_orthogonal_image]:
    Federer 1.7.3, p. 30, the last clause of the construction
    of h: images of kernel vectors under h are perpendicular to
    every vector of im f. Inner products on the kernel are preserved
    by the already specified orthogonality of h. *)
Theorem injection_factor_kernel_orthogonal_image x y :
  f x = 0 -> C (h x) (f y) = 0.
Proof.
move=> hx; have hgx := (proj1 (injection_factor_kernel x)) hx.
rewrite -(injection_factor_equation hF) (injection_factor_orthogonal hF)
  -(injection_factor_symmetric hF) hgx (bil0l (inner_bilinear hB)).
by [].
Qed.
End Kernel.
