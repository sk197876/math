(** Federer (1969), 3.4.12, p. 339, extending 3.4.6, pp. 322–323: consequences
    of the original transverse-space interface. No kernel
    carrier or chosen projection is unfolded. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexWeierstrassTransverseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Splitting.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variable v:X.
Variable xi:Hom X (ComplexScalars.C R)^o.
Variable inclusion:Hom K X.
Variable projection:Hom X K.
Hypothesis hSplit:is_complex_weierstrass_transverse_space NX NK v xi inclusion projection.

(** Source for [complex_weierstrass_inclusion_injective]: inclusion
    identifies the original transverse space with ker(xi),
    3.4.6, p. 322. *)
Lemma complex_weierstrass_inclusion_injective:injective inclusion.
Proof.
move=>x y h;rewrite -(complex_weierstrass_transverse_left_inverse hSplit x)
  -(complex_weierstrass_transverse_left_inverse hSplit y);by rewrite h.
Qed.

(** Source for [complex_weierstrass_projection_direction_zero]: the
    original transverse projection kills v, 3.4.6,
    p. 322. This follows from its exact splitting law. *)
Lemma complex_weierstrass_projection_direction_zero:projection v=0.
Proof.
apply:complex_weierstrass_inclusion_injective.
by rewrite (complex_weierstrass_transverse_projection_equation hSplit)
  (complex_weierstrass_transverse_functional_value hSplit) scale1r subrr linear0.
Qed.

(** Source for [complex_weierstrass_line_functional_coordinate]: the
    original functional maps tv+z to t for transverse z,
    supporting the series uniqueness argument in 3.4.6, p. 323. *)
Lemma complex_weierstrass_line_functional_coordinate t z:xi (t*:v+inclusion z)=t.
Proof.
have hLinear:xi (t*:v+inclusion z)=t*xi v+xi (inclusion z):=hom_linear xi t v (inclusion z).
by rewrite hLinear (complex_weierstrass_transverse_functional_value hSplit)
  (complex_weierstrass_transverse_kernel hSplit) mulr1 addr0.
Qed.

(** Source for [complex_weierstrass_line_transverse_coordinate]: the
    original projection maps tv+z to z, supporting the
    double-sequence uniqueness assertion in 3.4.6, p. 323. *)
Lemma complex_weierstrass_line_transverse_coordinate t z:projection (t*:v+inclusion z)=z.
Proof.
have hLinear:=hom_linear projection t v (inclusion z).
by rewrite hLinear complex_weierstrass_projection_direction_zero
  (complex_weierstrass_transverse_left_inverse hSplit) scaler0 add0r.
Qed.
End Splitting.
