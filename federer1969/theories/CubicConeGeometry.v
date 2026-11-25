(** Federer (1969), 3.4.5, p. 321: the actual
    homogeneous real cubic cone in the real Taylor proof
    of the example cited to Cartan (1957), pp. 97–99.
    Its equations and parametrized points are proved directly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCoordinateSplit PolynomialFunctions PolynomialLinearComposition EuclideanCoordinatePolynomialPowers
  ScalarPolynomialAlgebraSupport CubicConePolynomialDivisibility.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Geometry.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation Y:=(R_n R 2).
Local Notation point y w:=(y*:(@coordinate_basis R 2 ord0)+w*:(@coordinate_basis R 2 ord_max)).

(** Source for [cubic_cone_homogeneous]: the actual
    defining cubic is homogeneous of degree three,
    supporting the example in 3.4.5, p. 321. *)
Lemma cubic_cone_homogeneous (t:R) (v:X):
  cubic_cone_polynomial_value (t*:v)=t^+3*cubic_cone_polynomial_value v.
Proof.
rewrite /cubic_cone_polynomial_value /coordinate_head /coordinate_tail !ffunE.
change ((t*v ord0)^+3-(t*v (lift ord0 ord_max))*
  ((t*v ord0)^+2+(t*v (lift ord0 ord0))^+2)=
  t^+3*((v ord0)^+3-v (lift ord0 ord_max)*((v ord0)^+2+(v (lift ord0 ord0))^+2))).
rewrite !exprMn;ring.
Qed.

(** Source for [cubic_cone_rational_point]: every actual
    real point of the rational parametrization belongs
    to the original cubic cone, supporting 3.4.5, p. 321. *)
Lemma cubic_cone_rational_point (s t:R):
  cubic_cone_polynomial_value
    (euclidean_join (point (s*t*(1+t^+2)) s,s*(1+t^+2)))=0.
Proof.
pose y:=point (s*t*(1+t^+2)) s.
pose x:=s*(1+t^+2).
have hSplit:=@euclidean_joinK R 2 (y,x).
have hTail:coordinate_tail (euclidean_join (y,x))=y:=congr1 fst hSplit.
have hHead:coordinate_head (euclidean_join (y,x))=x:=congr1 snd hSplit.
have hYHead:y ord0=s*t*(1+t^+2).
  rewrite /y /coordinate_basis !ffunE /=.
  change ((s*t*(1+t^+2))*1+s*0=s*t*(1+t^+2)).
  by rewrite mulr1 mulr0 addr0.
have hYLast:y ord_max=s.
  rewrite /y /coordinate_basis !ffunE /=.
  change ((s*t*(1+t^+2))*0+s*1=s).
  by rewrite mulr0 mulr1 add0r.
change (cubic_cone_polynomial_value (euclidean_join (y,x))=0).
rewrite /cubic_cone_polynomial_value hTail hHead hYHead hYLast /x !exprMn;ring.
Qed.

(** Source for [cubic_cone_defining_polynomial]: the actual
    equation remains a polynomial in the original
    symmetric-form sense, supporting 3.4.5, p. 321. *)
Lemma cubic_cone_defining_polynomial:
  @is_polynomial_function R X R^o (@cubic_cone_polynomial_value R).
Proof.
have hX:=@euclidean_coordinate_polynomial R 3 ord0.
have hY:=@polynomial_linear_precompose R X Y R^o
  (GRing.Linear.clone R X Y *:%R (@coordinate_tail R 2) _)
  (fun y=>y ord0) (@euclidean_coordinate_polynomial R 2 ord0).
have hZ:=@polynomial_linear_precompose R X Y R^o
  (GRing.Linear.clone R X Y *:%R (@coordinate_tail R 2) _)
  (fun y=>y ord_max) (@euclidean_coordinate_polynomial R 2 ord_max).
exact:(real_polynomial_subtract (real_polynomial_power 3%N hX)
  (real_polynomial_multiply hZ (real_polynomial_add (real_polynomial_power 2%N hX)
    (real_polynomial_power 2%N hY)))).
Qed.

(** Source for [cubic_cone_equation_nonzero]: the unit
    first-coordinate vector lies outside the actual cone,
    supporting the polynomial division in 3.4.5, p. 321. *)
Lemma cubic_cone_equation_nonzero:
  cubic_cone_polynomial_value (@coordinate_basis R 3 ord0)= 1.
Proof.
rewrite /cubic_cone_polynomial_value /coordinate_head /coordinate_tail /coordinate_basis !ffunE /=.
ring.
Qed.
End Geometry.
