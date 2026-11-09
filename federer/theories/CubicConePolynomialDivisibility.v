(** Federer (1969), 3.4.5, p. 321: finite
    real polynomial divisibility for the actual cubic cone,
    supporting the example cited to Cartan (1957), pp. 97–99.
    This is proved by monic division and actual real evaluations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  PolynomialFunctions PolynomialRepresentations PolynomialComposition PolynomialLinearComposition
  PolynomialCoefficientUniqueness EuclideanCoordinateSplit EuclideanPolynomialSlices
  FiniteMonicPolynomialDivision PolynomialCoefficientMonicDivision ScalarPolynomialAlgebraSupport
  EuclideanCoordinatePolynomialPowers CubicConePolynomialRemainder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CubicDivision.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation Y:=(R_n R 2).
Local Notation point y w:=(y*:(@coordinate_basis R 2 ord0)+w*:(@coordinate_basis R 2 ord_max)).

(** Source for [cubic_cone_polynomial_value]: the actual
    homogeneous cubic after the analytic axis coordinate
    change in the counterexample argument supporting
    3.4.5, p. 321. *)
Definition cubic_cone_polynomial_value (v:X):R:=
  (coordinate_head v)^+3-(coordinate_tail v) ord_max*
    ((coordinate_head v)^+2+((coordinate_tail v) ord0)^+2).

(** Source for [rational_cubic_cone_polynomial_divisible]:
    an actual polynomial vanishing on the real rational
    cubic cone is a polynomial multiple of its original
    equation, supporting the example cited in 3.4.5,
    p. 321. No complex zero set or division
    identity is assumed. *)
Theorem rational_cubic_cone_polynomial_divisible (P:PolynomialFunction X R^o):
  (forall s t:R,P (euclidean_join (point (s*t*(1+t^+2)) s,s*(1+t^+2)))=0) ->
  exists Q:PolynomialFunction X R^o,forall v:X,
    P v=Q v*cubic_cone_polynomial_value v.
Proof.
move=>hCone.
pose d:=fun i:nat=>fun y:Y=>if (i==0)%N then -(y ord_max*(y ord0)^+2)
  else if (i==2)%N then -y ord_max else 0.
pose s:seq (Y->R):=[seq euclidean_polynomial_coefficient P i|
  i<-iota 0 (polynomial_degree P).+1].
have hDivisor i:@is_polynomial_function R Y R^o (d i).
  have hZero:=@composition_polynomial_constant R Y R^o 0.
  have hW:=@euclidean_coordinate_polynomial R 2 ord_max.
  have hSquare:=@euclidean_coordinate_power_polynomial R 2 ord0 2%N.
  rewrite /d;case:(i==0)%N.
  - have [F hF]:=real_polynomial_subtract hZero (real_polynomial_multiply hW hSquare).
    exists F=>y;by rewrite -hF sub0r.
  - case:(i==2)%N;last exact:hZero.
    have [F hF]:=real_polynomial_subtract hZero hW.
    exists F=>y;by rewrite -hF sub0r.
have hCoefficients:forall c,c \in s ->@is_polynomial_function R Y R^o c.
  move=>c /mapP [i hi ->].
  exact:(@euclidean_polynomial_coefficient_polynomial R 2 P i).
have [q [r [hQ [hR hDivision]]]]:=@finite_polynomial_coefficient_monic_division R Y
  3%N d s (isT:(0<3)%N) hDivisor hCoefficients.
have hSource (y:Y) (x:R):finite_ring_polynomial_value [seq a y|a<-s] x=
    P (euclidean_join (y,x)).
  rewrite /s -map_comp /comp.
  change (coefficient_polynomial_value (euclidean_polynomial_coefficients P y) x=
    P (euclidean_join (y,x))).
  exact:(@euclidean_polynomial_slice_value R 2 P y x).
have hDivisorValue (y:Y) (x:R):x^+3+\sum_(i<3) d i y*x^+i=
    x^+3-y ord_max*(x^+2+(y ord0)^+2).
  rewrite !big_ord_recl big_ord0 /= /d /= expr0 expr1;ring.
pose RP i:=@PolynomialMap R Y R^o (r i) (introT (asboolP _) (hR i)).
have hRationalRemainder s0 t:(\sum_(i<3) (s0*(1+t^+2))^+i*
    RP i (point (s0*t*(1+t^+2)) s0))=0.
  pose y:=point (s0*t*(1+t^+2)) s0.
  pose x:=s0*(1+t^+2).
  have hYHead:y ord0=s0*t*(1+t^+2).
    rewrite /y /coordinate_basis !ffunE /=.
    change ((s0*t*(1+t^+2))*1+s0*0=s0*t*(1+t^+2)).
    by rewrite mulr1 mulr0 addr0.
  have hYLast:y ord_max=s0.
    rewrite /y /coordinate_basis !ffunE /=.
    change ((s0*t*(1+t^+2))*0+s0*1=s0).
    by rewrite mulr0 mulr1 add0r.
  have hZero:x^+3-y ord_max*(x^+2+(y ord0)^+2)=0.
    rewrite hYHead hYLast /x !exprMn;ring.
  have hActual:=hDivision y x.
  rewrite hSource hDivisorValue hZero mulr0 add0r in hActual.
  have hOriginal:P (euclidean_join (y,x))=0:=hCone s0 t.
  have hSum:(\sum_(i<3) r i y*x^+i)=0:=eq_trans (esym hActual) hOriginal.
  rewrite -[RHS]hSum;apply:eq_bigr=>i _.
  change (x^+i*r i y=r i y*x^+i);exact:mulrC.
have hRemainderZero (i:'I_3) (y:Y):r i y=0.
  exact:(@cubic_cone_polynomial_remainder_zero R (fun i=>RP i) hRationalRemainder i y).
pose qOnX:seq (X->R):=[seq (fun v:X=>a (coordinate_tail v))|a<-q].
have hQOnX:forall c,c \in qOnX ->@is_polynomial_function R X R^o c.
  move=>c /mapP [a ha ->].
  exact:(@polynomial_linear_precompose R X Y R^o
    (GRing.Linear.clone R X Y *:%R (@coordinate_tail R 2) _) a (hQ a ha)).
have hHead:=@euclidean_coordinate_polynomial R 3 ord0.
have [F hF]:=@real_polynomial_coefficient_horner R X (fun v=>v ord0) qOnX hHead hQOnX.
have hPolynomial:@is_polynomial_function R X R^o
    (fun v=>finite_ring_polynomial_value [seq a (coordinate_tail v)|a<-q] (coordinate_head v)).
  exists F=>v;rewrite -hF /qOnX -map_comp /comp.
  reflexivity.
exists (@PolynomialMap R X R^o _ (introT (asboolP _) hPolynomial))=>v.
have hActual:=hDivision (coordinate_tail v) (coordinate_head v).
rewrite hSource hDivisorValue -/(euclidean_split v) euclidean_splitK in hActual.
have hRemaining:(\sum_(i<3) r i (coordinate_tail v)*(coordinate_head v)^+i)=0.
  apply:big1=>i _;by rewrite hRemainderZero mul0r.
by rewrite hRemaining addr0 in hActual.
Qed.
End CubicDivision.
