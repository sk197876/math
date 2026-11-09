(** Federer (1969), 3.4.5, p. 321: the actual
    real cubic cone determines every polynomial remainder
    of degree below three in its first coordinate.
    This supports the example cited to Cartan (1957), pp. 97–99. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct EuclideanCoordinateTopology
  PolynomialFunctions PolynomialRepresentations EuclideanPolynomialSlices EuclideanPolynomialPowerSlices
  CubicConeRemainderInjective PolynomialLineHalfRay.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Remainder.
Variable R:realType.
Local Notation Y:=(R_n R 2).
Local Notation point y w:=(y*:(@coordinate_basis R 2 ord0)+w*:(@coordinate_basis R 2 ord_max)).
Local Notation line w:=([ffun _:'I_1=>w]).

(** Source for [cubic_cone_polynomial_remainder_zero]:
    vanishing on the actual rational real cone forces
    every original polynomial remainder coefficient to vanish,
    supporting the example in 3.4.5, p. 321. The
    zero axis coordinate is included by actual polynomial uniqueness. *)
Theorem cubic_cone_polynomial_remainder_zero (P:'I_3->PolynomialFunction Y R^o):
  (forall s t:R,\sum_(i<3) (s*(1+t^+2))^+i*
    P i (point (s*t*(1+t^+2)) s)=0) ->
  forall i (v:Y),P i v=0.
Proof.
move=>hCone.
pose n i:=(polynomial_degree (P i)).+1.
pose M:=(\sum_(i<3) n i).+1.
pose a (i:'I_3) (j:nat) (w:R):=
  if (j<n i)%N then euclidean_polynomial_coefficient (P i) j (line w) else 0.
have hBound i:(n i<=M)%N.
  rewrite /M;apply:leq_trans _ (leqnSn _).
  by rewrite (bigD1 i) //= leq_addr.
have hValue i (y w:R):P i (point y w)=\sum_(j<M) a i j w*y^+j.
  rewrite euclidean_polynomial_slice_sum.
  have hHead:(point y w) ord0=y.
    rewrite /coordinate_basis !ffunE /=.
    change (y*1+w*0=y);by rewrite mulr1 mulr0 addr0.
  have hTail:coordinate_tail (point y w)=line w.
    apply/ffunP=>j;rewrite (ord1 j) /coordinate_tail /coordinate_basis !ffunE /=.
    change (y*0+w*1=w);by rewrite mulr0 mulr1 add0r.
  rewrite hHead hTail (big_ord_widen M
    (fun j=>y^+j*euclidean_polynomial_coefficient (P i) j (line w)) (hBound i)) big_mkcond.
  apply:eq_bigr=>j _;rewrite /a.
  by case:(j<n i)%N;rewrite ?mul0r // mulrC.
have hNonzero (s:R) (hs:s!=0) (i:'I_3) (j:'I_M):a i j s=0.
  pose b (i:'I_3) (j:'I_M):R^o:=s^+(i+j)*a i j s.
  have hParam t:(\sum_(i<3) \sum_(j<M)
      ((1+t^+2)^+i*(t*(1+t^+2))^+j)*:b i j)=0.
    rewrite -[RHS](hCone s t).
    under [RHS]eq_bigr do rewrite hValue mulr_sumr.
    apply:eq_bigr=>ii _;apply:eq_bigr=>jj _.
    change ((1+t^+2)^+ii*(t*(1+t^+2))^+jj*b ii jj=
      (s*(1+t^+2))^+ii*(a ii jj s*(s*t*(1+t^+2))^+jj)).
    rewrite /b !exprMn exprD;ring.
  have hZero:=@cubic_cone_remainder_injective R (@pchar_num R) R^o M b hParam i j.
  have hPower:s^+(i+j)!=0:=expf_neq0 _ hs.
  by move/eqP:hZero;rewrite /b mulf_eq0 (negbTE hPower) /= =>/eqP.
have hNonzeroValue (s:R) (hs:s!=0) i (y:R):P i (point y s)=0.
  rewrite hValue;apply:big1=>j _;by rewrite (hNonzero s hs i j) mul0r.
move=>i v.
pose y:=v ord0.
pose w:=v ord_max.
have hCoordinates:v=point y w.
  have h:=@euclidean_coordinate_expansion R 2 v.
  rewrite big_ord_recl big_ord1 in h.
  have hIndex:lift (ord0:'I_2) (ord0:'I_1)=(ord_max:'I_2) by apply:val_inj.
  rewrite hIndex in h.
  exact:esym h.
rewrite hCoordinates;case hW:(w==0).
- have hZeroW:w=0:=eqP hW;rewrite hZeroW.
  have hEndpoint:=@polynomial_positive_half_ray_endpoint R Y R^o (P i)
    (y*:(@coordinate_basis R 2 ord0)) (@coordinate_basis R 2 ord_max).
  have hAtZero:P i (y*:(@coordinate_basis R 2 ord0))=0.
    apply:hEndpoint=>t ht.
    have htNonzero:t!=0 by rewrite gt_eqF.
    exact:(hNonzeroValue t htNonzero i y).
  by rewrite scale0r addr0.
- exact:(hNonzeroValue w (negbT hW) i y).
Qed.
End Remainder.
