(** Federer (1969), 3.4.5, p. 321: an actual
    finite polynomial of x degree below three cannot
    vanish on the rational cubic cone unless it is zero.
    This supports the cited example of Cartan (1957), pp. 97–99. *)
From mathcomp Require Import all_boot all_order all_algebra ring.
From Federer Require Import ShiftedQuadraticPolynomial CubicConeParametrizationDegrees.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [cubic_cone_remainder_injective]: the
    rational substitution x=1+t^2, y=t*(1+t^2), z=1
    determines every original coefficient of a homogeneous
    remainder of x degree below three, supporting the
    example cited in 3.4.5, p. 321. *)
Theorem cubic_cone_remainder_injective (K:fieldType) (h0:[pchar K]=i pred0)
    (V:lmodType K) M (a:'I_3->'I_M->V):
  (forall t:K,\sum_(i<3) \sum_(j<M)
    ((1+t^+2)^+i*(t*(1+t^+2))^+j)*:a i j=0) ->
  forall i j,a i j=0.
Proof.
move=>hValues.
pose I:=[the finType of ('I_3*'I_M)%type].
pose indexJ:=fun p:I=>(p.2:nat).
pose indexM:=fun p:I=>(p.1+p.2)%N.
pose c:=fun p:I=>a p.1 p.2.
have hDegree p:(indexJ p+2 * indexM p)%N=(2 * p.1+3 * p.2)%N.
  by rewrite /indexJ /indexM mulnDr addnCA -mulSn.
have hInjective:injective (fun p:I=>(indexJ p+2 * indexM p)%N).
  move=>p q hEqual;apply:(@cubic_cone_remainder_degrees_injective M p q).
  by rewrite -!hDegree.
have hBound p:(indexJ p+2 * indexM p<(2 * 3+3 * M).+1)%N.
  rewrite hDegree ltnS;apply:leq_add.
  - rewrite leq_mul2l /=;exact:ltnW (ltn_ord p.1).
  - rewrite leq_mul2l /=;exact:ltnW (ltn_ord p.2).
have hParam t:(\sum_(p:I) (t^+(indexJ p)*(1+t^+2)^+(indexM p))*:c p)=0.
  rewrite /indexJ /indexM /c /I.
  rewrite -(pair_bigA +%R (fun (i:'I_3) (j:'I_M)=>
    (t^+j*(1+t^+2)^+(i+j))*:a i j)).
  rewrite -[RHS](hValues t);apply:eq_bigr=>i _;apply:eq_bigr=>j _.
  rewrite /= exprMn exprD.
  congr (_*:a i j);ring.
have hAll:=@shifted_quadratic_polynomials_independent K h0 V I indexJ indexM c
  (2 * 3+3 * M).+1 hInjective hBound hParam.
move=>i j;exact:(hAll (i,j)).
Qed.
