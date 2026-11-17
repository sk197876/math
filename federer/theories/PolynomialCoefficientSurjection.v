(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: lift a polynomial through a
    surjective original coefficient map. Reuse
    finite coefficient support and interpolation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialFiniteSums
  PolynomialCoefficientDivision PolynomialCoefficientMapUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_coefficient_map_surjective]:
    polynomials over the faithful coefficient image
    lift to original coefficient polynomials,
    supporting 3.4.8(8), p. 330. Only
    finitely many original coefficients are chosen;
    no coefficient-map injectivity is assumed. *)
Theorem polynomial_coefficient_map_surjective (A B C D:comNzRingType)
  (embedA:{rmorphism A->B}) (variableA:B) (source:B->nat->A)
  (embedC:{rmorphism C->D}) (variableC:D) (target:D->nat->C)
  (hA:is_commutative_polynomial_ring embedA variableA source)
  (hC:is_commutative_polynomial_ring embedC variableC target)
  (phi:{rmorphism A->C}) (M:{rmorphism B->D}):
  (forall c:C,exists a:A,phi a = c) ->is_polynomial_coefficient_map source target phi M ->
  forall Q:D,exists P:B,M P = Q.
Proof.
move=>hOnto hMap Q.
have [N hSupport]:=@polynomial_coefficients_finite C D embedC variableC target hC Q.
pose choose:=fun c:C=>projT1 (cid (hOnto c)).
have hChoose c:phi (choose c) = c:=projT2 (cid (hOnto c)).
pose f:=fun i=>if (i<N)%N then choose (target Q i) else 0.
have hFinite:exists n,forall i,(n<=i)%N ->f i = 0.
  exists N=>i hI;by rewrite /f ltnNge hI.
have [P hP]:=@polynomial_interpolation_exists A B embedA variableA source hA f hFinite.
exists P;apply:(@polynomial_coefficients_unique C D embedC variableC target hC)=>i.
rewrite hMap hP /f;case:(ltnP i N)=>hI.
- exact:hChoose.
- by rewrite rmorph0 hSupport.
Qed.
