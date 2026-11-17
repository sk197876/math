(** Supporting algebra for Federer (1969), 3.4.8(5), p. 328:
    the original local vanishing ideal passes to any quotient by
    an ideal contained in it. Use exact original kernels, surjection
    and image laws; no residue-ring or quotient-unit property is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeQuotientUP
  CommutativeFactorizationUP CommutativePrimeTransport AnalyticRotatedIdealUP AnalyticIdealImageLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [quotient_local_ideal_image]: supporting original
    local quotient for Federer 3.4.8(5), p. 328. The image of an
    original proper ideal containing the quotient kernel is proper;
    one-minus units descend through the actual quotient map. *)
Theorem quotient_local_ideal_image (A C:comNzRingType) (pi:{rmorphism A->C})
    (I M:set A) (N:set C):
  is_commutative_ideal_quotient I pi ->is_analytic_ideal_image pi M N ->
  is_commutative_ideal M ->~M 1 ->I `<=` M ->
  (forall a:A,M a ->is_commutative_unit (1-a)) ->
  is_commutative_ideal N /\~N 1 /\forall c:C,N c ->is_commutative_unit (1-c).
Proof.
move=>hPi hImage hM hProper hIM hUnit.
split.
- exact:(@analytic_ideal_image_ideal A C pi M N hImage
    (commutative_quotient_surjective hPi) hM).
- split.
  + move=>hOneImage;have [a [ha hA]]:=(hImage 1).1 hOneImage.
    have hDifference:I (a-1).
      apply:(commutative_quotient_kernel hPi _).1;by rewrite rmorphB hA rmorph1 subrr.
    have hNeg:M (-(a-1)):=commutative_ideal_opp hM (hIM _ hDifference).
    have hOne:=@commutative_ideal_add A M hM a (-(a-1)) ha hNeg.
    rewrite opprB addrCA subrr addr0 in hOne;exact:hProper hOne.
  + move=>c /(hImage c).1 [a [ha <-]].
    have hh:=@commutative_ring_map_unit A C pi (1-a) (hUnit a ha).
    by rewrite rmorphB rmorph1 in hh.
Qed.
