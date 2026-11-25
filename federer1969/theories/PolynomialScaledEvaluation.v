(** Federer (1969), 3.4.8(10), p. 331:
    multiplying a bounded coordinate polynomial
    by a suitable power of delta
    permits substitution of delta times that
    coordinate. Reuse finite polynomial evaluation
    and the original ring power laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialEvaluationUP
  CommutativePolynomialEvaluationLaws CommutativeSubringUP CommutativeSubringLaws PolynomialScalarComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_scaled_evaluation_expression]:
    delta^r times an original bounded
    coordinate polynomial is polynomial in
    delta times that coordinate, supporting
    the original induction in 3.4.8(10),
    p. 331. No inversion of delta,
    domain or nonzero hypothesis is needed. *)
Theorem polynomial_scaled_evaluation_expression (A B C:comNzRingType)
  (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (phi:{rmorphism A->C}) (t:C) (J:{rmorphism B->C}) (delta z:C) (W:B) N:
  is_commutative_polynomial_evaluation embed variable phi t J ->delta*t = z ->
  (forall i,(N<=i)%N ->coefficient W i = 0) ->
  delta^+N*J W = \sum_(i<N) phi (coefficient W i)*delta^+(N-i)*z^+(i:nat).
Proof.
move=>hJ hRelation hSupport.
rewrite (@polynomial_evaluation_finite_expression A B C embed variable coefficient hP
  phi t J hJ W N hSupport) mulr_sumr.
apply:eq_bigr=>i _.
have hPower:delta^+N*t^+(i:nat) = delta^+(N-i)*z^+(i:nat).
  by rewrite -hRelation exprMn mulrA -exprD subnK //;exact:ltnW (ltn_ord i).
by rewrite mulrCA hPower mulrA.
Qed.

(** Source for [polynomial_scaled_subring_representative]:
    delta^r times an original bounded
    polynomial agrees modulo the equation ideal
    with a member of the preceding
    coordinate ring, 3.4.8(10), p. 331.
    Only the exact original coefficient image,
    subring laws and quotient map are used. *)
Theorem polynomial_scaled_subring_representative (A B C D:comNzRingType)
  (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (phi:{rmorphism A->C}) (t:C) (J:{rmorphism B->C})
  (pi:{rmorphism C->D}) (Q:set C) (delta z:C) (W:B) N:
  is_commutative_polynomial_evaluation embed variable phi t J ->
  is_commutative_subring Q ->(forall a:A,Q (phi a)) ->Q delta ->Q z ->
  pi delta*pi t = pi z ->(forall i,(N<=i)%N ->coefficient W i = 0) ->
  exists q:C,Q q /\pi (delta^+N*J W) = pi q.
Proof.
move=>hJ hQ hCoefficients hDelta hZ hRelation hSupport.
pose q:=\sum_(i<N) phi (coefficient W i)*delta^+(N-i)*z^+(i:nat).
have hMember:Q q.
  apply:(commutative_subring_finite_sum hQ)=>i _ _.
  apply:(@commutative_subring_multiply C Q hQ);last exact:(@commutative_subring_power C Q hQ z (i:nat) hZ).
  apply:(@commutative_subring_multiply C Q hQ);first exact:hCoefficients.
  exact:(@commutative_subring_power C Q hQ delta (N-i)%N hDelta).
pose scalar:{rmorphism A->D}:=GRing.RMorphism.clone A D (pi \o phi) _.
pose evaluate:{rmorphism B->D}:=GRing.RMorphism.clone B D (pi \o J) _.
have hEvaluate:=@polynomial_evaluation_after_ring_map A B C D embed variable phi t J pi hJ.
have hScaled:=@polynomial_scaled_evaluation_expression A B D embed variable coefficient hP scalar
  (pi t) evaluate (pi delta) (pi z) W N hEvaluate hRelation hSupport.
exists q;split;first exact:hMember.
rewrite rmorphM rmorphXn.
change ((pi delta)^+N*evaluate W = pi q);rewrite hScaled /q rmorph_sum.
apply:eq_bigr=>i _;by rewrite !rmorphM !rmorphXn.
Qed.
