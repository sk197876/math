(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8), p. 330:
    the original complex linear combination
    of coordinates induces the same combination
    of original coordinate germs. Apply the
    existing finite-sum representative equation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP ScalarRestriction ComplexScalarSealed ComplexNormUP Hom RealNormUP LinearBasis NormFiniteLinearBound
  HolomorphicGermUP HolomorphicGermSealed HolomorphicGermRing HolomorphicGermRingLaws HolomorphicGermRepresentatives
  HolomorphicGermFiniteSum HolomorphicCoordinateGermsExistence HolomorphicCoordinateGermsSealed HolomorphicScalarsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Combination.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable NX:X->R.
Hypothesis hNX:is_complex_norm NX.
Local Notation hNXR:=(complex_norm_real hNX).
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Local Notation P:=(@holomorphic_representative_type R X NX hNXR 0).
Local Notation gamma:=(@HolomorphicCoordinateGerms.value R X NX hNX n e he omega).
Local Notation scalar:=(@HolomorphicScalars.map R X NX hNXR 0).

(** Source for [holomorphic_coordinate_linear_combination_germ]:
    the germ of an actual original
    coordinate combination is its original
    ring sum, 3.4.8(8), p. 330.
    Selected representatives remain local witnesses;
    the opaque germ operations are used
    only through their proved representative equations. *)
Theorem holomorphic_coordinate_linear_combination_germ (T:finType) (index:T->'I_n)
  (c:T->ComplexScalars.C R) (f:P):
  (forall x:X,holomorphic_representative_value f x = \sum_i c i*omega (index i) x) ->
  (holomorphic_germ f:G) = \sum_i scalar (c i)*gamma (index i).
Proof.
move=>hValues.
have hEach i:exists f:P,forall x:X,holomorphic_representative_value f x = omega (index i) x.
  exact:(@holomorphic_coordinate_representative_exists R X NX hNX n e he omega (index i)).
have [F hF]:=choice hEach.
pose term:=fun i:T=>@holomorphic_multiply_representatives R X NX hNXR 0
  (@holomorphic_constant_representative R X NX hNXR 0 (c i)) (F i).
have hTerms i:(holomorphic_germ (term i):G) = scalar (c i)*gamma (index i).
  rewrite -(holomorphic_germ_multiply_equation (@HolomorphicGerms.laws R X NX hNXR 0)).
  by rewrite -(@HolomorphicScalars.laws R X NX hNXR 0 (c i))
    (@HolomorphicCoordinateGerms.laws R X NX hNX n e he omega (index i) (F i) (hF i)).
have hSum:forall x:X,holomorphic_representative_value f x =
    \sum_(g<-map term (enum T)) holomorphic_representative_value g x.
  move=>x;rewrite hValues big_map -big_enum.
  apply:eq_bigr=>i _;change (c i*omega (index i) x = c i*holomorphic_representative_value (F i) x).
  by rewrite hF.
rewrite (@holomorphic_germ_finite_sum_equation R X NX hNXR 0 (map term (enum T)) f hSum) big_map -big_enum.
apply:eq_bigr=>i _;exact:hTerms.
Qed.
End Combination.
