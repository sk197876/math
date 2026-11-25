(** Federer (1969), 3.4.8(8), p. 330:
    the original real linear combination
    of coordinates induces the same combination
    of original coordinate germs. Apply the
    existing finite-sum representative equation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis NormFiniteLinearBound
  AnalyticGermUP AnalyticGermSealed AnalyticGermRing AnalyticGermRingLaws AnalyticGermRepresentatives
  AnalyticGermFiniteSum PointedFunctionalGermExistence AnalyticCoordinateGermsSealed AnalyticScalarsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Combination.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation P:=(@analytic_representative_type R X NX hNX 0).
Local Notation gamma:=(@AnalyticCoordinateGerms.value R X NX hNX n e he omega).
Local Notation scalar:=(@AnalyticScalars.map R X NX hNX 0).

(** Source for [analytic_coordinate_linear_combination_germ]:
    the germ of an actual original
    coordinate combination is its original
    ring sum, 3.4.8(8), p. 330.
    Selected representatives remain local witnesses;
    the opaque germ operations are used
    only through their proved representative equations. *)
Theorem analytic_coordinate_linear_combination_germ (T:finType) (index:T->'I_n)
  (c:T->R) (f:P):
  (forall x:X,analytic_representative_value f x = \sum_i c i*omega (index i) x) ->
  (analytic_germ f:G) = \sum_i scalar (c i)*gamma (index i).
Proof.
move=>hValues.
have hEach i:exists f:P,forall x:X,analytic_representative_value f x = omega (index i) x.
  have hBound:=@norm_finite_linear_bounded R X R^o NX (fun t:R^o=>`|t|) hNX
    (@scalar_absolute_value_norm R) n e he (omega (index i)).
  have [f0 hF0]:=@pointed_functional_representative_exists R X NX hNX 0 (omega (index i)) hBound.
  exists f0=>x;by rewrite hF0 subr0.
have [F hF]:=choice hEach.
pose term:=fun i:T=>@analytic_multiply_representatives R X NX hNX 0
  (@analytic_constant_representative R X NX hNX 0 (c i)) (F i).
have hTerms i:(analytic_germ (term i):G) = scalar (c i)*gamma (index i).
  rewrite -(analytic_germ_multiply_equation (@AnalyticGerms.laws R X NX hNX 0)).
  by rewrite -(@AnalyticScalars.laws R X NX hNX 0 (c i))
    (@AnalyticCoordinateGerms.laws R X NX hNX n e he omega (index i) (F i) (hF i)).
have hSum:forall x:X,analytic_representative_value f x =
    \sum_(g<-map term (enum T)) analytic_representative_value g x.
  move=>x;rewrite hValues big_map -big_enum.
  apply:eq_bigr=>i _;change (c i*omega (index i) x = c i*analytic_representative_value (F i) x).
  by rewrite hF.
rewrite (@analytic_germ_finite_sum_equation R X NX hNX 0 (map term (enum T)) f hSum) big_map -big_enum.
apply:eq_bigr=>i _;exact:hTerms.
Qed.
End Combination.
