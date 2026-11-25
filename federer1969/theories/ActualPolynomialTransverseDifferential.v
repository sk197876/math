(** Federer (1969), 3.4.8(10), p. 331:
    transfer the existing finite-polynomial differential
    to an actual representative with the
    same original coefficient expression. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal NormAnalyticUP
  AnalyticPrefixPolynomialDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [actual_polynomial_transverse_differential]:
    the bounded numerator t_j has its
    actual transverse differential, supporting the
    original equation differentials in 3.4.8(10), p. 331. *)
Theorem actual_polynomial_transverse_differential (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:Y->Prop) (P:Hom X Y) (xi:Hom X R^o) N (b:'I_N->Y->R) (f:X->R):
  (forall y,U y ->norm_domain_interior NY U y) ->
  norm_bounded_linear NX NY P ->norm_bounded_linear NX (fun t:R^o=>`|t|) xi ->
  (forall i,@norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY (@scalar_absolute_value_norm R) U (b i)) ->
  (forall x,f x = \sum_(i<N) b i (P x)*(xi x)^+(i:nat)) ->
  forall a,U (P a) ->exists L:Hom X R^o,
    has_norm_differential NX (fun t:R^o=>`|t|) (fun x=>U (P x)) f a L /\
    forall v,P v = 0 ->L v = (\sum_(i<N) (i:nat)%:R*b i (P a)*(xi a)^+(i:nat).-1)*xi v.
Proof.
move=>hInterior hP hXi hB hValues a ha.
have [L [hL hDirections]]:=(@analytic_prefix_polynomial_differential R X Y NX NY hNX hNY
  U P xi N b hInterior hP hXi hB).2.2 a ha.
exists L;split;last exact:hDirections.
apply:(norm_differential_domain_agreement hNX _ hL)=>x _;exact:esym (hValues x).
Qed.
