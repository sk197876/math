(** Federer (1969), 3.4.8(10), p. 331:
    differentiate the original polynomial equations
    in the last-coordinate direction. The
    original prefix coefficients are constant
    in that direction. Apply the existing
    product and finite-sum differential rules. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialLocal NormDifferentialFiniteCalculus NormDifferentialScalarProduct
  ScalarPowerDifferentialComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_polynomial_directional_differential]:
    the actual directional derivative of the
    finite original polynomial expression, supporting
    3.4.8(10), p. 331. The coefficient
    differentials vanish on the prescribed direction,
    and the actual coordinate differential is retained.
    These pointwise equations supply the printed
    polynomial derivative without new calculus arguments. *)
Theorem finite_polynomial_directional_differential (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) (A:X->Prop) (a v:X) N
  (f:'I_N->X->R) (D:'I_N->Hom X R^o) (xi:Hom X R^o):
  norm_domain_interior NX A a ->norm_bounded_linear NX (fun t:R^o=>`|t|) xi ->
  (forall i,has_norm_differential NX (fun t:R^o=>`|t|) A (f i) a (D i)) ->
  (forall i,D i v = 0) ->
  exists L:Hom X R^o,
    has_norm_differential NX (fun t:R^o=>`|t|) A
      (fun x=>\sum_(i<N) f i x*(xi x)^+(i:nat)) a L /\
    L v = (\sum_(i<N) (i:nat)%:R*f i a*(xi a)^+(i:nat).-1)*xi v.
Proof.
move=>hInterior hXi hF hZero.
have hXiD:=@norm_differential_linear R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) A a xi hInterior hXi.
pose power:=fun i:'I_N=>((i:nat)%:R*(xi a)^+(i:nat).-1)*:xi.
pose term:=fun i:'I_N=>scalar_vector_product_linear_term (f i a) ((xi a)^+(i:nat)) (D i) (power i).
have hTerm i:has_norm_differential NX (fun t:R^o=>`|t|) A
    (fun x=>f i x*(xi x)^+(i:nat)) a (term i).
  have hPower:=@norm_scalar_power_differential_composition R X NX hNX A xi a xi (i:nat) hXiD.
  exact:(@norm_differential_scalar_product R X R^o NX (fun t:R^o=>`|t|) hNX
    (@scalar_absolute_value_norm R) A (f i) (fun x=>(xi x)^+(i:nat)) a (D i) (power i) (hF i) hPower).
pose L:=\sum_(i<N) term i.
exists L;split.
- have hSum:=@norm_differential_finite_sum R X R^o NX (fun t:R^o=>`|t|) hNX
    (@scalar_absolute_value_norm R) A a [the finType of 'I_N] predT
    (fun i x=>f i x*(xi x)^+(i:nat)) term hInterior (fun i _=>hTerm i).
  apply:(@norm_differential_domain_agreement R X R^o NX (fun t:R^o=>`|t|) hNX A _ _ a L _ hSum)=>x _.
  by elim/big_rec2:_=>[|i c g _ <-].
- have hEvaluation:L v = \sum_(i<N) term i v.
    rewrite /L;by elim/big_rec2:_=>[|i c g _ <-];rewrite ?hom_addE ?hom_zeroE.
  rewrite hEvaluation mulr_suml;apply:eq_bigr=>i _.
  rewrite /term /scalar_vector_product_linear_term hom_addE hom_compE hom_scaleE hZero.
  change (0*(xi a)^+(i:nat)+f i a*((power i) v) =
    ((i:nat)%:R*f i a*(xi a)^+(i:nat).-1)*xi v).
  rewrite /power hom_scaleE.
  change (0*(xi a)^+(i:nat)+f i a*((i:nat)%:R*(xi a)^+(i:nat).-1*xi v) =
    ((i:nat)%:R*f i a*(xi a)^+(i:nat).-1)*xi v).
  ring.
Qed.
