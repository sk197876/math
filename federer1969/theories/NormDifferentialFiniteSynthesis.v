(** Federer (1969), 3.4.8(10), pp. 331–332:
    the differential of the joint equation
    map is assembled from the actual
    scalar equation differentials. Apply the
    existing finite-sum and linear postcomposition rules. *)
From mathcomp Require Import all_boot all_order all_algebra reals functions.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal
  NormHigherCurveDerivativeUP NormedPrimitiveCell NormDifferentialFiniteCalculus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_finite_synthesis]:
    assembling the actual finite equation
    differential preserves its pointwise coordinate
    formula, 3.4.8(10), pp. 331–332.
    The vectors and both normed spaces
    are arbitrary; the empty family remains. *)
Theorem norm_differential_finite_synthesis (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) a (index:finType) (v:index->Y) (f:index->X->R) (D:index->Hom X R^o):
  norm_domain_interior NX A a ->
  (forall i,has_norm_differential NX (fun t:R^o=>`|t|) A (f i) a (D i)) ->
  exists L:Hom X Y,
    has_norm_differential NX NY A (fun x=>\sum_i f i x*:v i) a L /\
    forall u,L u = \sum_i D i u*:v i.
Proof.
move=>hA hF.
pose maps i:=hom_comp (scalar_coefficient_linear_map (v i)) (D i).
have hTerm i:has_norm_differential NX NY A (fun x=>f i x*:v i) a (maps i).
  exact:(@norm_differential_postcompose R X R^o Y NX (fun t:R^o=>`|t|) NY hNX A
    (f i) a (D i) (scalar_coefficient_linear_map (v i)) (hF i)
    (scalar_coefficient_linear_bound hNY (v i))).
pose L:=\sum_i maps i.
exists L;split.
- have hSum:=@norm_differential_finite_sum R X Y NX NY hNX hNY A a index predT
    (fun i x=>f i x*:v i) maps hA (fun i _=>hTerm i).
  apply:(norm_differential_domain_agreement hNX _ hSum)=>x _.
  by elim/big_rec2:_=>[|i c g _ <-].
- move=>u;rewrite /L.
  have hValue:(\sum_i maps i) u = \sum_i maps i u.
    by elim/big_rec2:_=>[|i c g _ <-];rewrite ?hom_addE ?hom_zeroE.
  rewrite hValue;apply:eq_bigr=>i _;by rewrite /maps hom_compE.
Qed.
