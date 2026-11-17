(** Federer (1969), 3.4.8(10), pp. 331–332:
    assemble the actual scalar equations into
    a finite-dimensional analytic coordinate map.
    Apply the existing bounded-linear composition,
    constant and addition laws from 3.1.24, p. 240. *)
From mathcomp Require Import all_boot all_order all_algebra reals functions.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormHigherCurveDerivativeUP NormedPrimitiveCell
  NormAnalyticUP NormAnalyticConstant NormAnalyticLinear NormAnalyticOperations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_analytic_finite_synthesis]:
    finite original analytic coordinates give
    the joint analytic map used to
    straighten the equation system, 3.4.8(10),
    pp. 331–332. The target vectors
    and both normed spaces are arbitrary;
    the empty family is the zero map. *)
Theorem norm_analytic_finite_synthesis (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (index:finType) (v:index->Y) (f:index->X->R):
  (forall x,A x ->norm_domain_interior NX A x) ->
  (forall i,@norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R) A (f i)) ->
  @norm_analytic R X Y NX NY hNX hNY A (fun x=>\sum_i f i x*:v i).
Proof.
move=>hA hF.
pose term i:=fun x=>f i x*:v i.
have hTerm i:@norm_analytic R X Y NX NY hNX hNY A (term i).
  have hCoefficient:=@norm_bounded_linear_analytic R R^o Y (fun t:R^o=>`|t|) NY
    (@scalar_absolute_value_norm R) hNY (fun _=>True)
    (fun x _=>norm_full_domain_interior (fun t:R^o=>`|t|) x)
    (scalar_coefficient_linear_map (v i)) (scalar_coefficient_linear_bound hNY (v i)).
  exact:(@norm_analytic_compose_on R X R^o Y NX (fun t:R^o=>`|t|) NY hNX
    (@scalar_absolute_value_norm R) hNY A (fun _=>True) (f i)
    (scalar_coefficient_linear_map (v i)) (fun x _=>I) (hF i) hCoefficient).
have hSum:@norm_analytic R X Y NX NY hNX hNY A (\sum_i term i).
  elim/big_ind:_=>[|g h hg hh|i _].
  - exact:(@norm_constant_analytic R X Y NX NY hNX hNY A hA 0).
  - exact:norm_analytic_add hg hh.
  - exact:hTerm.
apply:(@norm_analytic_domain_agreement R X Y NX NY hNX hNY A _ _ _ hSum)=>x _.
by elim/big_rec2:_=>[|i c g _ <-].
Qed.
