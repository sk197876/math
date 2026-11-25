(** Federer (1969), 3.4.5, p. 321, used in
    3.4.8(12), p. 327: assemble the original defining
    equations into one analytic Euclidean map. The finite
    analytic sum and bounded linear composition laws of
    3.1.24, p. 240, suffice, including an empty family. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals functions.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness EuclideanCoordinateTopology
  NormDifferentialUP NormAnalyticUP NormAnalyticOperations NormAnalyticLinear
  NormAnalyticConstant NormRegularityLinearMaps NormHigherCurveDerivativeUP NormOpenDomainLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_scalar_assembly_analytic]: bundle the
    equations in the functional analytic submanifold definition,
    3.4.5, p. 321, for the analytic coordinates
    used in 3.4.8(12), pp. 327, 335. *)
Theorem euclidean_scalar_assembly_analytic (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:set X) m (F:'I_m->X->R^o):
  (forall x,A x ->norm_domain_interior NX A x) ->
  (forall i,@norm_analytic R X R^o NX (fun t:R^o=>`|t|)
    hNX (@scalar_absolute_value_norm R) A (F i)) ->
  @norm_analytic R X (R_n R m) NX (inner_norm (@euclidean_inner_productP R m))
    hNX (inner_norm_real_norm (@euclidean_inner_productP R m)) A
    (fun x=>[ffun i=>F i x]).
Proof.
move=>hA hF.
pose Y:=R_n R m.
pose NY:=inner_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose e:=@coordinate_basis R m.
pose L i:=@scalar_coefficient_linear_map R Y (e i).
have hBound i:norm_bounded_linear (fun t:R^o=>`|t|) NY (L i).
  exists (NY (e i));split;first exact:real_seminorm_nonnegative hNY.1 (e i).
  move=>t;change (is_true (NY (t*:e i)<=NY (e i)*`|t|)).
  by rewrite /NY (real_seminorm_scale hNY.1) mulrC.
have hTerm i:@norm_analytic R X Y NX NY hNX hNY A (fun x=>L i (F i x)).
  apply:(@norm_analytic_compose_on R X R^o Y NX (fun t:R^o=>`|t|) NY
    hNX (@scalar_absolute_value_norm R) hNY A setT (F i) (L i)
    (fun x hx=>Logic.I) (hF i)).
  exact:(@norm_bounded_linear_analytic R R^o Y (fun t:R^o=>`|t|) NY
    (@scalar_absolute_value_norm R) hNY setT
    (fun t ht=>@norm_full_domain_interior R R^o (fun z:R^o=>`|z|) t) (L i) (hBound i)).
have hSum:@norm_analytic R X Y NX NY hNX hNY A (\sum_i (fun x=>L i (F i x))).
  elim/big_ind:_=>[|g h hg hh|i _].
  - exact:(@norm_constant_analytic R X Y NX NY hNX hNY A hA 0).
  - exact:(norm_analytic_add hg hh).
  - exact:hTerm.
apply:(@norm_analytic_domain_agreement R X Y NX NY hNX hNY A
  (\sum_i (fun x=>L i (F i x))) (fun x=>[ffun i=>F i x]) _ hSum)=>x hx.
have hEval:(\sum_i (fun x=>L i (F i x))) x=\sum_i L i (F i x).
  by elim/big_rec2:_=>[|i y G _ <-].
rewrite hEval.
have hExpansion:=@euclidean_coordinate_expansion R m [ffun i=>F i x].
change ((\sum_i F i x*:e i)=[ffun i=>F i x]).
have hEqual:(\sum_i [ffun j=>F j x] i*:e i)=\sum_i F i x*:e i.
  by apply:eq_bigr=>i _;rewrite ffunE.
by move:hExpansion;rewrite hEqual.
Qed.
