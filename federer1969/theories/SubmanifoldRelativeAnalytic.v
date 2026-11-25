(** Federer (1969), 3.2.33, p. 270: analyticity of f
    on an analytic submanifold is equivalently analyticity in
    its analytic coordinates, as in 3.1.22 and 3.1.24,
    pp. 236,240. Local ambient extensions are auxiliary. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness RealNormUP NormCoordinateSystemUP NormAnalyticUP
  NormAnalyticRelativeUP NormAnalyticRelativeComposition AnalyticSubmanifoldUP
  AnalyticSubmanifoldCoordinateSystems.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section CoordinateMeaning.
Variable R:realType.
Variables n m:nat.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Local Notation X:=(R_n R n).
Local Notation Z:=(R_n R m).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R m)).

(** Source for [submanifold_relative_analytic_coordinates]:
    the intrinsic analytic-map hypothesis in the final
    paragraph of Federer 3.2.33, p. 270. The
    local-extension definition is equivalent to analyticity
    of f composed with every actual analytic inverse chart.
    Both implications are proved using existing chart laws;
    no global extension is imposed. *)
Theorem submanifold_relative_analytic_coordinates (A W:set X) (f:X->Y):
  @is_euclidean_analytic_submanifold R n m W ->W `<=` A ->
  (@norm_analytic_relative R X Y NX NY hNX hNY A W f <->
    forall (T:set X) (V:set Z) (phi:X->Z) (psi:Z->X),
      @norm_analytic R X Z NX NZ hNX hNZ T phi ->
      @norm_analytic R Z X NZ NX hNZ hNX V psi ->
      is_norm_coordinate_system hNX hNZ W T V phi psi 1%N ->
      @norm_analytic R Z Y NZ NY hNZ hNY V (fun u=>f (psi u))).
Proof.
move=>hW hWA; split.
- move=>hf T V phi psi hPhi hPsi hc.
  apply:(relative_analytic_in_parametrisation _ hPsi hf).
  move=>u hu; exact:(norm_coordinate_backward_membership hc hu).1.
- move=>hall a ha.
  have [T [V [phi [psi [haT [hConvex [hPhi [hPsi hc]]]]]]]]:=
    analytic_submanifold_coordinate_system_exists hW ha.
  have hCoordinate:=hall T V phi psi hPhi hPsi hc.
  have [g [hg hAgree]]:=@analytic_coordinate_local_extension R X Z Y
    NX NZ NY hNX hNZ hNY A W T V phi psi f hWA
    (norm_coordinate_forward_range hc)
    (fun x hx ht=>norm_coordinate_base_inverse hc hx ht) hPhi hCoordinate.
  exists T,g; by split=>//; split.
Qed.
End CoordinateMeaning.
