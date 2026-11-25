(** Federer (1969), 3.2.48, pp. 285–286: transfer the actual
    Cartesian tangent differential to the exact Euclidean partial graph
    used by coarea. Actual plane dimensions, inclusions and isometric
    carrier laws discharge the coordinate obligations. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations EuclideanLinearMaps EuclideanInnerProduct InnerProductUP InnerProductRestriction InnerNorm
  ProductInner OrthogonalMaps LinearBasis FiniteInnerChartUP TangentConeUP
  ExteriorMaps InnerExteriorPositivity OperatorNormUP PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction PartialExteriorNormUP GrassmannCartesianProduct
  CartesianTopExteriorNorm ExteriorIsometricPrecomposition FiniteInnerTangentPartialJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_cartesian_tangent_partial_jacobian]: the
    actual source tangent norm becomes the exact coordinate partial
    Jacobian in 3.2.48, p. 286. The product tangent equality is a proved
    geometric obligation; no value is assigned outside that tangent. *)
Theorem finite_inner_cartesian_tangent_partial_jacobian (R:realType) (X Y Z:lmodType R)
    BX BY BZ (hX:@is_inner_product R X BX) (hY:@is_inner_product R Y BY) (hZ:@is_inner_product R Z BZ)
    n m (bx:'I_n->X) (by0:'I_m->Y) (hbX:is_basis bx) (hbY:is_basis by0)
    N K (e:Hom (R_n R N) [the lmodType R of (X*Y)%type])
    (p:Hom [the lmodType R of (X*Y)%type] (R_n R N)) (t:Hom Z (R_n R K))
    (W:set (X*Y)) a r s (S:G X r) (T:G Y s)
    (D:Hom [the lmodType R of (X*Y)%type] Z) q j:
  is_finite_inner_chart (product_inner hX hY) e p ->
  is_orthogonal_map BZ (@euclidean_inner_product R K) (hom_as_linear t) ->
  norm_tangent_cone (inner_norm (product_inner_productP hX hY)) W a=
    [set z:X*Y|grassmann_val S z.1 /\grassmann_val T z.2] ->
  is_operator_norm
    (exterior_inner_productP (euclidean_two_nonzero R)
      (product_inner_productP (restricted_inner_productP hX (grassmann_val S))
        (restricted_inner_productP hY (grassmann_val T))) q)
    (exterior_inner_productP (euclidean_two_nonzero R) hZ q)
    (exterior_power_map (hom_as_linear (hom_comp D
      (cartesian_linear_hom (hom_of_linear (subspace_inclusion (grassmann_val S)))
        (hom_of_linear (subspace_inclusion (grassmann_val T)))))) q) j ->
  is_partial_exterior_norm q
    (partial_function_source_restrict
      (norm_tangent_cone (inner_norm (@euclidean_inner_productP R N)) (p @` W) (p a))
      (partial_function_total (hom_comp t (hom_comp D e)))) j.
Proof.
move=>hChart ht hTangent hNorm.
have [P [hPlane [i [l [hil [hli [hi hiValue]]]]]]]:=
  @grassmann_cartesian_product R X Y BX BY hX hY n m bx by0 hbX hbY r s S T.
pose U:lmodType R:=[the lmodType R of (subspace_space (grassmann_val S)*subspace_space (grassmann_val T))%type].
pose V:=subspace_space (grassmann_val P).
pose hU:=product_inner_productP (restricted_inner_productP hX (grassmann_val S))
  (restricted_inner_productP hY (grassmann_val T)).
pose hV:=restricted_inner_productP (product_inner_productP hX hY) (grassmann_val P).
pose F:=hom_comp D (cartesian_linear_hom (hom_of_linear (subspace_inclusion (grassmann_val S)))
  (hom_of_linear (subspace_inclusion (grassmann_val T)))).
pose G:=hom_comp D (hom_of_linear (subspace_inclusion (grassmann_val P))).
have hNormP:is_operator_norm (exterior_inner_productP (euclidean_two_nonzero R) hV q)
    (exterior_inner_productP (euclidean_two_nonzero R) hZ q)
    (exterior_power_map (hom_as_linear G) q) j.
  apply:(@exterior_isometric_precomposition_norm R (euclidean_two_nonzero R)
    U V Z _ _ _ hU hV hZ (hom_as_linear i) (hom_as_linear l) (hom_as_linear F)
    (hom_as_linear G) q j hil hli hi _ hNorm).
  move=>u.
  change (D (subspace_val (i u))=F u).
  rewrite hiValue /F hom_compE.
  case:u=>v w; by rewrite cartesian_linear_homE.
have hActual:norm_tangent_cone (inner_norm (product_inner_productP hX hY)) W a=(grassmann_val P:set _).
  rewrite hTangent; apply/seteqP; split=>z hz; [exact ((hPlane z).2 hz)|exact ((hPlane z).1 hz)].
have [b hb]:=grassmann_proof P.
exact (@finite_inner_tangent_partial_jacobian_chart R [the lmodType R of (X*Y)%type] Z
  _ BZ (product_inner_productP hX hY) hZ N K e p t W a (grassmann_val P) (r+s)%N b hb D q j
  hChart ht hActual hNormP).
Qed.
