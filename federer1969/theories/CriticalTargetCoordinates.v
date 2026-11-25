(** Federer (1969), 3.4.3, p. 317: the Hahn–Banach
    selection of bounded coordinates on the actual derivative range. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceSums SubspaceCarrier
  LinearBasis FiniteDimension FiniteCoordinates GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness RealNormUP
  RealSeminormOperations NormDifferentialUP NormDifferentialArithmetic
  NormFiniteLinearBound FiniteBoundedRetraction LinearRankUP CriticalTargetCoordinatesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_target_coordinates_exists]: the first
    choice of L in 3.4.3, p. 317. A basis of the actual
    differential range gives its parametrisation J. The project's
    Hahn–Banach retraction extends the inverse coordinates;
    finite-dimensional norm comparison proves their bound in the
    original Euclidean norm. The target needs no finite basis
    or completeness, and rank zero is included. *)
Theorem critical_target_coordinates_exists (R:realType) (X Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (D:Hom X Y) nu:
  has_linear_rank D nu ->exists (L:Hom Y (R_n R nu)) (J:Hom (R_n R nu) Y),
    is_critical_target_coordinates NY D L J.
Proof.
move=>[e he].
pose U:=subspace_space (range_subspace (hom_as_linear D)).
pose V:=R_n R nu.
pose S:{linear V->U}:=finite_basis_synthesis e.
pose J0:{linear V->Y}:=linear_comp (subspace_inclusion _) S.
have hS:injective S:=can_inj (finite_basis_synthesisK he).
have hJ:injective J0.
  move=>u v h;apply:hS.
  apply:(@subspace_val_injective R Y (range_subspace (hom_as_linear D))).
  exact:h.
have [L0 [hCancel [C [hC hBound]]]]:=@finite_bounded_linear_retraction R V Y
  NY hNY nu (@coordinate_basis R nu) (@coordinate_basisP R nu) J0 hJ.
pose NP:=fun u:V=>NY (J0 u).
have hNP:is_real_norm NP:=real_norm_injective_precompose hNY hJ.
pose NV:=inner_norm (@euclidean_inner_productP R nu).
pose hNV:=inner_norm_real_norm (@euclidean_inner_productP R nu).
pose I:=hom_of_linear (linear_id V).
have [K [hK hComparison]]:=@norm_finite_linear_bounded R V V NP NV hNP hNV
  nu (@coordinate_basis R nu) (@coordinate_basisP R nu) I.
exists (hom_of_linear L0),(hom_of_linear J0);constructor.
- exists (K*C);split;first exact:mulr_ge0 hK hC.
  move=>y.
  have h1:=hComparison (L0 y).
  have h2:=ler_wpM2l hK (hBound y).
  change (is_true (NV (L0 y)<=K*NP (L0 y))) in h1.
  change (is_true (K*NP (L0 y)<=K*(C*NY y))) in h2.
  rewrite mulrA in h2;exact:le_trans h1 h2.
- exact:hCancel.
- move=>y;split.
  + move=>[x hx].
    have hRange:range_subspace (hom_as_linear D) y by exists x;exact:esym hx.
    exists (finite_basis_coordinates he (subspace_lift hRange)).
    change (subspace_val (S (finite_basis_coordinates he (subspace_lift hRange)))=y).
    by rewrite /S finite_basis_coordinatesK subspace_liftE.
  + move=>[u <-].
    have [x hx]:=subspace_valP (S u).
    exists x;exact:esym hx.
Qed.
