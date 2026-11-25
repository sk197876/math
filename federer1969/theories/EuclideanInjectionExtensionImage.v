(** Federer (1969), 3.3.4, p. 290:
    every actual ambient orthogonal map
    fixing the active orthogonal complement
    is the extension of a unique active
    orthogonal operator. All restriction
    witnesses remain local. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  OrthogonalMaps EuclideanRectangularAdjoint EuclideanInjectionRetraction
  InjectionExtensionUP InjectionExtension InjectionExtensionRange
  EuclideanInjectionExtension EuclideanOrthogonalInvariantMeasures OrthogonalGroupHaarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_injection_extension_image]:
    the original K of Federer 3.3.4,
    p. 290, is precisely the copy
    of the full orthogonal group on X.
    Fixing the actual normal complement
    forces preservation of the active range;
    the actual adjoint restriction is
    orthogonal and its opaque extension
    recovers the original whole operator. *)
Theorem euclidean_injection_extension_image (R:realType) d n
    (w:Hom (R_n R d) (R_n R n))
    (hW:is_orthogonal_map (@euclidean_inner_product R d)
      (@euclidean_inner_product R n) (hom_as_linear w))
    (K:euclidean_orthogonal_group R n):
  (forall x,euclidean_rectangular_adjoint w x=0 ->orthogonal_element_map K x=x) ->
  exists h:euclidean_orthogonal_group R d,
    euclidean_injection_orthogonal_extension hW h=K.
Proof.
move=>hFixed.
pose q:=euclidean_rectangular_adjoint w.
pose hCancel:=euclidean_orthogonal_injection_adjoint_cancel hW.
pose g:=orthogonal_element_map K.
have hRange u:g (w u)=w (q (g (w u))).
  exact:(@injection_fixed_normal_range R (R_n R d) (R_n R n)
    (@euclidean_inner_product R d) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R d) (@euclidean_inner_productP R n)
    w q g hCancel (euclidean_rectangular_adjoint_pairing w)
    (orthogonal_element_orthogonal K) hFixed u).
pose h:Hom (R_n R d) (R_n R d):=hom_comp q (hom_comp g w).
have hOrthogonal:is_orthogonal_map (@euclidean_inner_product R d)
    (@euclidean_inner_product R d) (hom_as_linear h).
  move=>u v.
  change (euclidean_inner_product (h u) (h v)=euclidean_inner_product u v).
  rewrite -(hW (h u) (h v)).
  change (euclidean_inner_product (w (q (g (w u)))) (w (q (g (w v))))=
    euclidean_inner_product u v).
  rewrite -!hRange (orthogonal_element_inner K).
  exact:hW.
pose hElement:=orthogonal_element_of (@euclidean_inner_productP R d)
  (@coordinate_basisP R d) hOrthogonal.
have hValue:orthogonal_element_map hElement=h.
  apply:hom_ext=>u; exact:orthogonal_element_ofE.
have hSpec:is_injection_extension w q h g.
  split; last exact:hFixed.
  move=>u; exact:hRange u.
have hUnique:injection_extension hCancel h=g.
  exact:(injection_extension_unique hCancel (injection_extension_specification hCancel h) hSpec).
exists hElement; apply:orthogonal_element_ext=>x.
by rewrite euclidean_injection_orthogonal_extensionE hValue hUnique.
Qed.
