(** Federer (1969), 3.2.48, pp. 285–286: the
    top-target Jacobian of independent orthogonal Cartesian
    blocks is the product of their top-target Jacobians.
    This supporting calculation follows 1.7.6 and 1.7.11;
    it retains singular maps and all zero dimensions. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom TensorUP Bilinear InnerProductUP InnerNorm ProductInner
  ProductInnerNormBounds ProductInnerDifferential ProductLinearMaps ProductFiniteBasis
  ProductTopNorm CartesianExteriorWordNorm LinearBasis GramSchmidt OrthonormalisationUP
  OrthonormalFamilies AdjointUP Adjoint ExteriorMaps ExteriorNorm ExteriorGrading
  ExteriorHomogeneousProducts FiniteExteriorPowers CovectorProductNaturality
  InnerExteriorPositivity ExteriorOperatorNorm ExteriorMapScaling ExteriorNormNaturality TopExteriorNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [cartesian_linear_hom]: the two independent
    linear blocks in the differential diagram of 3.2.48,
    p. 285, expressed through the existing Cartesian
    projections and pair map. This is the actual map
    (x,y) to (f(x),g(y)), not a selected representative. *)
Definition cartesian_linear_hom (R:realType) (V W U Z:lmodType R)
    (f:Hom V U) (g:Hom W Z):=
  product_pair_hom (hom_comp f (@product_first_projection_hom R V W))
    (hom_comp g (@product_second_projection_hom R V W)).

(** Source for [cartesian_linear_homE]: the actual values
    of the Cartesian linear blocks supporting 3.2.48,
    pp. 285–286, by the linear product of 1.1.2. *)
Lemma cartesian_linear_homE (R:realType) (V W U Z:lmodType R)
    (f:Hom V U) (g:Hom W Z) x y:cartesian_linear_hom f g (x,y)=(f x,g y).
Proof. by rewrite /cartesian_linear_hom product_pair_homE. Qed.

(** Source for [cartesian_linear_adjoint]: the adjoint of
    independent Cartesian blocks is the Cartesian map of
    their adjoints, supporting 3.2.48, p. 286,
    by the inner-product sum in 1.7.11, p. 36. *)
Lemma cartesian_linear_adjoint (R:realType) (V W U Z:lmodType R)
    BV BW BU BZ (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW)
    (hU:@is_inner_product R U BU) (hZ:@is_inner_product R Z BZ)
    (f:Hom V U) (g:Hom W Z) (a:Hom U V) (b:Hom Z W):
  is_adjoint BV BU (hom_as_linear f) (hom_as_linear a) ->
  is_adjoint BW BZ (hom_as_linear g) (hom_as_linear b) ->
  is_adjoint (product_inner hV hW) (product_inner hU hZ)
    (hom_as_linear (cartesian_linear_hom f g)) (hom_as_linear (cartesian_linear_hom a b)).
Proof.
move=>ha hb [x y] [u z].
change (product_inner hV hW (x,y) (cartesian_linear_hom a b (u,z))=
  product_inner hU hZ (cartesian_linear_hom f g (x,y)) (u,z)).
by rewrite !cartesian_linear_homE !product_innerE ha hb.
Qed.

(** Source for [cartesian_top_exterior_norm]: the two
    independent Jacobian factors used in 3.2.48, p. 286.
    The degree equals the sum of the target dimensions;
    source dimensions are unrestricted. Adjoints reduce the
    calculation to actual unit top words and orthogonal factors. *)
Theorem cartesian_top_exterior_norm (R:realType) (h2:(1+1:R)!=0)
    (V W U Z:lmodType R) BV BW BU BZ
    (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW)
    (hU:@is_inner_product R U BU) (hZ:@is_inner_product R Z BZ)
    n m r s (v:'I_n->V) (w:'I_m->W) (u:'I_r->U) (z:'I_s->Z)
    (hv:is_basis v) (hw:is_basis w) (hu:is_basis u) (hz:is_basis z)
    (f:Hom V U) (g:Hom W Z):
  exterior_operator_norm h2 (product_inner_productP hV hW) (product_inner_productP hU hZ)
    (cartesian_basisP hv hw) (hom_as_linear (cartesian_linear_hom f g)) (r+s)=
  exterior_operator_norm h2 hV hU hv (hom_as_linear f) r*
    exterior_operator_norm h2 hW hZ hw (hom_as_linear g) s.
Proof.
pose P:lmodType R:=[the lmodType R of (V*W)%type].
pose Q:lmodType R:=[the lmodType R of (U*Z)%type].
pose hP:=product_inner_productP hV hW.
pose hQ:=product_inner_productP hU hZ.
pose a:Hom U V:=hom_of_linear (inner_adjoint hV hU hv (hom_as_linear f)).
pose b:Hom Z W:=hom_of_linear (inner_adjoint hW hZ hw (hom_as_linear g)).
have ha:is_adjoint BV BU (hom_as_linear f) (hom_as_linear a):=inner_adjointP hV hU hv (hom_as_linear f).
have hb:is_adjoint BW BZ (hom_as_linear g) (hom_as_linear b):=inner_adjointP hW hZ hw (hom_as_linear g).
have [e [he hE]]:=@orthonormal_basis_exists R U BU hU r u hu.
have [h [hh hH]]:=@orthonormal_basis_exists R Z BZ hZ s z hz.
pose E:=e_lambda e (ord_tuple r).
pose H:=e_lambda h (ord_tuple s).
have hEN:exterior_norm h2 hU E= 1.
  exact (orthonormal_product_unit_norm h2 hU (orthonormalisation_orthonormal hE)).
have hHN:exterior_norm h2 hZ H= 1.
  exact (orthonormal_product_unit_norm h2 hZ (orthonormalisation_orthonormal hH)).
pose iQ:{linear U->Q}:=GRing.Linear.clone _ _ _ _ (@product_left R U Z) _.
pose jQ:{linear Z->Q}:=GRing.Linear.clone _ _ _ _ (@product_right R U Z) _.
pose iP:{linear V->P}:=GRing.Linear.clone _ _ _ _ (@product_left R V W) _.
pose jP:{linear W->P}:=GRing.Linear.clone _ _ _ _ (@product_right R V W) _.
pose volume:=exterior_product (exterior_power_map iQ r E) (exterior_power_map jQ s H).
have hVolume:exterior_norm h2 hQ volume= 1.
  by rewrite (@product_top_norm R h2 U Z BU BZ hU hZ r s e h he hh E H) hEN hHN mulr1.
pose F:=cartesian_linear_hom f g.
pose A:=cartesian_linear_hom a b.
have hA:=@cartesian_linear_adjoint R V W U Z BV BW BU BZ hV hW hU hZ f g a b ha hb.
rewrite (@exterior_operator_adjoint_norm_equal R h2 P Q _ _ hP hQ (n+m) (r+s)
  (cartesian_basis v w) (cartesian_basis e h) (cartesian_basisP hv hw) (cartesian_basisP he hh)
  (hom_as_linear F) (hom_as_linear A) hA (r+s)).
rewrite (@top_exterior_operator_unit_value R h2 Q P _ _ hQ hP (r+s)
  (cartesian_basis e h) (cartesian_basisP he hh) (hom_as_linear A) volume hVolume).
have hFValue:exterior_operator_norm h2 hV hU hv (hom_as_linear f) r=
    exterior_norm h2 hV (exterior_power_map (hom_as_linear a) r E).
  rewrite (@exterior_operator_adjoint_norm_equal R h2 V U BV BU hV hU n r v e hv he
    (hom_as_linear f) (hom_as_linear a) ha r).
  exact (@top_exterior_operator_unit_value R h2 U V BU BV hU hV r e he (hom_as_linear a) E hEN).
have hGValue:exterior_operator_norm h2 hW hZ hw (hom_as_linear g) s=
    exterior_norm h2 hW (exterior_power_map (hom_as_linear b) s H).
  rewrite (@exterior_operator_adjoint_norm_equal R h2 W Z BW BZ hW hZ m s w h hw hh
    (hom_as_linear g) (hom_as_linear b) hb s).
  exact (@top_exterior_operator_unit_value R h2 Z W BZ BW hZ hW s h hh (hom_as_linear b) H hHN).
rewrite hFValue hGValue.
have hImage:exterior_power_map (hom_as_linear A) (r+s) volume=
    exterior_product (exterior_power_map iP r (exterior_power_map (hom_as_linear a) r E))
      (exterior_power_map jP s (exterior_power_map (hom_as_linear b) s H)).
  rewrite /volume exterior_power_map_product !exterior_power_map_composition.
  congr (exterior_product _ _); apply:exterior_power_map_ext.
  - move=>x; change (cartesian_linear_hom a b (x,0)=(a x,0)).
    by rewrite cartesian_linear_homE linear0.
  - move=>y; change (cartesian_linear_hom a b (0,y)=(0,b y)).
    by rewrite cartesian_linear_homE linear0.
rewrite hImage /E /H !exterior_basis_product_natural.
have hProduct:=@cartesian_exterior_word_norm R h2 V W BV BW hV hW r s
  (fun i=>a (e i)) (fun j=>b (h j)).
rewrite !exterior_basis_product_natural in hProduct; exact hProduct.
Qed.
