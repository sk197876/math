(** Federer (1969), 4.1.8, p. 361: both zero-degree
    endpoints of the original product mass assertions.
    Reuse the actual scalar identification of 1.3.1,
    p. 13, and the absolute-scalar norm of 4.1.7. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear AlgebraUP GradedComponents
  ExteriorAlgebra ExteriorGrading ExteriorMaps ExteriorPowers SimpleZeroDegree
  ExteriorHomogeneousProducts GrassmannAbbreviations EuclideanInnerProduct
  CurrentCoefficientNorms ZeroDegreeCovectorNorm RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_power_map_zeroth_scalar]: every
    original exterior map is the scalar identity in degree
    zero, supporting Federer 4.1.8, p. 361, by 1.3.1,
    p. 13. No nonzero source premise is needed. *)
Lemma exterior_power_map_zeroth_scalar (K:fieldType) (V W:lmodType K)
    (f:{linear V->W}) (c:K):
  exterior_power_map f 0 (exterior_zeroth_inclusion V c)=exterior_zeroth_inclusion W c.
Proof.
apply:val_inj.
change (exterior_algebra_map f (component_val (exterior_zeroth_inclusion V c))=
  component_val (exterior_zeroth_inclusion W c)).
rewrite !zeroth_inclusion_val /exterior_scalar linearZ.
change (c*:exterior_algebra_map f (alg_one (exterior_algebra V))=
  c*:alg_one (exterior_algebra W)).
by rewrite algebra_map_one.
Qed.

(** Source for [exterior_product_zeroth_scalar_left]:
    the original degree-zero factor acts by its scalar,
    supporting Federer 4.1.8, p. 361, by 1.3.1, p. 13. *)
Lemma exterior_product_zeroth_scalar_left (K:fieldType) (V:lmodType K) d
    (c:K) (x:exterior_power V d):
  exterior_product (exterior_zeroth_inclusion V c) x=c*:x.
Proof.
apply:val_inj.
change (wedge (component_val (exterior_zeroth_inclusion V c)) (component_val x)=component_val (c*:x)).
rewrite zeroth_inclusion_val /exterior_scalar linearZ.
by rewrite (bilZl (wedge_bilinear V)) wedge_unitl.
Qed.

(** Source for [exterior_product_zeroth_scalar_right]:
    the original scalar factor on the right gives the same
    scalar product after the equal-degree identification,
    supporting Federer 4.1.8, p. 361. *)
Lemma exterior_product_zeroth_scalar_right (K:fieldType) (V:lmodType K) d
    (c:K) (x:exterior_power V d):
  exterior_reindex (addn0 d) (exterior_product x (exterior_zeroth_inclusion V c))=c*:x.
Proof.
apply:val_inj.
change (component_val (exterior_reindex (addn0 d) (exterior_product x (exterior_zeroth_inclusion V c)))=component_val (c*:x)).
rewrite exterior_reindexE exterior_productE zeroth_inclusion_val /exterior_scalar linearZ.
by rewrite (bilZr (wedge_bilinear V)) wedge_unitr.
Qed.

(** Source for [current_vector_mass_reindex]: the original
    mass is unchanged by equal degree indices, supporting
    Federer 4.1.8, p. 361. This includes degree zero. *)
Lemma current_vector_mass_reindex (R:realType) (h2:(1+1:R)!=0) n d e (h:d=e)
    (x:exterior_power (R_n R n) d):
  @current_vector_mass R h2 n e (exterior_reindex h x)=@current_vector_mass R h2 n d x.
Proof. by case:e/h. Qed.

(** Source for [current_vector_mass_zeroth_scalar]: the
    original scalar multivector has absolute scalar mass,
    supporting Federer 4.1.8, p. 361, with the already
    established degree-zero convention. *)
Lemma current_vector_mass_zeroth_scalar (R:realType) (h2:(1+1:R)!=0) n (c:R):
  @current_vector_mass R h2 n 0 (exterior_zeroth_inclusion (R_n R n) c)=`|c|.
Proof. exact:zeroth_exterior_scalar_norm. Qed.

(** Source for [current_vector_mass_zeroth_value]: every
    original degree-zero multivector has the mass of its
    scalar coordinate, supporting Federer 4.1.8, p. 361. *)
Lemma current_vector_mass_zeroth_value (R:realType) (h2:(1+1:R)!=0) n
    (x:exterior_power (R_n R n) 0):
  @current_vector_mass R h2 n 0 x=`|exterior_zeroth_inverse (R_n R n) x|.
Proof.
rewrite -{1}(exterior_zeroth_inverseK x);exact:current_vector_mass_zeroth_scalar.
Qed.
