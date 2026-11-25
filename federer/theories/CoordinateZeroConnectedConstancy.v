(** Federer (1969), 4.1.4, p. 349: vanishing of the
    coordinate derivatives makes the smoothed dual field
    constant on C_e. Finite basis extensionality gives the
    zero differential; the existing rank-zero theorem and
    connectedness then give the original constancy. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis GrassmannAbbreviations
  FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormDifferentialUP NormConnectedZeroDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [coordinate_zero_linear_map]: a linear map
    vanishing on the original standard basis is zero, the
    finite-dimensional inference used in Federer 4.1.4, p. 349.
    The empty basis handles dimension zero. *)
Lemma coordinate_zero_linear_map (R:realType) n (Y:lmodType R) (L:Hom (R_n R n) Y):
  (forall i,L (@coordinate_basis R n i)=0) ->L=0.
Proof.
move=>hZero; apply:hom_ext=>v.
change (hom_as_linear L v=hom_as_linear (0:Hom (R_n R n) Y) v).
apply:(@basis_linear_ext R (Choice.clone 'I_n _) (R_n R n) (@coordinate_basis R n)
  (@coordinate_basisP R n) Y (hom_as_linear L) (hom_as_linear (0:Hom (R_n R n) Y)))=>i.
by rewrite !hom_as_linearE hom_zeroE hZero.
Qed.

(** Source for [connected_zero_coordinate_differential_constant]:
    the exact constancy inference for the actual smoothed dual
    field in Federer 4.1.4, p. 349. The target may have
    arbitrary dimension and need not be separable. *)
Theorem connected_zero_coordinate_differential_constant (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (A:set (R_n R n))
    (f:R_n R n->Y) (D:R_n R n->Hom (R_n R n) Y):
  @connected (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) A ->
  (forall x,A x ->has_norm_differential (inner_norm (@euclidean_inner_productP R n)) NY A f x (D x)) ->
  (forall x,A x ->forall i,D x (@coordinate_basis R n i)=0) ->
  forall a b,A a ->A b ->f b=f a.
Proof.
move=>hConnected hD hZero.
apply:(@norm_connected_zero_differential_constant R (R_n R n) Y
  (inner_norm (@euclidean_inner_productP R n)) NY
  (inner_norm_real_norm (@euclidean_inner_productP R n)) hNY A f hConnected).
move=>x hx.
have hMap:D x=0:=coordinate_zero_linear_map (hZero x hx).
by rewrite -hMap; exact:hD x hx.
Qed.
