(** Federer (1969), 3.4.10, p. 338,
    citing Bruhat and Whitney, section 11(c),
    p. 159: use y=x^2 t to
    obtain an analytic implicit equation near the
    negative z-axis. The equation and the
    coordinate map are explicit local proof witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals ring.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP NormOpenDomainLaws
  NormAnalyticUP NormAnalyticOperations NormAnalyticConstant NormAnalyticScalarProducts
  EuclideanScalarCoordinateAnalytic BruhatWhitneySurfaceUP BruhatWhitneySurfaceSealed
  BruhatWhitneySurfaceAnalytic BruhatWhitneyNegativeRootBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Auxiliary.
Variable R:realType.
Local Notation X:=(R_n R 3).
Local Notation j:=(Ordinal (isT:(1<3)%N)).
Local Notation hB:=(@euclidean_inner_productP R 3).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).

(** Source for [bruhat_whitney_auxiliary_equation]: the
    substitution y=x^2 t in the cited
    polynomial gives zt-z^2 x^2 t^3+1.
    This supports the example in 3.4.10,
    p. 338; coordinates here are ordered (x,z,t). *)
Definition bruhat_whitney_auxiliary_equation (v:X):R:=
  v j*v ord_max-(v j)^+2*(v ord0)^+2*(v ord_max)^+3+1.

(** Source for [bruhat_whitney_auxiliary_point]: at an
    original nonzero axis coordinate b, the
    auxiliary solution is (0,b,-1/b), supporting
    the example cited in 3.4.10, p. 338. *)
Definition bruhat_whitney_auxiliary_point (b:R):X:=
  [ffun i=>if i==ord0 then 0 else if i==j then b else -b^-1].

(** Source for [bruhat_whitney_auxiliary_point_coordinates]: exact
    coordinates of the local proof witness,
    supporting 3.4.10, p. 338. *)
Lemma bruhat_whitney_auxiliary_point_coordinates b:
  bruhat_whitney_auxiliary_point b ord0=0 /\
  bruhat_whitney_auxiliary_point b j=b /\
  bruhat_whitney_auxiliary_point b ord_max= -b^-1.
Proof. by rewrite /bruhat_whitney_auxiliary_point !ffunE /=. Qed.

(** Source for [bruhat_whitney_auxiliary_point_zero]: the
    original axis point lifts to an actual
    zero of the auxiliary equation, supporting
    the example in 3.4.10, p. 338. *)
Lemma bruhat_whitney_auxiliary_point_zero b:b!=0 ->
  bruhat_whitney_auxiliary_equation (bruhat_whitney_auxiliary_point b)=0.
Proof.
move=>hb;rewrite /bruhat_whitney_auxiliary_equation
  (bruhat_whitney_auxiliary_point_coordinates b).1
  (bruhat_whitney_auxiliary_point_coordinates b).2.1
  (bruhat_whitney_auxiliary_point_coordinates b).2.2.
by rewrite expr0n mulr0 mul0r subr0 mulrN mulfV // addNr.
Qed.

(** Source for [bruhat_whitney_auxiliary_analytic]: the
    auxiliary implicit equation is genuinely analytic,
    by the project's coordinate and scalar operations,
    supporting 3.4.10, p. 338. *)
Lemma bruhat_whitney_auxiliary_analytic:
  @norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX
    (@scalar_absolute_value_norm R) setT bruhat_whitney_auxiliary_equation.
Proof.
have hX:=@euclidean_scalar_coordinate_analytic R 3 ord0.
have hZ:=@euclidean_scalar_coordinate_analytic R 3 j.
have hT:=@euclidean_scalar_coordinate_analytic R 3 ord_max.
have hOne:=@norm_constant_analytic R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) setT (fun x _=>norm_full_domain_interior NX x) 1.
exact:(norm_analytic_add
  (norm_analytic_subtract (norm_analytic_scalar_product hZ hT)
    (norm_analytic_scalar_product
      (norm_analytic_scalar_product (norm_analytic_scalar_power 2%N hZ)
        (norm_analytic_scalar_power 2%N hX)) (norm_analytic_scalar_power 3%N hT))) hOne).
Qed.

(** Source for [bruhat_whitney_auxiliary_projection]: the
    explicit map (x,z,t) to (x,x^2 t,z)
    returns to the original surface coordinates,
    supporting the example in 3.4.10, p. 338. *)
Definition bruhat_whitney_auxiliary_projection (v:X):X:=
  [ffun i=>if i==ord0 then v ord0 else if i==j then (v ord0)^+2*v ord_max else v j].

(** Source for [bruhat_whitney_auxiliary_projection_equation]: the
    actual original polynomial after substitution is
    x^4 times the auxiliary equation, supporting
    the example in 3.4.10, p. 338.
    The identity includes x=0. *)
Lemma bruhat_whitney_auxiliary_projection_equation v:
  bruhat_whitney_surface_equation (bruhat_whitney_auxiliary_projection v)=
    (v ord0)^+4*bruhat_whitney_auxiliary_equation v.
Proof.
rewrite /bruhat_whitney_surface_equation /bruhat_whitney_auxiliary_projection !ffunE /=.
exact:bruhat_whitney_rescaled_equation.
Qed.

(** Source for [bruhat_whitney_auxiliary_projects_into_surface]: every
    auxiliary solution gives an actual point of
    the cited original surface, 3.4.10, p. 338. *)
Lemma bruhat_whitney_auxiliary_projects_into_surface v:
  bruhat_whitney_auxiliary_equation v=0 ->
  @BruhatWhitneySurface.set R (bruhat_whitney_auxiliary_projection v).
Proof.
move=>hZero;apply/(bruhat_whitney_surface_membership (@BruhatWhitneySurface.laws R)).
change (bruhat_whitney_surface_equation (bruhat_whitney_auxiliary_projection v)=0).
by rewrite bruhat_whitney_auxiliary_projection_equation hZero mulr0.
Qed.
End Auxiliary.
