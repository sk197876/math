(** Federer (1969), 4.1.24, p. 380: rectifiable
    currents are mass limits of Lipschitz images of original
    integral polyhedral chains. The source Euclidean dimension
    is arbitrary, and every source compact maps inside the
    exact original K. This is an independent approximation
    specification, without assumed flatness, mass or support
    of the limiting current. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP LipschitzBasic SmoothCompactSet CurrentSpaces CurrentMassSealed
  FlatCurrentsUP CurrentFlatLipschitzPushforwardSealed
  PolyhedralCurrentAlgebra PolyhedralCurrentFlat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [polyhedral_lipschitz_image]: the actual f#P
    in the first definition of 4.1.24, p. 380.
    This is an abbreviation of the existing opaque
    Lipschitz pushforward. Integral polyhedral membership supplies
    its required flat-domain evidence; no additional premise
    is imposed on the original approximation data. *)
Definition polyhedral_lipschitz_image (R:realType) (h2:(1+1:R)!=0)
    (d n m:nat) (Z:set (R_n R d)) (U:set (R_n R n))
    (hZ:forall x,Z x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R d)) Z x)
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (C:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R d)) Z)
    (f:R_n R d->R_n R n) (hImage:forall x,Z x->U (f x))
    (hLip:@is_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) Z f)
    (P:@current_space R h2 d Z hZ m)
    (hP:@integral_polyhedral_current_class R h2 d m Z hZ C P):
    @current_space R h2 n U hU m:=
  @CurrentFlatLipschitzPushforward.value R h2 d n m Z U hZ hU f hImage
    (@metric_lipschitz_is_local R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      Z f hLip) P
    (ex_intro _ C (@integral_polyhedral_current_flat_supported R h2 d m Z hZ C P hP)).

Section RectifiableCurrentApproximationUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set hNX U.
Local Notation Current:=(@current_space R h2 n U hU m).
Local Notation M:=(@CurrentMass.value R h2 n m U hU).

(** Source for [is_rectifiable_image_approximant]: the full
    original image witness in 4.1.24, p. 380. The
    globally Lipschitz source map is defined on an arbitrary
    open Z in an arbitrary finite Euclidean dimension d.
    Its compact C, integral polyhedral chain and map may
    all depend on the eventual approximation tolerance. *)
Definition is_rectifiable_image_approximant (Q:Current):Prop:=
  exists d:nat,exists Z:set (R_n R d),
  exists hZ:forall x,Z x->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R d)) Z x,
  exists C:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R d)) Z,
  exists f:R_n R d->X,exists hImage:forall x,Z x->U (f x),
  exists hLip:@is_metric_lipschitz R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R d)))
    (real_norm_metric_space hNX) Z f,
  exists P:@current_space R h2 d Z hZ m,
  exists hP:@integral_polyhedral_current_class R h2 d m Z hZ C P,
    (forall x,smooth_compact_carrier C x->smooth_compact_carrier K (f x)) /\
    @polyhedral_lipschitz_image R h2 d n m Z U hZ hU C f hImage hLip P hP=Q.

(** Source for [is_rectifiable_current_supported_in]: the literal
    defining property of R_(m,K)(U), Federer 4.1.24,
    p. 380. Finite mass, support in K and flatness
    are subsequent conclusions, not definition hypotheses. *)
Definition is_rectifiable_current_supported_in (T:Current):Prop:=
  forall epsilon:R,0<epsilon->exists Q:Current,
    is_rectifiable_image_approximant Q /\(M (T-Q)<epsilon%:E)%E.
End RectifiableCurrentApproximationUP.
