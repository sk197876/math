(** Federer (1969), 4.1.13, pp. 369–370: replace the
    source of a normal current by any open neighbourhood
    of its original support. The exact zero-extension mass
    bound and boundary commutation preserve finite normal
    mass; the support remains the original compact set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary SmoothCompactSet CurrentSupportGeometry
  CurrentOpenRestriction CurrentOpenRestrictionBoundary CurrentOpenRestrictionSupport
  CurrentOpenRestrictionMass NormalCurrentsUP CurrentNormalMass NormalCurrentFiniteMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentOpenRestrictionNormal.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables U V:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall x,V x->norm_domain_interior NX V x.
Hypothesis hUV:forall x,U x->V x.
Local Notation restriction := (fun m=>@current_open_restriction R h2 n m U V hU hV hUV).

(** Source for [current_open_restriction_normal_mass_bound]:
    N(R_U T)<=N(T), by the original mass and boundary
    definitions of Federer 4.1.7, p. 358, supporting
    the neighbourhood replacement in 4.1.13, pp. 369–370.
    Degree zero retains only its original current mass. *)
Theorem current_open_restriction_normal_mass_bound m
    (T:@current_space R h2 n V hV m):
  (@current_normal_mass R h2 n U hU m (restriction m T)<=
    @current_normal_mass R h2 n V hV m T)%E.
Proof.
case:m T=>[|j] T.
- exact:(@current_open_restriction_mass_bound R h2 n 0%N U V hU hV hUV T).
- rewrite !current_normal_mass_positive_degree -current_open_restriction_boundary.
  apply:leeD.
  + exact:(@current_open_restriction_mass_bound R h2 n j.+1 U V hU hV hUV T).
  + exact:(@current_open_restriction_mass_bound R h2 n j U V hU hV hUV
      (@current_boundary R h2 n j V hV T)).
Qed.

(** Source for [current_normal_neighbourhood_restriction]: a
    normal current remains normal on every open neighbourhood
    of its support, supporting the literal source replacement
    in Federer 4.1.13, pp. 369–370. No connectedness,
    convexity or positive-dimensional premise is added. *)
Theorem current_normal_neighbourhood_restriction m
    (T:@current_space R h2 n V hV m):
  @is_normal_current R h2 n V hV m T->
  @current_support R h2 n V hV m T `<=` U->
  @is_normal_current R h2 n U hU m (restriction m T).
Proof.
move=>hNormal hSupport;split.
- apply:finite_normal_mass_locally_normal.
  exact:(le_lt_trans (current_open_restriction_normal_mass_bound T)
    (@normal_current_finite_normal_mass R h2 n V hV m T hNormal)).
- pose K:=@Build_smooth_compact_set R X NX hNX U
    (@current_support R h2 n V hV m T) hSupport hNormal.2.
  apply:(@current_support_compact_bound R h2 n m U hU K (restriction m T)).
  exact:(@current_open_restriction_support_subset R h2 n m U V hU hV hUV T).
Qed.
End CurrentOpenRestrictionNormal.
