(** Federer (1969), 4.1.26, pp. 383–384:
    current constancy outside the boundary carrier
    in every ambient degree. A positive-dimensional
    current has its usual boundary; dimension zero
    uses the original boundary-free constancy theorem.
    These are abbreviations and consequences of
    the existing actual current operations. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDensityUP CurrentBoundary EuclideanFundamentalCurrent
  TopCurrentComponentConstancy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [top_current_boundary_carried]: the
    original boundary-support premise used in
    4.1.26, p. 384, in positive dimension.
    In ambient dimension zero it is vacuous;
    there is no negative-degree boundary. *)
Definition top_current_boundary_carried (R:realType) (h2:(1+1:R)!=0) m:
    @full_current_space R h2 m m->set (R_n R m)->Prop:=
  match m as k return @full_current_space R h2 k k->set (R_n R k)->Prop with
  |0%N=>fun _ _=>True
  |p.+1=>fun T B=>
    @current_support R h2 p.+1 (fun _=>True)
      (fun x (_:True)=>norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R p.+1)) x) p
      (@current_boundary R h2 p.+1 p (fun _=>True)
        (fun x (_:True)=>norm_full_domain_interior
          (inner_norm (@euclidean_inner_productP R p.+1)) x) T) `<=` B
  end.

(** Source for [top_current_all_degree_component_constancy]:
    the original top-current constancy step of
    4.1.26, p. 384, with the dimension-zero
    case kept separate internally. No mass
    or current representation is assumed. *)
Theorem top_current_all_degree_component_constancy (R:realType)
    (h2:(1+1:R)!=0) m:
  forall (T:@full_current_space R h2 m m) (B:set (R_n R m)),
  @closed (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) B->
  @top_current_boundary_carried R h2 m T B->
  forall a,~B a->exists c:R,
    @current_support R h2 m (fun _=>True)
      (fun x (_:True)=>norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R m)) x) m
      (T-c*:@euclidean_fundamental_current R h2 m) `<=`
      ~`(@connected_component (real_norm_metric_space
        (inner_norm_real_norm (@euclidean_inner_productP R m))) (~` B) a).
Proof.
case:m=>[|p] T B hB hBoundary a ha.
- exact:(@zero_top_current_complement_component_constancy R h2 T B hB a ha).
- exact:(@top_current_complement_component_constancy R h2 p T B hB hBoundary a ha).
Qed.
