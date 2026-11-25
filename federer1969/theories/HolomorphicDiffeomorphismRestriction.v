(** Federer (1969), 3.4.12, p. 339: restrict the original
    holomorphic charts to open source subsets. Reuse the actual
    real continuity and composite-domain interior laws of 3.1.11. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import NormRegularityOperations TensorUP Hom RealNormUP ScalarRestriction ComplexScalarSealed
  HolomorphicUP HolomorphicRestriction HolomorphicDiffeomorphismUP NormDifferentialUP
  NormRegularity NormAnalyticLocal NormLinearDomainLaws NormClassZeroComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_diffeomorphism_source_restriction]: the
    original chart and its inverse retain their holomorphic laws
    after open restriction, supporting 3.4.10, p. 337, under
    3.4.12, p. 339. The image is specified by the
    original inverse map, rather than by a selected construction. *)
Theorem holomorphic_diffeomorphism_source_restriction (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R)
    (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
    (A B W:X->Prop) (f g:X->X):
  is_holomorphic_diffeomorphism hNX A B f g ->
  (forall x,W x ->A x) ->(forall x,W x ->@norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX W x) ->
  is_holomorphic_diffeomorphism hNX W (fun y=>B y /\W (g y)) f g.
Proof.
move=>hD hWA hW.
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose Id:Hom XR XR:=hom_of_linear (linear_id XR).
have hIdBound:@norm_bounded_linear R XR XR NX NX Id.
  exists 1;split;first exact:ler01.
  by move=>x;rewrite /Id hom_of_linearE mul1r.
have hId:=@norm_class_linear R XR XR NX NX hNX hNX W Id 0%N hW hIdBound.
have hGClass:=norm_analytic_class_all_orders (holomorphic_diffeomorphism_inverse hD).1 0%N.
have hG0:=@norm_class_continuous R XR XR NX NX hNX hNX B g 0%N hGClass.
have hId0:=@norm_class_continuous R XR XR NX NX hNX hNX W Id 0%N hId.
have hImageInterior:=@norm_class_zero_composite_interior R XR XR XR NX NX NX
  B W g Id hG0 hId0.
constructor.
- exact:holomorphic_open_restriction hWA hW (holomorphic_diffeomorphism_forward hD).
- exact:(@holomorphic_open_restriction R X X NX NX hNX hNX B
    (fun y=>B y /\W (g y)) g (fun y hy=>hy.1) hImageInterior
    (holomorphic_diffeomorphism_inverse hD)).
- move=>x hx;split;first exact:(@holomorphic_diffeomorphism_maps R X NX hNX A B f g hD x (hWA x hx)).
  by rewrite (@holomorphic_diffeomorphism_left_inverse R X NX hNX A B f g hD x (hWA x hx)).
- by move=>x hx;exact:hx.2.
- move=>x hx;exact:(@holomorphic_diffeomorphism_left_inverse R X NX hNX A B f g hD x (hWA x hx)).
- move=>y hy;exact:(@holomorphic_diffeomorphism_right_inverse R X NX hNX A B f g hD y hy.1).
Qed.
