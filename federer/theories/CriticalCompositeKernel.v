(** Federer (1969), 3.4.2(7), p. 314: the cutting projection
    q composed with p still has its kernel in the fixed subspace. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations EuclideanProjectionSpace
  EuclideanProjectionComposition CriticalManifoldFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_composite_projection_kernel]: the
    calculation ker(q p) contained in Z in 3.4.2(7), p. 314.
    If q(p(w))=0, then p(w)=t p(z), so w-tz lies in ker p
    and hence in Z. Both summands then belong to Z. The
    composite is an actual orthogonal projection by 1.7.4. *)
Theorem critical_composite_projection_kernel (R:realType) m mu gamma k
    (Z:subspace (R_n R m)) (S:set (R_n R m))
    (p:euclidean_projection_space R m mu) g
    (q:euclidean_projection_space R mu gamma) z:
  is_critical_manifold_chart k Z S p g ->Z z ->
  (forall w,euclidean_projection_linear q w=0 ->
    exists t:R,w=t*:euclidean_projection_linear p z) ->
  exists r:euclidean_projection_space R m gamma,
    (forall w,euclidean_projection_linear r w=
      euclidean_projection_linear q (euclidean_projection_linear p w)) /\
    forall w,euclidean_projection_linear r w=0 ->Z w.
Proof.
move=>hChart hz hKernel.
have [C hC]:=@euclidean_projection_composition_exists R m mu gamma.
pose r:=C (q,p).
exists r;split;first exact:(hC q p).
move=>w hw.
have hQ:euclidean_projection_linear q (euclidean_projection_linear p w)=0.
  by rewrite -(hC q p w).
have [t ht]:=hKernel (euclidean_projection_linear p w) hQ.
have hSmall:euclidean_projection_linear p (w-t*:z)=0.
  by rewrite linearB linearZ ht subrr.
have hFirst:=critical_chart_kernel hChart hSmall.
have hSecond:=subspace_scale t hz.
have hSum:=subspace_add hFirst hSecond.
by rewrite subrK in hSum.
Qed.
