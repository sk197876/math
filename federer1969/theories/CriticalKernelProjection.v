(** Federer (1969), 3.4.3, p. 317: prove existence
    of the original orthogonal coordinates on the kernel. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerProductLaws InnerPolarity EuclideanKernelFrameUP EuclideanKernelFrameExistence
  GramSchmidt OrthonormalisationUP OrthonormalFrameMap FrameImageSpan
  AdjointUP Adjoint AdjointLaws CriticalKernelProjectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [critical_kernel_projection_exists]: the choice
    q in O*(m,m-nu) with im q*=ker Df(a),
    3.4.3, p. 317. The proved epimorphism kernel frame,
    orthonormalisation with preserved span, and sealed adjoint
    supply the original q. All witnesses remain local; rank
    zero and zero-dimensional kernel coordinates are included. *)
Theorem critical_kernel_projection_exists (R:realType) nu l
    (alpha:Hom (R_n R (nu+l)) (R_n R nu)):
  (forall y,exists x,alpha x=y) ->
  exists (q:{linear R_n R (nu+l)->R_n R l})
    (j:{linear R_n R l->R_n R (nu+l)}),is_critical_kernel_projection alpha q j.
Proof.
move=>hSurj.
have [e [he hKernel]]:=euclidean_epimorphism_kernel_frame_exists hSurj.
pose BX:=@euclidean_inner_product R (nu+l).
pose hBX:=@euclidean_inner_productP R (nu+l).
pose BV:=@euclidean_inner_product R l.
pose hBV:=@euclidean_inner_productP R l.
have [v hv]:=gram_schmidt_exists hBX he.
have [j [hJ hJE]]:=orthonormal_frame_map_exists hBX (orthonormalisation_orthonormal hv).
pose q:=inner_adjoint hBV hBX (@coordinate_basisP R l) j.
have hq:is_adjoint BV BX j q:=inner_adjointP _ _ _ _.
exists q,j;constructor;[exact:hJ|exact:hq|].
move=>x;rewrite hKernel (orthonormalisation_span hv).
exact:iff_sym (basis_image_finite_span (@coordinate_basisP R l) hJE x).
Qed.

(** Source for [critical_kernel_projection_kernel_intersection]:
    ker(L Df(a)) intersect ker q is zero in
    3.4.3, p. 317. On the original kernel, q*
    parametrises every vector and q q* is the identity. *)
Lemma critical_kernel_projection_kernel_intersection (R:realType) nu l
    (alpha:Hom (R_n R (nu+l)) (R_n R nu))
    (q:{linear R_n R (nu+l)->R_n R l})
    (j:{linear R_n R l->R_n R (nu+l)}):
  is_critical_kernel_projection alpha q j ->
  forall x,alpha x=0 ->q x=0 ->x=0.
Proof.
move=>h x hAlpha hQ.
have [u hu]:=(critical_kernel_projection_image h x).1 hAlpha.
have hCancel:cancel j q.
  move=>v;apply:(inner_vectors_ext (@euclidean_inner_productP R l))=>w.
  by rewrite (critical_kernel_projection_adjoint h) (critical_kernel_projection_orthogonal h).
have hU:u=0 by have hh:=congr1 q hu;rewrite hCancel hQ in hh.
by rewrite -hu hU linear0.
Qed.
