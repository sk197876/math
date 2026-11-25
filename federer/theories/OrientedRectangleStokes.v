(** Federer (1969), 4.1.8, p. 362: Stokes'
    theorem for the original oriented rectangular
    parallelepiped. Follow the printed induction using
    only the original segment and binary boundary laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear CurrentSpaces CurrentBoundary CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentCartesianBoundaryPositive
  OrientedSegmentFactor OrientedRectangleDomain OrientedRectangleSpaces
  OrientedRectangleCurrentUP OrientedRectangleCurrentSealed OrientedRectangleStokesSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section OrientedRectangleStokes.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation Factor := (oriented_segment_factor R).
Local Notation Product := (@oriented_rectangle_product R h2).
Local Notation P := (@OrientedRectangleCurrent.value R h2).
Local Notation S := (@oriented_segment_factor_current R h2).
Local Notation Delta := (@oriented_segment_factor_endpoint_difference R h2).
Local Notation Sum := (@oriented_rectangle_stokes_sum R h2).
Local Notation bd := (fun f k=>@current_boundary R h2 (oriented_rectangle_dimension f) k
  (@oriented_rectangle_domain R f) (@oriented_rectangle_domain_open R f)).

(** Source for [oriented_rectangle_stokes]: the original
    boundary of [u_1,v_1] times ... times [u_nu,v_nu]
    is the sum of the original endpoint-difference
    faces with exactly (-1)^k, k=1,...,nu,
    Federer 4.1.8, p. 362. Every factor may
    have its own Euclidean dimension and open domain.
    A boundary is taken only for a nonempty family. *)
Theorem oriented_rectangle_stokes (a:Factor) (t:seq Factor):
  bd (a::t) (size t) (P (a::t))=Sum (a::t).
Proof.
elim:t a=>[|b t hTail] a.
- rewrite ((@OrientedRectangleCurrent.laws R h2).2.1 a)
    oriented_rectangle_stokes_sum_single.
  exact:oriented_segment_factor_boundary.
- have h:=@current_cartesian_boundary_positive R h2 (oriented_segment_factor_dimension a)
    (oriented_rectangle_dimension (b::t)) (@oriented_segment_factor_domain R a)
    (@oriented_rectangle_domain R (b::t)) (@oriented_segment_factor_open R a)
    (@oriented_rectangle_domain_open R (b::t)) 0%N (size t) (S a) (P (b::t)).
  rewrite !current_degree_transport_identity expr1 scaleN1r oriented_segment_factor_boundary in h.
  change (bd (a::b::t) (size (b::t))
      (Product a b t 1%N (size (b::t)) (S a) (P (b::t)))=
    Product a b t 0%N (size (b::t)) (-Delta a) (P (b::t))-
    Product a b t 1%N (size t) (S a) (bd (b::t) (size t) (P (b::t)))) in h.
  have hNeg:=bilZl (@oriented_rectangle_product_bilinear R h2 a b t 0%N (size (b::t)))
    (-1:R) (Delta a) (P (b::t)).
  rewrite !scaleN1r in hNeg.
  rewrite hNeg (hTail b) in h.
  rewrite ((@OrientedRectangleCurrent.laws R h2).2.2 a b t) oriented_rectangle_stokes_sum_cons.
  exact:h.
Qed.
End OrientedRectangleStokes.
