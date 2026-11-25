(** Federer (1969), 4.1.8, p. 362: the
    original finite Cartesian domain of the segment
    factors. Derived products use the existing block
    identification. Single factors retain their original
    domain; the empty family has the original R^0 domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentCartesianDomain OrientedSegmentFactor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section OrientedRectangleDomain.
Variable R:realType.
Local Notation Factor := (oriented_segment_factor R).

(** Source for [oriented_rectangle_dimension]: the
    total Euclidean dimension of the original finite
    product, supporting Federer 4.1.8, p. 362.
    It adds the original factor dimensions. *)
Fixpoint oriented_rectangle_dimension (f:seq Factor):nat:=
  match f with
  |[::]=>0%N
  |a::t=>match t with
    |[::]=>oriented_segment_factor_dimension a
    |_::_=>(oriented_segment_factor_dimension a+oriented_rectangle_dimension t)%N
    end
  end.

(** Source for [oriented_rectangle_domain_step]: attach the
    original first factor to a nonempty remaining
    Cartesian domain; a singleton retains its original
    domain, supporting Federer 4.1.8, p. 362. *)
Definition oriented_rectangle_domain_step (a:Factor) (t:seq Factor):
    set (R_n R (oriented_rectangle_dimension t))->
      set (R_n R (oriented_rectangle_dimension (a::t))):=
  match t as q return set (R_n R (oriented_rectangle_dimension q))->
      set (R_n R (oriented_rectangle_dimension (a::q))) with
  |[::]=>fun _=>@oriented_segment_factor_domain R a
  |b::s=>fun B=>@euclidean_cartesian_set R (oriented_segment_factor_dimension a)
      (oriented_rectangle_dimension (b::s)) (@oriented_segment_factor_domain R a) B
  end.

(** Source for [oriented_rectangle_domain]: the original
    Cartesian product of all containing domains,
    supporting the finite-product Stokes display in
    Federer 4.1.8, p. 362. No assertion about
    currents or their boundaries is assumed. *)
Fixpoint oriented_rectangle_domain (f:seq Factor):set (R_n R (oriented_rectangle_dimension f)):=
  match f as g return set (R_n R (oriented_rectangle_dimension g)) with
  |[::]=>setT
  |a::t=>@oriented_rectangle_domain_step a t (@oriented_rectangle_domain t)
  end.

(** Source for [oriented_rectangle_domain_open_step]: the
    original binary product preserves openness, while
    a singleton uses its original open domain,
    supporting Federer 4.1.8, p. 362. *)
Definition oriented_rectangle_domain_open_step (a:Factor) (t:seq Factor):
    (forall x,@oriented_rectangle_domain t x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R (oriented_rectangle_dimension t)))
      (@oriented_rectangle_domain t) x)->
    forall x,@oriented_rectangle_domain (a::t) x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R (oriented_rectangle_dimension (a::t))))
      (@oriented_rectangle_domain (a::t)) x.
Proof.
case:t=>[|b t] hTail.
- exact:(@oriented_segment_factor_open R a).
- exact:(@current_cartesian_domain_open R (oriented_segment_factor_dimension a)
    (oriented_rectangle_dimension (b::t)) (@oriented_segment_factor_domain R a)
    (@oriented_rectangle_domain (b::t)) (@oriented_segment_factor_open R a) hTail).
Defined.

(** Source for [oriented_rectangle_domain_open]: the
    original finite product domain is open, supporting
    its actual test spaces in Federer 4.1.8,
    p. 362. This follows from the original binary
    Cartesian openness, including the empty family. *)
Fixpoint oriented_rectangle_domain_open (f:seq Factor):
    forall x,@oriented_rectangle_domain f x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R (oriented_rectangle_dimension f)))
      (@oriented_rectangle_domain f) x:=
  match f as g return forall x,@oriented_rectangle_domain g x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R (oriented_rectangle_dimension g)))
      (@oriented_rectangle_domain g) x with
  |[::]=>fun x _=>norm_full_domain_interior
      (inner_norm (@euclidean_inner_productP R 0%N)) x
  |a::t=>@oriented_rectangle_domain_open_step a t (@oriented_rectangle_domain_open t)
  end.
End OrientedRectangleDomain.
