(** Federer (1969), 4.1.8, p. 362: scalar
    endpoint pairs as original segment factors. Their
    finite product has one coordinate for each
    factor and retains the original full containing domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanCartesianMap
  ScalarSegmentCoordinateValues OrientedSegmentFactor OrientedRectangleDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_segment_factor]: each original
    scalar pair u_k,v_k determines the original
    one-dimensional segment factor, supporting the final
    product display of Federer 4.1.8, p. 362.
    Ordering is a hypothesis of that identity,
    not of the segment's definition. *)
Definition scalar_segment_factor (R:realType) (p:R*R):oriented_segment_factor R:={|
  oriented_segment_factor_dimension:=1%N;
  oriented_segment_factor_domain:=fun _=>True;
  oriented_segment_factor_open:=fun x (_:True)=>@norm_full_domain_interior R (R_n R 1%N)
    (inner_norm (@euclidean_inner_productP R 1%N)) x;
  oriented_segment_factor_start:=@euclidean_one_embed R p.1;
  oriented_segment_factor_end:=@euclidean_one_embed R p.2;
  oriented_segment_factor_contains:=@scalar_segment_full_domain R p.1 p.2
|}.

(** Source for [scalar_segment_factors]: the original
    finite ordered family of scalar segments,
    supporting Federer 4.1.8, p. 362. *)
Definition scalar_segment_factors (R:realType) (f:seq (R*R)):=
  [seq @scalar_segment_factor R p|p<-f].

(** Source for [scalar_rectangle_dimension]: the original
    ambient dimension is exactly the number of
    scalar factors, supporting E^nu in the final
    display of Federer 4.1.8, p. 362. *)
Lemma scalar_rectangle_dimension (R:realType) (f:seq (R*R)):
  oriented_rectangle_dimension (@scalar_segment_factors R f)=size f.
Proof.
elim:f=>[|a t IH].
- by [].
- case:t IH=>[|b t] IH;first by [].
  change ((1+oriented_rectangle_dimension (@scalar_segment_factors R (b::t)))%N=
    (1+size (b::t))%N).
  by rewrite IH.
Qed.

(** Source for [scalar_rectangle_domain_whole]: the original
    full scalar containing domains have the whole
    concatenated Euclidean space as their finite
    Cartesian product, supporting Federer 4.1.8, p. 362. *)
Lemma scalar_rectangle_domain_whole (R:realType) (f:seq (R*R)):
  forall x,@oriented_rectangle_domain R (@scalar_segment_factors R f) x.
Proof.
elim:f=>[|a t IH].
- move=>x;exact:Logic.I.
- case:t IH=>[|b t] IH.
  + move=>x;exact:Logic.I.
  + move=>x.
    change (True /\ @oriented_rectangle_domain R (@scalar_segment_factors R (b::t))
      (euclidean_block_split x).2).
    split;first exact:Logic.I.
    exact:IH.
Qed.

(** Source for [scalar_rectangle_ordered]: every original
    scalar pair has u_k<v_k, precisely the
    hypothesis in the final display of Federer
    4.1.8, p. 362. *)
Definition scalar_rectangle_ordered (R:realType) (f:seq (R*R)):=
  all (fun p:R*R=>p.1<p.2) f.
