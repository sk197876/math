(** Federer (1969), 4.1.8, p. 360: A times B is the original
    open Cartesian domain. Its coordinates are the existing orthogonal
    block projections of 2.6.5, p. 120. Openness follows from the
    earlier bounded-linear inverse-image and intersection laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormFiniteLinearBound
  NormLinearDomainLaws InnerNorm HilbertFormCompactness LinearBasis
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_cartesian_domain_coordinates]: the two displayed
    coordinate projections p and q in Federer 4.1.8, p. 360. Membership
    in A times B means membership of each original block in its factor. *)
Lemma current_cartesian_domain_coordinates (R:realType) m n
    (A:set (R_n R m)) (B:set (R_n R n)) (z:R_n R (m+n)):
  euclidean_cartesian_set A B z <->
    A (@euclidean_first_block_map R m n z) /\
    B (@euclidean_last_block_map R m n z).
Proof. by []. Qed.

(** Source for [current_cartesian_domain_open]: the opening hypotheses
    and Cartesian domain in Federer 4.1.8, p. 360. This supporting
    implication uses the original norms and includes empty blocks and
    empty factor domains. No product openness premise is added. *)
Theorem current_cartesian_domain_open (R:realType) m n
    (A:set (R_n R m)) (B:set (R_n R n)):
  (forall a,A a->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R m)) A a)->
  (forall b,B b->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R n)) B b)->
  forall z,euclidean_cartesian_set A B z->
    norm_domain_interior (inner_norm (@euclidean_inner_productP R (m+n)))
      (euclidean_cartesian_set A B) z.
Proof.
move=>hA hB z hz.
pose X:=R_n R m.
pose Y:=R_n R n.
pose Z:=R_n R (m+n).
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose NZ:=inner_norm (@euclidean_inner_productP R (m+n)).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNZ:=inner_norm_real_norm (@euclidean_inner_productP R (m+n)).
pose p:=@euclidean_first_block_map R m n.
pose q:=@euclidean_last_block_map R m n.
have [hzA hzB]:=(@current_cartesian_domain_coordinates R m n A B z).1 hz.
have hP:=@norm_finite_linear_bounded R Z X NZ NX hNZ hNX (m+n)%N
  (@coordinate_basis R (m+n)) (@coordinate_basisP R (m+n)) p.
have hQ:=@norm_finite_linear_bounded R Z Y NZ NY hNZ hNY (m+n)%N
  (@coordinate_basis R (m+n)) (@coordinate_basisP R (m+n)) q.
have hFirst:=@norm_bounded_linear_preimage_interior R Z X NZ NX hNZ p A z
  hP (@hA (p z) hzA).
have hLast:=@norm_bounded_linear_preimage_interior R Z Y NZ NY hNZ q B z
  hQ (@hB (q z) hzB).
change (norm_domain_interior NZ (fun w=>A (p w)/\B (q w)) z).
exact:(@norm_domain_intersection_interior R Z NZ
  (fun w=>A (p w)) (fun w=>B (q w)) z hFirst hLast).
Qed.
