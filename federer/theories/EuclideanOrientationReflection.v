(** Federer (1969), 3.2.28(2), printed p. 265:
    SO(m) has half the measure of O(m), for m>0.
    This supporting existence theorem supplies an actual
    orthogonal involution of determinant minus one, using
    only the coordinate determinant law of 1.3.4, p. 16. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp ring.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanLinearMaps OrthogonalMaps ExteriorDeterminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_orientation_reflection_exists]:
    an orientation-reversing orthogonal involution exchanges
    the two components of O(m), supporting the half-volume
    assertion in Federer 3.2.28(2), p. 265. Positive
    m is necessary; in degree zero O(0)=SO(0) is a singleton. *)
Theorem euclidean_orientation_reflection_exists (R:realType) m:
  (0<m)%N ->exists r:Hom (R_n R m) (R_n R m),
    is_orthogonal_map (@euclidean_inner_product R m)
      (@euclidean_inner_product R m) (hom_as_linear r) /\
    cancel r r /\
    det (euclidean_two_nonzero R) (@coordinate_basisP R m) (hom_as_linear r)= -1.
Proof.
move=>hm.
pose i0:'I_m:=Ordinal hm.
pose c (i:'I_m):R:=if i==i0 then -1 else 1.
pose r:=hom_of_linear (euclidean_diagonal_map c).
have hE x i:r x i=c i*x i.
  by rewrite /r hom_of_linearE /euclidean_diagonal_map /euclidean_diagonal /= ffunE.
have hC i:c i*c i= 1.
  rewrite /c; case:ifP=>_; by rewrite ?mulrNN mulr1.
exists r; split.
- move=>x y; rewrite /euclidean_inner_product.
  apply:eq_bigr=>i _; rewrite !hE.
  have heq:(c i*x i)*(c i*y i)=(c i*c i)*(x i*y i) by ring.
  by rewrite heq hC mul1r.
split.
- move=>x; apply/ffunP=>i.
  by rewrite !hE mulrA hC mul1r.
- have he:hom_as_linear r=1 euclidean_diagonal_map c by move=>x; exact:hom_of_linearE.
  rewrite (@det_ext R (euclidean_two_nonzero R) m (R_n R m) (@coordinate_basis R m)
    (@coordinate_basisP R m) (hom_as_linear r) (euclidean_diagonal_map c) he).
  change (euclidean_det (euclidean_diagonal_map c)= -1).
  rewrite euclidean_diagonal_det (bigD1 i0) //= /c eqxx.
  have hRest:(\prod_(i<m|i!=i0) (if i==i0 then -1 else 1:R))= 1.
    apply:big1=>i hi; by rewrite (negbTE hi).
  by rewrite hRest mulr1.
Qed.
