(** Federer (1969), 4.1.8, p. 360: for fixed b,
    the first-variable map a to (a,b) has differential P.
    These supporting laws use the original block maps and
    earlier linear, constant and sum calculus. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialArithmetic NormFiniteLinearBound NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianAffineSlice.
Variable R:realType.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation P := (@euclidean_first_injection_map R m n).
Local Notation Q := (@euclidean_last_injection_map R m n).

(** Source for [current_cartesian_join_affine]: (a,b)=P(a)+Q(b),
    using exactly the two injections displayed in Federer
    4.1.8, p. 360. This reuses the preceding block decomposition. *)
Lemma current_cartesian_join_affine (a:X) (b:Y):
  @euclidean_block_join R m n (a,b)=(P a:Z)+(Q b:Z).
Proof.
have h:=@euclidean_block_linear_decomposition R m n (@euclidean_block_join R m n (a,b)).
have hFirst:@euclidean_first_block R m n (@euclidean_block_join R m n (a,b))=a.
  change ((@euclidean_block_split R m n (@euclidean_block_join R m n (a,b))).1=a).
  by rewrite euclidean_block_joinK.
have hLast:@euclidean_last_block R m n (@euclidean_block_join R m n (a,b))=b.
  change ((@euclidean_block_split R m n (@euclidean_block_join R m n (a,b))).2=b).
  by rewrite euclidean_block_joinK.
rewrite hFirst hLast in h;exact:h.
Qed.

(** Source for [current_cartesian_affine_slice_image]: for b
    in B, the original slice of Federer 4.1.8, p. 360,
    carries A into A times B, with no condition that B contain zero. *)
Lemma current_cartesian_affine_slice_image (A:set X) (B:set Y) b:
  B b->forall a,A a->euclidean_cartesian_set A B (@euclidean_block_join R m n (a,b)).
Proof.
move=>hb a ha.
change (A (euclidean_block_split (euclidean_block_join (a,b))).1 /\
  B (euclidean_block_split (euclidean_block_join (a,b))).2).
by rewrite euclidean_block_joinK;split.
Qed.

Variable A:set X.
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.

(** Source for [current_cartesian_affine_slice_smooth]: the
    fixed-b slice in the definition of phi_S is smooth
    on the original A, supporting Federer 4.1.8, p. 360. *)
Theorem current_cartesian_affine_slice_smooth (b:Y):
  norm_class_all_orders hNX hNZ A (fun a=>@euclidean_block_join R m n (a,b)).
Proof.
have hFun:(fun a:X=>@euclidean_block_join R m n (a,b))=(fun a=>(P a:Z)+(Q b:Z)).
  apply:funext=>a;exact:current_cartesian_join_affine.
have hP:=@norm_finite_linear_bounded R X Z NX NZ hNX hNZ m
  (@coordinate_basis R m) (@coordinate_basisP R m) P.
move=>k;rewrite hFun.
apply:(@norm_class_add R X Z NX NZ hNX hNZ A P (fun _=>Q b) k).
- exact:(@norm_class_linear R X Z NX NZ hNX hNZ A P k hA hP).
- exact:(@norm_class_constant R X Z NX NZ hNX hNZ A (Q b) k hA).
Qed.

(** Source for [current_cartesian_affine_slice_differential]: the
    actual differential in the first variables is P, supporting
    the slice pullback in Federer 4.1.8, p. 360. *)
Theorem current_cartesian_affine_slice_differential (b:Y) a:
  A a->has_norm_differential NX NZ A
    (fun x=>@euclidean_block_join R m n (x,b)) a P.
Proof.
move=>ha.
have hFun:(fun x:X=>@euclidean_block_join R m n (x,b))=(fun x=>(P x:Z)+(Q b:Z)).
  apply:funext=>x;exact:current_cartesian_join_affine.
have hP:=@norm_finite_linear_bounded R X Z NX NZ hNX hNZ m
  (@coordinate_basis R m) (@coordinate_basisP R m) P.
have hLinear:=@norm_differential_linear R X Z NX NZ hNX hNZ A a P (@hA a ha) hP.
have hConstant:=@norm_differential_constant R X Z NX NZ hNX hNZ A a (Q b) (@hA a ha).
have hSum:=@norm_differential_add R X Z NX NZ hNZ A P (fun _=>Q b) a P 0 hLinear hConstant.
rewrite addr0 in hSum;rewrite hFun;exact:hSum.
Qed.
End CurrentCartesianAffineSlice.
