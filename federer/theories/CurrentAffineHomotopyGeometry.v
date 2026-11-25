(** Federer (1969), 4.1.13, pp. 369–370: turn the
    original affine formula and an established image bound
    into the smooth homotopy of 4.1.9, p. 363.
    The neighbourhood theorem establishes this image bound
    from the printed support-only hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockLinearMaps
  CurrentHomotopyUP CurrentHomotopyGeometry CurrentAffineHomotopyUP
  CurrentAffineHomotopySealed CurrentAffineHomotopyClass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentAffineHomotopyGeometry.
Variable R:realType.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variable A:set R.
Hypothesis hA:@is_homotopy_parameter_interval R A.
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variables f g:X->Y.
Hypothesis hf:norm_class_all_orders hNX hNY U f.
Hypothesis hg:norm_class_all_orders hNX hNY U g.
Hypothesis hImage:forall t x,A t->U x->V ((1-t)*:f x+t*:g x).
Local Notation H := (@CurrentAffineHomotopy.value R n nu f g).

(** Source for [current_affine_homotopy_in_target]: the original
    affine homotopy used after the source-neighbourhood replacement
    in Federer 4.1.13, pp. 369–370. Its image premise
    is proved by compactness for that smaller source. *)
Definition current_affine_homotopy_in_target:
  @is_smooth_current_homotopy R n nu A U V f g H.
Proof.
refine (conj
  (@Build_is_current_homotopy_geometry R n nu A U V f g H hA hU hV _ _ _)
  (@current_affine_homotopy_smooth R n nu f g A hA U hU hf hg)).
- move=>z [ht hx].
  rewrite current_affine_homotopy_coordinates.
  exact:hImage _ _ ht hx.
- move=>x _;exact:(current_affine_homotopy_start (CurrentAffineHomotopy.laws f g) x).
- move=>x _;exact:(current_affine_homotopy_end (CurrentAffineHomotopy.laws f g) x).
Defined.
End CurrentAffineHomotopyGeometry.

(** Source for [current_affine_ambient_homotopy]: the original
    affine formula is a smooth homotopy on R times U
    into the whole ambient target, supporting compactness
    of C in Federer 4.1.13, p. 369. This statement
    makes no global image claim about the original open V. *)
Definition current_affine_ambient_homotopy (R:realType) n nu
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (f g:R_n R n->R_n R nu)
    (hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U f)
    (hg:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R nu)) U g):
  @is_smooth_current_homotopy R n nu (fun _=>True) U (fun _=>True) f g
    (@CurrentAffineHomotopy.value R n nu f g).
Proof.
refine (@current_affine_homotopy_in_target R n nu (fun _=>True) _
  U (fun _=>True) hU
  (fun y _=>@norm_full_domain_interior R (R_n R nu)
    (inner_norm (@euclidean_inner_productP R nu)) y) f g hf hg
  (fun t x _ _=>Logic.I)).
constructor;first exact:openT;by [].
Defined.
