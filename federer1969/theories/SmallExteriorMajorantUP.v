(** Federer (1969), 3.2.31, p. 269: independent laws
    for the symmetric automorphism with small exterior norm
    used to rescale a low-rank actual differential. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  SymmetricEndomorphisms EuclideanLinearJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_small_exterior_majorant]: the small
    symmetric automorphism t in Federer 3.2.31, p. 269.
    Specify symmetry, an actual two-sided inverse, exterior
    norm below epsilon and contraction of the prescribed linear
    map after inverse rescaling. The supporting contraction
    constant one half is stronger than the printed strict unit
    bound and permits a direct class-one neighborhood argument.
    Existence must be proved separately; no witness is selected. *)
Record is_small_exterior_majorant (R:realType) m v mu
    (D:Hom (R_n R m) (R_n R v)) (epsilon:R)
    (T U:Hom (R_n R v) (R_n R v)):Prop:={
  (** Source for [small_exterior_majorant_symmetric]: symmetry
      of t in Federer 3.2.31, p. 269. *)
  small_exterior_majorant_symmetric:is_symmetric_endomorphism
    (@euclidean_inner_product R v) (hom_as_linear T);
  (** Source for [small_exterior_majorant_left_inverse]: one
      inverse law of the automorphism in 3.2.31, p. 269. *)
  small_exterior_majorant_left_inverse:cancel T U;
  (** Source for [small_exterior_majorant_right_inverse]: the
      other inverse law of the automorphism in 3.2.31, p. 269. *)
  small_exterior_majorant_right_inverse:cancel U T;
  (** Source for [small_exterior_majorant_small_norm]: the
      displayed norm(Lambda^mu t)<epsilon condition in
      Federer 3.2.31, p. 269, using the actual operator norm. *)
  small_exterior_majorant_small_norm:euclidean_linear_jacobian mu T<epsilon;
  (** Source for [small_exterior_majorant_contraction]: a
      supporting stronger inverse-rescaled derivative bound
      for the local unit Lipschitz estimate in 3.2.31, p. 269. *)
  small_exterior_majorant_contraction:forall x,
    inner_norm (@euclidean_inner_productP R v) (U (D x))<=
      (1/2)*inner_norm (@euclidean_inner_productP R m) x
}.
