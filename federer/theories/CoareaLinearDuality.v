(** Federer (1969), 3.2.11, p. 249: the
    critical rank condition and a unit covector annihilating
    the differential. Use the already proved adjoint and
    top exterior norm laws of 1.7.4–1.7.6. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom Bilinear GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps EuclideanLinearJacobian EuclideanRectangularAdjoint
  ExteriorOperatorNorm TopTargetExteriorNorm InnerNorm InnerNormalization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_target_jacobian_adjoint]: supporting
    duality calculation in Federer 3.2.11, p. 249.
    J_n D is the top-source Jacobian of its adjoint,
    by 1.7.6, pp. 33–34; all dimensions are retained. *)
Lemma euclidean_target_jacobian_adjoint (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)):
  euclidean_linear_jacobian n D=
    euclidean_linear_jacobian n (euclidean_rectangular_adjoint D).
Proof.
exact (@exterior_operator_adjoint_norm_equal R (euclidean_two_nonzero R)
  (R_n R m) (R_n R n) (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) m n
  (@coordinate_basis R m) (@coordinate_basis R n)
  (@coordinate_basisP R m) (@coordinate_basisP R n) (hom_as_linear D)
  (hom_as_linear (euclidean_rectangular_adjoint D)) (euclidean_rectangular_adjoint_pairing D) n).
Qed.

(** Source for [euclidean_target_jacobian_positive_iff_surjective]:
    the two rank alternatives in Federer 3.2.11, p. 249.
    The positive target-degree Jacobian is equivalent to an
    epimorphism, by 1.7.6, p. 34, including target dimension zero. *)
Lemma euclidean_target_jacobian_positive_iff_surjective (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)):
  0<euclidean_linear_jacobian n D <->forall y,exists x,D x=y.
Proof.
exact (@top_target_norm_positive_iff_surjective R (euclidean_two_nonzero R)
  (R_n R m) (R_n R n) (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) m n
  (@coordinate_basis R m) (@coordinate_basis R n)
  (@coordinate_basisP R m) (@coordinate_basisP R n) (hom_as_linear D)).
Qed.

(** Source for [critical_differential_unit_annihilator]: the
    nonzero covector in ker Df* used to bound J_n g
    in Federer 3.2.11, p. 249. The supporting witness
    is normalized inside a local existence proof, using the
    existing sealed adjoint and elementary normalization laws. *)
Lemma critical_differential_unit_annihilator (R:realType) m n
    (D:Hom (R_n R m) (R_n R n)):
  euclidean_linear_jacobian n D=0 ->exists b:R_n R n,
    euclidean_inner_product b b= 1 /\ euclidean_rectangular_adjoint D b=0.
Proof.
move=>hD; pose A:=euclidean_rectangular_adjoint D.
have hKernel:exists b:R_n R n,b!=0 /\ A b=0.
  apply:contrapT=>hEmpty.
  have hInj:injective A.
    move=>x y hEq.
    have hZero:A (x-y)=0.
      have hDiff:=linearB (hom_as_linear A) x y.
      change (A (x-y)=A x-A y) in hDiff.
      by rewrite hDiff hEq subrr.
    have hxy:x-y=0.
      apply:contrapT=>hNe; apply:hEmpty; exists (x-y); split; last exact hZero.
      apply/eqP=>h; exact (hNe h).
    move/eqP:hxy; by rewrite subr_eq0=>/eqP.
  have hPos:0<euclidean_linear_jacobian n A:=(euclidean_linear_jacobian_top_positive A).2 hInj.
  have hDual:=euclidean_target_jacobian_adjoint D.
  change (euclidean_linear_jacobian n D=euclidean_linear_jacobian n A) in hDual.
  by rewrite -hDual hD ltxx in hPos.
have [b [hb hZero]]:=hKernel.
exists (inner_normalize (@euclidean_inner_productP R n) b); split.
- exact (inner_normalize_square (@euclidean_inner_productP R n) hb).
- change (A (inner_normalize (@euclidean_inner_productP R n) b)=0).
  have hScale:=linZ (hom_linear A) (inner_norm (@euclidean_inner_productP R n) b)^-1 b.
  change (A ((inner_norm (@euclidean_inner_productP R n) b)^-1*:b)=
    (inner_norm (@euclidean_inner_productP R n) b)^-1*:A b) in hScale.
  by rewrite /inner_normalize hScale hZero scaler0.
Qed.
