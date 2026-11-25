(** Federer (1969), 3.2.28(1), printed p. 263:
    the continuous actual differential field of the
    Gram map with its symmetric codomain. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier
  GrassmannAbbreviations InnerNorm HilbertFormCompactness NormedSubspace
  EuclideanHomInnerCharts EuclideanSymmetricEndomorphismSpace
  EuclideanSymmetricGram EuclideanSymmetricGramSmooth
  NormClassOneUP NormRegularity NormDifferentialDirectional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_symmetric_gram_class_one_field]:
    the actual DP(g) varies continuously, supporting
    the regular-level argument in Federer 3.2.28(1),
    p. 263. Uniqueness identifies the displayed field
    with the field supplied by the proved smoothness theorem. *)
Theorem euclidean_symmetric_gram_class_one_field (R:realType) m n:
  is_norm_class_one_field
    (inner_norm (@euclidean_hom_inner_productP R m n))
    (subspace_norm (inner_norm (@euclidean_hom_inner_productP R m m))
      (@euclidean_symmetric_hom_subspace R m))
    (fun _=>True) (@euclidean_symmetric_gram R m n)
    (@euclidean_symmetric_gram_differential R m n).
Proof.
pose NX:=inner_norm (@euclidean_hom_inner_productP R m n).
pose NE:=inner_norm (@euclidean_hom_inner_productP R m m).
pose NY:=subspace_norm NE (@euclidean_symmetric_hom_subspace R m).
pose hNX:=inner_norm_real_norm (@euclidean_hom_inner_productP R m n).
pose hNY:=subspace_norm_laws
  (inner_norm_real_norm (@euclidean_hom_inner_productP R m m))
  (@euclidean_symmetric_hom_subspace R m).
have [D hD]:=(norm_class_firstP hNX hNY (fun _=>True)
  (@euclidean_symmetric_gram R m n)).1 (@euclidean_symmetric_gram_smooth R m n 1%N).
have hEq:D=@euclidean_symmetric_gram_differential R m n.
  apply:funext=>g.
  exact:(norm_differential_unique hNX hNY
    (norm_class_one_differential hD I) (@euclidean_symmetric_gram_has_differential R m n g)).
by rewrite -hEq.
Qed.
