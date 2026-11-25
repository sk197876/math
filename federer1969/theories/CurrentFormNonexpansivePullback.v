(** Federer (1969), 4.1.8, p. 361: original
    coordinate pullbacks contract comass. Apply the actual
    induced multilinear norm of 4.1.6, p. 352, to
    nonexpansive original maps, including degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct AlternatingForms AlternatingDual AlternatingFormUnitBounds
  CurrentCoefficientNorms CurrentFormInducedNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_comass_nonexpansive_pullback]: the
    original nonexpansive pullback contracts actual comass
    in every degree, supporting Federer 4.1.8, p. 361,
    by 1.8.1, p. 39, and the scalar endpoint. *)
Theorem current_comass_nonexpansive_pullback (R:realType) (h2:(1+1:R)!=0) m n
    (f:{linear R_n R m->R_n R n})
    (hContract:forall x,inner_norm (@euclidean_inner_productP R n) (f x)<=
      inner_norm (@euclidean_inner_productP R m) x)
    d (phi:A_m (R_n R n) R^o d):
  @current_form_comass R h2 m d (A_m_dual f phi)<=@current_form_comass R h2 n d phi.
Proof.
apply:(@alternating_form_unit_tuple_least R (R_n R m) R^o
  (inner_norm (@euclidean_inner_productP R m)) (fun a:R^o=>`|a|)
  (inner_norm_real_norm (@euclidean_inner_productP R m)) (@scalar_absolute_value_norm R)
  d (A_m_dual f phi) _ ((@current_form_comass_is_induced R h2 m d) (A_m_dual f phi))
  (@current_form_comass R h2 n d phi)).
- exact:real_seminorm_nonnegative (@current_form_comass_real_norm R h2 n d).1 phi.
- move=>t hUnit;rewrite A_m_dualE.
  apply:(@alternating_form_unit_tuple_bound R (R_n R n) R^o
    (inner_norm (@euclidean_inner_productP R n)) (fun a:R^o=>`|a|)
    (inner_norm_real_norm (@euclidean_inner_productP R n)) d phi _
    ((@current_form_comass_is_induced R h2 n d) phi) (map_tuple f t)).
  move=>k;rewrite tnth_map;exact:le_trans (hContract _) (hUnit k).
Qed.
