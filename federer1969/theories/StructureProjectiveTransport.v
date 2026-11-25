(** Federer (1969), 3.3.4, p. 290: an actual
    orthogonal map of the active space induces an
    isometric action on its projective unit-sphere image.
    The action is the previously sealed symmetric-power
    functor; no new selected line representative is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import TensorUP InnerProductUP InnerNorm OrthogonalMaps
  SymmetricGrading SymmetricFormIsomorphism SymmetricMaps SymmetricMassMapBound InnerSymmetricPositivity
  SymmetricSquareGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [structure_projective_square_natural]:
    T(gx) is the induced action of g on T(x),
    supporting Federer 3.3.4, p. 290, by
    the functorial definition in 1.9.1, pp. 41–42. *)
Lemma structure_projective_square_natural (R:realType) (U V:lmodType R)
    (f:{linear U->V}) x:
  symmetric_power_map f 2 (inner_projective_square x)=inner_projective_square (f x).
Proof.
rewrite /inner_projective_square linearZ symmetric_tuple_component_natural.
congr (_ *: _); congr (symmetric_tuple_component _).
apply/eqP; rewrite eqEtuple; apply/forallP=>i.
by rewrite tnth_map !tnth_mktuple.
Qed.

(** Source for [structure_projective_orthogonal_isometry]:
    the orthogonal action is isometric on T(U),
    Federer 3.3.4, p. 290. The exact unit
    square-distance formula and original orthogonality
    prove the claim on all actual image points. *)
Theorem structure_projective_orthogonal_isometry (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (f:{linear V->V}) x y:
  is_orthogonal_map B B f ->inner_norm hB x= 1 ->inner_norm hB y= 1 ->
  inner_norm (@symmetric_inner_productP R V B hB 2)
    (symmetric_power_map f 2 (inner_projective_square x)-
      symmetric_power_map f 2 (inner_projective_square y))=
  inner_norm (@symmetric_inner_productP R V B hB 2)
    (inner_projective_square x-inner_projective_square y).
Proof.
move=>hF hx hy; rewrite !structure_projective_square_natural.
have hFx:inner_norm hB (f x)= 1 by rewrite (orthogonal_map_norm hB hB hF) hx.
have hFy:inner_norm hB (f y)= 1 by rewrite (orthogonal_map_norm hB hB hF) hy.
apply/eqP; rewrite eq_le; apply/andP; split;
  rewrite -(ler_sqr (inner_norm_nonnegative _ _) (inner_norm_nonnegative _ _))
    (inner_projective_square_unit_distance hFx hFy)
    (inner_projective_square_unit_distance hx hy) hF; exact:lexx.
Qed.
