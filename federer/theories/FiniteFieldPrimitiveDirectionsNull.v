(** Supporting algebra and measure theory for
    Federer (1969), 3.4.8(8), p. 330:
    almost every original real direction is
    primitive, both in the ambient coefficient
    space and on its unit sphere. Reuse
    the nonzero polynomial and null-cone theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  RingScalarRestriction RingSubmoduleUP CommutativeSubringUP CommutativePolynomialUP
  PolynomialPrimitiveGenerator FiniteFieldPrimitivePolynomial PolynomialFunctions
  EuclideanLebesgueDimensions EuclideanNullConeAllDimensions HausdorffMeasure
  MeasureUP MeasureBasic MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Directions.
Variable R:realType.
Variables K L:fieldType.
Variable eta:{rmorphism R->K}.
Variable phi:{rmorphism K->L}.
Variable n:nat.
Variable x:'I_n->L.
Local Notation z:=(fun v:R_n R n=>\sum_i phi (eta (v i))*x i).
Local Notation bad:=(fun v:R_n R n=>~is_generated_commutative_subring
  (fun y:L=>y = z v \/exists a:K,y = phi a) setT).

(** Source for [primitive_field_bad_direction_cone]: nonzero
    real scaling preserves the generated ring,
    so failing original directions form a
    positive cone, supporting 3.4.8(8), p. 330. *)
Lemma primitive_field_bad_direction_cone (t:R):
  0<t ->forall v:R_n R n,bad v ->bad (t*:v).
Proof.
move=>hPositive v hBad hGood;apply:hBad.
have hT:t!=0 by rewrite gt_eqF.
have hEta:eta t!=0 by rewrite fmorph_eq0.
have hInverse:(eta t)^-1<>0 by apply/eqP;rewrite invr_eq0.
have hScale:z (t*:v) = phi (eta t)*z v.
  rewrite mulr_sumr;apply:eq_bigr=>i _.
  by rewrite ffunE !rmorphM mulrA.
have hScaled:=@primitive_generator_nonzero_scaling K L phi (z (t*:v)) ((eta t)^-1) hInverse hGood.
by rewrite hScale mulrA -rmorphM (mulVf hEta) rmorph1 mul1r in hScaled.
Qed.

(** Source for [finite_field_primitive_real_directions_null]:
    the original almost-everywhere primitive real
    linear combination in 3.4.8(8), p. 330.
    The nonzero determinant polynomial contains
    all failing directions. The existing polynomial
    zero-set and null-cone theorems give both
    nullities without a measurability hypothesis.
    Dimension zero retains its empty unit sphere. *)
Theorem finite_field_primitive_real_directions_null (B:comNzRingType)
  (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
  (hP:is_commutative_polynomial_ring embed variable coefficient):
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType K of ring_restricted_space phi L^o]) ->
  is_generated_commutative_subring
    (fun y:L=>(exists i:'I_n,y = x i) \/exists a:K,y = phi a) setT ->
  @euclidean_lebesgue_measure R n bad = 0%:E /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (n-1)
    [set v|bad v /\inner_norm (@euclidean_inner_productP R n) v = 1] = 0%:E.
Proof.
move=>hFinite hGenerated.
have [Q [w [hQ hGood]]]:=@finite_field_primitive_exceptional_polynomial R K L B eta embed variable coefficient hP
  phi n x hFinite hGenerated.
have hNonzero:exists v,Q v<>0.
  exists w;rewrite hQ;by apply/eqP;exact:oner_neq0.
have hPolynomialNull:=@euclidean_polynomial_zero_set_null R n Q hNonzero.
have hSubset:bad `<=` [set v|Q v = 0].
  move=>v hBad;apply:contrapT=>hNotZero;exact:hBad (hGood v hNotZero).
have hAmbient:=@measure_null_subset R (Choice.clone (inner_metric_space (@euclidean_inner_productP R n)) _)
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n) bad [set v|Q v = 0] hSubset hPolynomialNull.
split;first exact:hAmbient.
exact:(@euclidean_all_dimensions_null_cone_sphere R n bad primitive_field_bad_direction_cone hAmbient).
Qed.
End Directions.
