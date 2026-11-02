(** Supporting local projection control for Federer (1969), 2.10.5(2), p.
    173, and its forward reference to 3.2.36, p. 272. Preimages of a
    projected affine basis give a linear right inverse whose small ball,
    translated to a simplex barycentre, lies in the source convex set. This
    is a proved supporting existence statement; no right inverse or interior
    ball is assumed without witnesses. The finite convex-combination sources
    and editions are specified in ConvexSimplexBuffer.v. Linear coordinates
    use the local basis theory of 1.1.2, p. 10, and finite-dimensional
    continuity of 1.7.1, p. 28. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  InnerNorm InnerNormedTopology EuclideanCoordinateMetric EuclideanLinearMaps
  LinearBasis FiniteBasisCriterion FiniteHaarLinear ConvexSimplexBuffer InnerConvex TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_projection_section_buffer]:
    supporting actual section and simplex ball
    for the convex geometry behind Federer
    2.10.5(2), p. 173. Source and target
    dimensions may differ; zero target dimension
    is included in the coordinate-box proof. *)
Theorem convex_projection_section_buffer (R : realType) (n m : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : {linear R_n R n -> R_n R m})
    (a : R_n R n) (v : 'I_m -> R_n R n) (e : 'I_m -> R_n R m) :
  is_inner_convex K -> K a -> (forall i, K (a+v i)) ->
  is_basis e -> (forall i, p (v i)=e i) ->
  exists (b : R_n R n) (g : {linear R_n R m -> R_n R n}) (r : R),
    K b /\ cancel g p /\ 0<r /\ forall u : inner_metric_space (@euclidean_inner_productP R m),
      mdist (0%R : inner_metric_space (@euclidean_inner_productP R m)) u<r -> K (b+g u).
Proof.
move=> hK ha hv he hpe.
pose Y := inner_metric_space (@euclidean_inner_productP R m).
pose A := euclidean_frame_map e.
have hA x : A x=basis_synthesis e (coordinate_to_free x).
  rewrite basis_synthesis_finiteE; apply: eq_bigr=> i _; by rewrite coordinate_to_freeE.
have hinj : injective A.
  move=> x y hxy; apply: (can_inj (@coordinate_to_freeK R m)).
  apply: (basis_synthesis_injective he); by rewrite -!hA.
have [B [hAB hBA]] := euclidean_linear_inverse hinj.
pose F : {linear R_n R m -> R_n R n} := GRing.Linear.clone _ _ _ _
  (@orthonormal_synthesis R (R_n R n) m v) _.
have hF x : F x=\sum_i x i*:v i by [].
have hpF x : p (F x)=A x.
  rewrite hF linear_sum; apply: eq_bigr=> i _; by rewrite linearZ hpe.
pose g := linear_comp F B.
have hgp : cancel g p by move=> x; rewrite /g /linear_comp /= hpF hBA.
pose c : R := ((m.+1)%:R)^-1.
pose C : R_n R m := [ffun _ => c].
pose b := a+F C.
have hc : 0<c by rewrite /c invr_gt0 ltr0n.
have hd : 0<c^+2 by rewrite exprn_gt0 //.
have hnb : nbhs (B (0%R : Y) : Y) [set y : Y | mdist (0%R:Y) y<c^+2].
  rewrite linear0; exact: nbhsx_ballx (0%R:Y) (c^+2) hd.
have hn := (@euclidean_linear_continuous R m B) (0%R:Y) _ hnb.
have [r hr hball] := proj1 (metricType_numDomainType.nbhs_mdistP (0%R:Y) _) hn.
have hKb : K b.
  have hz0 (i : 'I_m) : `|(0:R)|<=c^+2 by rewrite normr0; exact: sqr_ge0.
  have hh := @convex_simplex_coordinate_buffer R (R_n R n) K a m v (fun _ => 0)
    hK ha hv hz0.
  move: hh; rewrite -/c; rewrite [X in K (a+X)](eq_bigr (fun i => C i*:v i));
    last by move=> i _; rewrite /C ffunE addr0.
  by rewrite -hF.
exists b,g,r; split=> //; split=> //; split=> // u hu.
have hBu : mdist (0%R:Y) (B u)<c^+2 := hball u hu.
have hcoord i : `|(B u) i|<=c^+2.
  apply: ltW; apply: le_lt_trans (euclidean_coordinate_norm_bound i (B u)) _.
  by move: hBu; rewrite inner_metric_distanceE sub0r inner_normN.
have hh := @convex_simplex_coordinate_buffer R (R_n R n) K a m v (fun i => (B u) i)
  hK ha hv hcoord.
rewrite /b /g /linear_comp /= -addrA -linearD hF.
change (K (a+\sum_i (C+B u) i*:v i)).
have heq : (\sum_i (C+B u) i*:v i)=\sum_i (c+(B u) i)*:v i.
  apply: eq_bigr=> i _; by rewrite /C !ffunE.
by rewrite heq.
Qed.
