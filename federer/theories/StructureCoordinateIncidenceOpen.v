(** Federer (1969), 3.3.4, p. 289:
    the single-coordinate cone incidence is
    open in its frame parameter and original
    source point. This is the continuity
    step for B_j and C_j, using 3.3.2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  InnerNormedTopology EuclideanBlockLinearMaps EuclideanRectangularMapContinuity
  EuclideanCoordinateTopology TopologicalProductMaps MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_coordinate_incidence_open]:
    joint openness of the I_j incidence
    used to prove measurability of B_j
    and C_j in Federer 3.3.4, p. 289,
    through the compact-inner argument of
    3.3.2, pp. 287–288. A continuous
    frame-evaluation family gives two strict
    continuous inequalities on the original source. *)
Theorem structure_coordinate_incidence_open (R:realType) m k (P:topologicalType)
    (f:P*inner_metric_space (@euclidean_inner_productP R (m+k))->
      inner_metric_space (@euclidean_inner_productP R (m+k)))
    (a:inner_metric_space (@euclidean_inner_productP R (m+k))) (j:'I_k) (r s:R):
  continuous f ->
  open [set z:P*inner_metric_space (@euclidean_inner_productP R (m+k))|
    inner_norm (@euclidean_inner_productP R (m+k)) (z.2-a)<r /\
    ((s^-1)^+2-1)*
      (inner_norm (@euclidean_inner_productP R m) (@euclidean_first_block R m k (f z)))^+2<
      ((@euclidean_last_block R m k (f z)) j)^+2].
Proof.
move=>hF.
pose E:=inner_metric_space (@euclidean_inner_productP R (m+k)).
pose Y:=inner_metric_space (@euclidean_inner_productP R m).
have hFirst:continuous (fun z:P*E=>(@euclidean_first_block R m k (f z):Y)).
  move=>z; exact:(continuous_comp (hF z)
    (@euclidean_rectangular_map_continuous R (m+k) m (@euclidean_first_block_map R m k) (f z))).
have hCoordinate:continuous (fun z:P*E=>(f z (rshift m j):R^o)).
  move=>z; exact:(continuous_comp (hF z)
    (@euclidean_coordinate_continuous R (m+k) (rshift m j) (f z))).
pose L (z:P*E):R^o:=((s^-1)^+2-1)*
  (inner_norm (@euclidean_inner_productP R m) (@euclidean_first_block R m k (f z)))^+2.
pose H (z:P*E):R^o:=(f z (rshift m j))^+2-L z.
have hL:continuous L.
  move=>z; apply:cvgM; first exact:cvg_cst.
  rewrite expr2; apply:cvgM; exact:cvg_norm (hFirst z).
have hH:continuous H.
  move=>z; apply:cvgB; last exact:hL z.
  rewrite expr2; apply:cvgM; exact:hCoordinate z.
have hRadius:open [set z:P*E|inner_norm (@euclidean_inner_productP R (m+k)) (z.2-a)<r].
  have hEq:[set z:P*E|inner_norm (@euclidean_inner_productP R (m+k)) (z.2-a)<r]=
      (@snd P E) @^-1` [set x:E|mdist a x<r].
    apply/seteqP; split=>z; by rewrite /preimage /= inner_metric_distanceE -opprB inner_normN.
  rewrite hEq; exact:(open_comp (fun z _=>@second_projection_continuous P E z) (metric_open_ball_open a r)).
have hEqual:[set z:P*E|
    inner_norm (@euclidean_inner_productP R (m+k)) (z.2-a)<r /\
    ((s^-1)^+2-1)*
      (inner_norm (@euclidean_inner_productP R m) (@euclidean_first_block R m k (f z)))^+2<
      ((@euclidean_last_block R m k (f z)) j)^+2]=
    [set z:P*E|inner_norm (@euclidean_inner_productP R (m+k)) (z.2-a)<r] `&`
      H @^-1` [set t:R^o|0<t].
  apply/seteqP; split=>z [hR hA]; split=>//;
    move:hA; by rewrite /H /L /preimage /euclidean_last_block /= ffunE subr_gt0.
rewrite hEqual; apply:openI=>//.
exact:((continuousP H).1 hH [set t:R^o|0<t] (@open_gt R 0)).
Qed.
