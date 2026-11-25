(** Federer (1969), 4.1.15, p. 373: the actual opaque
    example sequence converges uniformly to zero, has one
    derivative bound everywhere, and has alternating slopes.
    Use only the independent family laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  NormDifferentialLipschitzBound InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanHomOperator HomSpaceTopology
  NaturalScaledReciprocalTail PointOneOscillatingMapsUP
  PointOneOscillatingMapsSealed NonzeroAlternatingRealSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section PointOneOscillatingMapsBounds.
Variable R:realType.
Local Notation X:=(R_n R 1%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full:=(fun _:X=>True).
Local Notation e:=(@coordinate_basis R 1%N ord0).
Local Notation Id:=(hom_of_linear (@linear_id R X)).
Local Notation u:=(@PointOneOscillatingMaps.value R).
Local Notation hU:=(@PointOneOscillatingMaps.laws R).

(** Source for [point_one_oscillating_uniform_zero]: literal
    uniform convergence on the entire line, as required
    by 4.1.15, p. 373. The proof reuses the
    existing all-integer reciprocal tail bound. *)
Theorem point_one_oscillating_uniform_zero:
  forall eps:R,0<eps->exists N,forall i,(N<=i)%N->forall x,NX (u i x)<eps.
Proof.
move=>eps hEps.
have hTwo:0<(2:R) by rewrite ltr0n.
have [N hN]:=@natural_scaled_reciprocal_tail R 2 eps hTwo hEps.
exists N=>i hi x.
have hTail: (N<=i.+1)%N:=leq_trans hi (leqnSn i).
exact:(le_lt_trans (@point_one_oscillating_size R u hU i x) (hN i.+1 hTail).2).
Qed.

(** Source for [point_one_oscillating_all_differentials_bound]: one
    finite constant bounds the actual differentials of every
    map, everywhere, as in 4.1.15, p. 373.
    Every actual derivative witness is permitted; no arbitrary
    off-domain value of a partial differential is used. *)
Theorem point_one_oscillating_all_differentials_bound:
  exists L:R,0<L /\forall i x (D:Hom X X),
    has_norm_differential NX NX Full (u i) x D ->
    @euclidean_operator_norm R 1%N 1%N D<=L.
Proof.
have [L [hL hLip]]:=@point_one_oscillating_lipschitz R u hU.
exists L;split;first exact:hL.
move=>i x D hD;apply:hom_operator_norm_least;first exact:ltW hL.
exact:(@norm_differential_global_lipschitz_bound R X X NX NX hNX hNX
  (u i) x D L hD (hLip i)).
Qed.

(** Source for [point_one_oscillating_origin_slopes]: the actual
    derivatives at zero are (-1)^i, so the sequence
    used in 4.1.15, p. 373, satisfies the printed
    failure of convergence of psi_i'(0). *)
Theorem point_one_oscillating_origin_slopes i:
  euclidean_one_project (((-1:R)^+i*:Id) e)=(-1:R)^+i.
Proof.
rewrite /euclidean_one_project hom_scaleE /Id hom_of_linearE /=.
rewrite /coordinate_basis ffunE.
by rewrite ffunE eqxx;exact:mulr1.
Qed.

(** Source for [point_one_oscillating_origin_slopes_diverge]: the
    actual derivative values at zero of this same example
    do not converge, as in 4.1.15, p. 373. *)
Theorem point_one_oscillating_origin_slopes_diverge:
  ~exists c:R,forall eps:R,0<eps->exists N,forall i,(N<=i)%N->
    `|euclidean_one_project (((-1:R)^+i*:Id) e)-c|<eps.
Proof.
move=>[c hLimit].
apply:(@nonzero_alternating_real_sequence_diverges R 1).
- by move=>hBad;have:=@oner_neq0 R;rewrite hBad eqxx.
- exists c=>eps hEps;have [N hN]:=hLimit eps hEps.
  exists N=>i hi;rewrite mulr1 -point_one_oscillating_origin_slopes.
  exact:hN i hi.
Qed.
End PointOneOscillatingMapsBounds.
